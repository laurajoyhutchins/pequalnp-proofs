"""Offline, deterministic research retrieval; no desk mutations."""
import argparse
import json
import re
from pathlib import Path

def frontier(snapshot):
    rows = snapshot["gaps"]
    by_id = {}
    for row in rows:
        name = row["id"]
        if not isinstance(name, str) or not name or name in by_id:
            raise ValueError("invalid or duplicate gap id")
        by_id[name] = row
    reverse = {name: set() for name in by_id}
    unknown = set()
    missing = set()
    for name, row in by_id.items():
        if "depends_on" not in row:
            missing.add(name)
            continue
        deps = row["depends_on"]
        if not isinstance(deps, list) or not all(isinstance(d, str) for d in deps):
            raise ValueError("invalid dependencies")
        for d in deps:
            if d in reverse:
                reverse[d].add(name)
            else:
                unknown.add((name, d))
    result = []
    for name, row in by_id.items():
        if row.get("status") != "open":
            continue
        visited = {name}
        pending = list(reverse[name])
        while pending:
            n = pending.pop()
            if n in visited:
                continue
            visited.add(n)
            pending.extend(reverse[n] - visited)
        unresolved = sorted(n for n in visited - {name}
                            if by_id[n].get("status") in ("open", "blocked"))
        result.append({"id": name, "known_downstream": unresolved,
                       "score": len(unresolved)})
    return {"ranking": sorted(result, key=lambda x: (-x["score"], x["id"])),
            "unknown_edges": sorted(unknown), "missing_dependency_lists": sorted(missing),
            "scope": "explicit edges only; not official priority or ownership"}

DECL = re.compile(r"^\s*(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma|def|abbrev|structure|class|inductive)\s+([^\s:(]+)")
def index(root):
    for path in sorted(Path(root).rglob("*.lean")):
        if path.is_symlink():
            continue
        for line, text in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            match = DECL.match(text)
            if match:
                yield {"file": str(path), "line": line, "kind": match[1], "name": match[2]}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["frontier", "index"])
    parser.add_argument("path", type=Path)
    args = parser.parse_args()
    if args.mode == "frontier":
        print(json.dumps(frontier(json.loads(args.path.read_text())), indent=2))
    else:
        for row in index(args.path):
            print(json.dumps(row, ensure_ascii=False))

if __name__ == "__main__":
    main()
