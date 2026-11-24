#!/usr/bin/env bash
# Local preflight only. Run inside an isolated credential-free disposable environment.
set -euo pipefail
mode=full
kind=check
while [[ "${1:-}" == --* ]]; do
  case "$1" in
    --diagnostic) mode=diagnostic; shift ;;
    --kind)
      [[ $# -ge 2 && "$2" =~ ^(check|refute|reduce)$ ]] || exit 2
      kind=$2; shift 2 ;;
    *) echo "unknown option: $1" >&2; exit 2 ;;
  esac
done
script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
if [ "$#" -ne 6 ]; then
  echo 'usage: bash check-candidate.sh [--diagnostic] [--kind check|refute|reduce] BASE SNAPSHOT GAP FILE CANDIDATE RECEIPTS' >&2; exit 2
fi
base=$(realpath "$1"); snapshot=$(realpath "$2"); gap=$3; file=$4
candidate=$(realpath "$5"); mkdir -p "$6"; receipt=$(realpath "$6")
if [[ "$kind" == reduce ]]; then
  [[ "$file" =~ ^lean/PEqualNP/Outside/R_[a-z0-9_]+_[1-9][0-9]{0,2}\.lean$ ]] || exit 2
else
  [[ "$file" =~ ^lean/PEqualNP/Outside/L_[a-z0-9_]+\.lean$ ]] || exit 2
fi
[[ "$gap" =~ ^L-[a-z0-9]+(-[a-z0-9]+)*$ ]] || exit 2
for p in "$snapshot" "$candidate" "$receipt"; do
  [[ "$p" != "$base" && "$p" != "$base/"* ]] || { echo 'inputs and receipts must be outside BASE'; exit 2; }
done
cd "$base"
[[ "$(git rev-parse --show-toplevel)" == "$base" ]] || exit 2
[[ -z "$(git status --porcelain --untracked-files=all)" ]] || { echo 'BASE is not clean'; exit 2; }
[[ ! -e "$file" && ! -L "$file" ]] || { echo 'gap path already exists'; exit 2; }
[[ -f "$candidate" ]] || exit 2
[[ ! -e "$receipt/result.txt" ]] || { echo 'use a new receipt directory'; exit 2; }
git rev-parse HEAD > "$receipt/base.sha"
sha256sum "$snapshot" "$candidate" lean/lean-toolchain lean/lake-manifest.json tools/check-lean.mjs .github/scripts/outside-guard.mjs > "$receipt/input.sha256"
guard=.github/scripts/outside-guard.mjs
node "$guard" gap "$snapshot" "$gap" "$file" "$receipt" "$kind"
[[ "$(cat "$receipt/gap.kind")" == "$kind" ]] || exit 2
node "$guard" imports "$candidate" "$receipt/imports.json" "$file" "$kind"
node "$guard" closure "$base" "$receipt/imports.json" "$file" "$receipt" "$kind"
# noclobber prevents overwriting an existing source even if concurrently created.
mkdir -p "$(dirname "$file")"
(set -o noclobber; cat "$candidate" > "$file")
trap 'rm -f -- "$file"' EXIT
cmp "$candidate" "$file"
if [[ "$mode" == diagnostic ]]; then
  set +e
  bash "$script_dir/diagnose.sh" "$file" "$receipt/diagnostic"
  code=$?
  set -e
  cmp "$candidate" "$file"
  sha256sum --check "$receipt/input.sha256"
  exit "$code"
fi
set +e
node tools/check-lean.mjs "$file" "$receipt/statement.txt" "$kind" 2>&1 | tee "$receipt/checker.log"
codes=("${PIPESTATUS[@]}")
set -e
[[ "${codes[1]}" == 0 ]] || exit 3
cmp "$candidate" "$file"
sha256sum --check "$receipt/input.sha256"
if [[ "${codes[0]}" == 0 ]] && grep -q "^ACCEPTED ($kind)" "$receipt/checker.log" && ! grep -q '^REJECTED' "$receipt/checker.log"; then
  echo LOCAL_CHECK_ACCEPTED | tee "$receipt/result.txt"
else
  echo LOCAL_CHECK_NOT_ACCEPTED | tee "$receipt/result.txt"
  exit 1
fi
