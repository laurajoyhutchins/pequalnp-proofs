#!/usr/bin/env bash
# Diagnostic only; use an isolated, credential-free checkout with pinned dependencies.
set -euo pipefail
if [[ $# != 2 ]]; then
  echo 'usage: bash diagnose.sh lean/PEqualNP/Research/Name.lean RECEIPTS' >&2
  exit 2
fi
file=$1
root=$(git rev-parse --show-toplevel)
cd "$root"
root=$(pwd -P)
[[ "$file" =~ ^lean/PEqualNP/(Research|Outside)/([A-Za-z][A-Za-z0-9_]*/)*[A-Za-z][A-Za-z0-9_]*\.lean$ ]] || exit 2
[[ -f "$file" && ! -L "$file" && "$(realpath "$file")" == "$root/$file" ]] || exit 2
config=(lean/lean-toolchain lean/lake-manifest.json lean/lakefile.toml)
[[ ! -e lean/lakefile.lean ]] || exit 2
git ls-files --error-unmatch -- "${config[@]}" >/dev/null
git diff --quiet HEAD -- "${config[@]}" || { echo 'build configuration differs from HEAD' >&2; exit 2; }
mkdir -p "$2"
receipt=$(realpath "$2")
[[ "$receipt" != "$root" && "$receipt" != "$root/"* ]] || { echo 'receipts must be outside checkout' >&2; exit 2; }
[[ ! -e "$receipt/result.txt" && ! -e "$receipt/build.log" ]] || { echo 'use a fresh receipt directory' >&2; exit 2; }
git rev-parse HEAD > "$receipt/base.sha"
sha256sum "$file" "${config[@]}" > "$receipt/input.sha256"
module=${file#lean/}
module=${module%.lean}
module=${module//\//.}
printf '%s\n' "$module" > "$receipt/module.txt"
# Match the upstream checker's environment boundary. Reuse only same-tree Lake outputs.
for var in $(compgen -e); do
  case "$var" in LAKE|LAKE_*|LEAN_*|ELAN_TOOLCHAIN|PEQUALNP_IN_QUEUE) unset "$var";; esac
done
export LAKE_ARTIFACT_CACHE=false
start=$SECONDS
set +e
(
  cd lean
  lean --version && lake --version && lake build "+$module"
) 2>&1 | tee "$receipt/build.log"
codes=("${PIPESTATUS[@]}")
set -e
printf '%s\n' "$((SECONDS-start))" > "$receipt/elapsed-seconds.txt"
printf '%s\n' "${codes[0]}" > "$receipt/build-exit.txt"
if [[ "${codes[1]}" != 0 ]] || ! sha256sum --check "$receipt/input.sha256" || ! git diff --quiet HEAD -- "${config[@]}"; then
  echo DIAGNOSTIC_INVALIDATED | tee "$receipt/result.txt"
  exit 3
fi
if [[ "${codes[0]}" == 0 ]]; then
  echo DIAGNOSTIC_BUILD_SUCCEEDED | tee "$receipt/result.txt"
else
  echo DIAGNOSTIC_BUILD_FAILED | tee "$receipt/result.txt"
  exit 1
fi
