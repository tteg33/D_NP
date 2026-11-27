#!/usr/bin/env bash
# Run after the clean build, or pass a local checkout of the pinned checker.
# Usage: bash verification/replay.sh [project|fresh] [checker-checkout]
set -euo pipefail

mode=${1:-project}
if [[ $# -gt 2 || ( "$mode" != project && "$mode" != fresh ) ]]; then
    echo "Usage: $0 [project|fresh] [checker-checkout]" >&2
    exit 2
fi

project_dir=$(cd -- "$(dirname -- "$0")/.." && pwd)
checker_rev=da26eb05e9959402afcb9bd6dfe5dc4f700f70d6
toolchain=leanprover/lean4:v4.24.0
tmp_dir=$(mktemp -d)
trap 'rm -rf -- "$tmp_dir"' EXIT
if [[ -n ${2:-} ]]; then
    checker_dir=$(cd -- "$2" && pwd)
else
    checker_dir="$tmp_dir/checker"
    git clone --quiet --depth 1 --branch v4.24.0 https://github.com/leanprover/lean4checker.git "$checker_dir"
fi
if [[ $(git -C "$checker_dir" rev-parse HEAD) != "$checker_rev" ]] ||
   [[ -n $(git -C "$checker_dir" status --porcelain --untracked-files=no) ]]; then
    echo "Use a clean checkout of lean4checker at $checker_rev." >&2
    exit 1
fi

cd "$project_dir"
test "$(tr -d '\r\n' < lean-toolchain)" = "$toolchain"
printf 'Project toolchain: %s\nKernel checker: %s\nReplay mode: %s\n' "$toolchain" "$checker_rev" "$mode"
lean --version
# Ensure the serialized declarations match the current sources.
lake build
(cd "$checker_dir" && lake build lean4checker)

case "$mode" in
    project)
        # The driver reads the project's own .olean files and trusts its external imports.
        lake env bash -eu -c '
            export LEAN_PATH="$1/.lake/build/lib/lean:${LEAN_PATH:-}"
            export LEAN_NUM_THREADS=1
            lean --run verification/ProjectReplay.lean
        ' _ "$checker_dir"
        ;;
    fresh)
        # The v4.24 checker uses name prefixes. One uniquely named wrapper selects one module.
        printf '%s\n' 'import DiophantineNP' > "$tmp_dir/DnpReleaseReplay.lean"
        lake env bash -eu -c '
            export LEAN_PATH="$1:${LEAN_PATH:-}"
            cd "$1"
            lean -o DnpReleaseReplay.olean DnpReleaseReplay.lean
            "$2/.lake/build/bin/lean4checker" --fresh --verbose DnpReleaseReplay
        ' _ "$tmp_dir" "$checker_dir"
        echo "Fresh replay completed for the project and all transitive imports."
        ;;
esac
