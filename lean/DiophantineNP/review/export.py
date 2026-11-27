"""Export the project sources needed to review one theorem with pinned mathlib."""
import argparse
from pathlib import Path
import re
from zipfile import ZIP_DEFLATED, ZipFile, ZipInfo

PROJECT = Path(__file__).resolve().parents[1]
TARGETS = {
    "hab": ("HAB63", "Hesse–Allender–Barrington Corollary 6.3", "HAB_REVIEW.md"),
    "rank": ("Rank37", "Rank one for curve 37a1", "RANK_REVIEW.md"),
}
IMPORT = re.compile(r"^import (DiophantineNP\.\w+)$", re.MULTILINE)


def project_sources(entry):
    """Follow this project's one-module-per-import declarations."""
    sources = {}
    pending = [entry]
    while pending:
        source = pending.pop()
        for module in IMPORT.findall(source.decode("utf-8")):
            name = module.replace(".", "/") + ".lean"
            if name not in sources:
                sources[name] = (PROJECT / name).read_bytes()
                pending.append(sources[name])
    return sources


def export(target, output):
    name, title, guide = TARGETS[target]
    entry = (PROJECT / "review" / (name + ".lean")).read_bytes()
    files = project_sources(entry)
    count = len(files)
    for filename in ("lean-toolchain", "lakefile.toml", "lake-manifest.json", guide):
        files[filename] = (PROJECT / filename).read_bytes()
    # Lake builds the public review statement itself as the default library root.
    files["DiophantineNP.lean"] = entry
    files["README.md"] = (
        f"# {title}\n\n"
        f"The default target contains the review statements in `DiophantineNP.lean` "
        f"and imports {count} local proof modules. The Lean toolchain and dependency "
        f"manifest are copied from the full D_NP project. `{guide}` gives the "
        "mathematical background and also refers to the larger development.\n\n"
        "From this directory, with Git and elan installed, run\n\n"
        "```sh\nlake exe cache get\nlake build\nlake env lean DiophantineNP.lean\n```\n\n"
        "The last command checks the stated theorem and prints its axiom dependencies.\n"
    ).encode("utf-8")
    with ZipFile(output, "x") as archive:
        for path, data in sorted(files.items()):
            info = ZipInfo(f"{name}/{path}", date_time=(1980, 1, 1, 0, 0, 0))
            info.external_attr = 0o100644 << 16
            archive.writestr(info, data, compress_type=ZIP_DEFLATED, compresslevel=9)
    print(f"{output}: {count} local proof modules")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("target", choices=TARGETS)
    parser.add_argument("output", type=Path, help="path of a new ZIP file")
    args = parser.parse_args()
    export(args.target, args.output)
