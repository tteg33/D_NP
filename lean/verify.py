"""Check the project: static preflight, pinned Lean build, axiom audit.

    python verify.py                 preflight, mathlib cache, `lake build`, `Audit.lean`
    python verify.py --static-only   preflight only (needs no Lean installation)
    python verify.py --strict        also re-elaborate every module with autoImplicit off
    python verify.py --extras        also check the two standalone entry points and model,
                                     Premises.lean, blueprint/Evaluator.lean and the
                                     Python reference evaluator

The preflight catches the mistakes that a successful build cannot reveal: a module
that the root file forgot to import is never compiled and never audited, and a
toolchain or dependency pin that was edited in one place only.
"""

from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys


PROJECT = Path(__file__).resolve().parent
LIBRARY = "DiophantineNP"

# Constructs that would bypass the kernel or leave a hole. `Audit.lean` also rejects any
# axiom beyond propext, Quot.sound and Classical.choice; this scan fails earlier and
# names the file.
FORBIDDEN = ("sorry", "admit", "axiom", "native_decide", "implemented_by", "extern", "unsafe",
             "ofReduceBool", "reduceBool", "trustCompiler")
DECLARATION = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class)\s+([^\s:({\[]+)", re.M)


def strip_lean(text):
    """Blank out comments (nested block comments included) and string literals."""
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        if depth:
            if text.startswith("/-", i):
                depth, i = depth + 1, i + 2
            elif text.startswith("-/", i):
                depth, i = depth - 1, i + 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth, i = 1, i + 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = n if end < 0 else end
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append('""')
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def read(path):
    return path.read_text(encoding="utf-8")


def static_checks(project=PROJECT):
    """Return (errors, warnings, summary lines). Uses only the files on disk."""
    errors, warnings, summary = [], [], []
    library = project / LIBRARY
    root = project / f"{LIBRARY}.lean"
    modules = sorted(library.glob("*.lean"))
    if not root.is_file() or not modules:
        return [f"Expected {root.name} and the folder {LIBRARY}/ next to verify.py."], warnings, summary
    names = {m.stem for m in modules}
    project_import = re.compile(rf"^import {LIBRARY}\.([\w.]+)\s*$", re.M)

    # 1. The root file must import every module: `lake build` and the audit only see those.
    root_imports = set(project_import.findall(strip_lean(read(root))))
    for missing in sorted(names - root_imports):
        errors.append(f"{LIBRARY}/{missing}.lean is not imported by {root.name}: "
                      "it would be neither compiled nor audited.")
    for ghost in sorted(root_imports - names):
        errors.append(f"{root.name} imports {LIBRARY}.{ghost}, which does not exist.")

    # 2. Imports between modules resolve, and nothing bypasses the kernel.
    audited = modules + [root] + [p for p in (project / "Audit.lean", project / "Premises.lean") if p.is_file()]
    declared = set()
    for path in audited:
        code = strip_lean(read(path))
        for target in project_import.findall(code):
            if target not in names:
                errors.append(f"{path.name} imports {LIBRARY}.{target}, which does not exist.")
        for word in FORBIDDEN:
            hits = [code.count("\n", 0, m.start()) + 1
                    for m in re.finditer(rf"(?<![\w.'])(?:Lean\.)?{word}(?![\w'])", code)]
            if hits:
                errors.append(f"{path.name}: `{word}` at line(s) {', '.join(map(str, hits[:8]))}.")
        declared.update(name.split(".")[-1] for name in DECLARATION.findall(code))

    # 3. The pins agree with each other.
    toolchain = project / "lean-toolchain"
    lakefile = project / "lakefile.toml"
    manifest = project / "lake-manifest.json"
    pin = read(toolchain).strip() if toolchain.is_file() else ""
    if not re.fullmatch(r"leanprover/lean4:v\d+\.\d+\.\d+(-rc\d+)?", pin):
        errors.append(f"lean-toolchain should pin one Lean release, found {pin!r}.")
    wanted = re.search(r'name\s*=\s*"mathlib".*?rev\s*=\s*"([^"]+)"', read(lakefile), re.S) if lakefile.is_file() else None
    if wanted is None:
        errors.append("lakefile.toml does not pin a mathlib revision.")
    if manifest.is_file():
        packages = {p["name"]: p for p in json.loads(read(manifest)).get("packages", [])}
        mathlib = packages.get("mathlib")
        if mathlib is None:
            errors.append("lake-manifest.json has no mathlib entry.")
        else:
            if wanted and mathlib.get("inputRev") != wanted.group(1):
                errors.append(f"lakefile.toml asks for mathlib {wanted.group(1)!r} but the manifest "
                              f"was resolved from {mathlib.get('inputRev')!r}. Run `lake update mathlib`.")
            if not re.fullmatch(r"[0-9a-f]{40}", mathlib.get("rev", "")):
                errors.append("lake-manifest.json does not pin mathlib to a full commit hash.")
            if wanted and pin and wanted.group(1).startswith("v") and not pin.endswith(":" + wanted.group(1)):
                warnings.append(f"Lean {pin} and mathlib tag {wanted.group(1)} carry different version numbers.")
            summary.append(f"Lean {pin.split(':')[-1]}, mathlib {mathlib.get('rev', '?')[:12]}")
    else:
        warnings.append("lake-manifest.json is missing: dependencies would be resolved afresh.")

    # 4. Names that Audit.lean prints should exist (a typo would only surface after the build).
    audit = project / "Audit.lean"
    if audit.is_file():
        for name in re.findall(rf"^#(?:check|print axioms)\s+({LIBRARY}[\w.']*)", strip_lean(read(audit)), re.M):
            if name.split(".")[-1] not in declared:
                warnings.append(f"Audit.lean mentions {name}, and no declaration with that final name was found.")
    else:
        errors.append("Audit.lean is missing. The build requires its axiom check.")

    digest = hashlib.sha256()
    lines = 0
    for path in modules:
        data = path.read_bytes()
        digest.update(path.name.encode() + b"\0" + hashlib.sha256(data).digest())
        lines += data.count(b"\n")
    summary.append(f"{len(modules)} modules, {lines} lines, all imported by {root.name}")
    summary.append(f"source digest {digest.hexdigest()[:16]} (changes whenever a module changes)")
    return errors, warnings, summary


def run(command, env, **kwargs):
    print("$ " + " ".join(str(c) for c in command), flush=True)
    return subprocess.run(command, cwd=PROJECT, env=env, **kwargs)


def elaborate(lake, env, path, options=()):
    result = subprocess.run([lake, "env", "lean", *options, str(path)], cwd=PROJECT, env=env,
                            capture_output=True, text=True)
    return path, result.returncode, (result.stdout + result.stderr).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--static-only", action="store_true", help="run the preflight and stop")
    parser.add_argument("--strict", action="store_true",
                        help="re-elaborate every module with -DautoImplicit=false after the build")
    parser.add_argument("--extras", action="store_true",
                        help="also check the files that are outside the default build")
    parser.add_argument("-j", "--jobs", type=int, default=max(1, (os.cpu_count() or 2) // 2),
                        help="parallel Lean processes for --strict")
    args = parser.parse_args()

    errors, warnings, summary = static_checks()
    for line in summary:
        print("preflight: " + line)
    for line in warnings:
        print("preflight warning: " + line)
    if errors:
        sys.exit("Preflight failed:\n  " + "\n  ".join(errors))
    print("preflight: ok", flush=True)

    failed_extras = []
    if args.extras:
        reference = PROJECT / "blueprint" / "reference_evaluator.py"
        if not reference.is_file():
            sys.exit("Missing check file: blueprint/reference_evaluator.py")
        code = run([sys.executable, str(reference), "--quick"], dict(os.environ)).returncode
        if code:
            failed_extras.append("blueprint/reference_evaluator.py")
    if args.static_only:
        if failed_extras:
            sys.exit("Failed: " + ", ".join(failed_extras))
        return

    lake = shutil.which("lake")
    if lake is None:
        sys.exit("Install Lean 4 using elan, then reopen your terminal and run this script again.\n"
                 "(The preflight above passed; `python verify.py --static-only` needs no Lean.)")

    # The manifest already pins every dependency. Restrict the binary cache fetch
    # to modules imported by this project, including their transitive imports.
    imports = set()
    for source in sorted((PROJECT / LIBRARY).glob("*.lean")):
        imports.update(re.findall(r"^import (Mathlib(?:\.\w+)*)$", read(source), re.M))

    env = {**os.environ, "MATHLIB_NO_CACHE_ON_UPDATE": "1"}
    run([lake, "exe", "cache", "get", *sorted(imports)], env, check=True)
    run([lake, "build"], env, check=True)

    run([lake, "env", "lean", "Audit.lean"], env, check=True)
    print("Build and axiom audit succeeded. The theorem types printed above list the premises "
          "that remain hypotheses.", flush=True)

    if args.strict:
        modules = sorted((PROJECT / LIBRARY).glob("*.lean"))
        print(f"strict: re-elaborating {len(modules)} modules with autoImplicit off", flush=True)
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            results = list(pool.map(lambda m: elaborate(lake, env, m, ["-DautoImplicit=false"]), modules))
        bad = [(path, output) for path, code, output in results if code]
        for path, output in bad:
            print(f"--- {path.name}\n{output}")
        if bad:
            sys.exit(f"strict: {len(bad)} module(s) did not elaborate with autoImplicit off (output above).")
        print("strict: ok. All project modules rechecked with autoImplicit disabled.")

    if args.extras:
        for extra in (PROJECT / "Premises.lean", PROJECT / "blueprint" / "Evaluator.lean"):
            if not extra.is_file():
                sys.exit(f"Missing check file: {extra.relative_to(PROJECT)}")
            path, code, output = elaborate(lake, env, extra)
            print(f"--- {extra.relative_to(PROJECT)} (outside the default build)\n{output}")
            if code:
                failed_extras.append(str(extra.relative_to(PROJECT)))
        if failed_extras:
            sys.exit("The verified library built and passed the audit. These additions did not check: "
                     + ", ".join(failed_extras))
        print("extras: ok. The standalone files expose the same audited evaluator and external premises.")


if __name__ == "__main__":
    main()
