"""Mutation tests for the preflight of verify.py (no Lean needed).

    python tests/test_preflight.py

Each case copies the project to a temporary folder, breaks one thing, and checks
that `verify.static_checks` reports it. Two controls must stay clean."""
import importlib.util, shutil, sys, tempfile
from pathlib import Path
src = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("verify", src / "verify.py")
v = importlib.util.module_from_spec(spec); spec.loader.exec_module(v)

def mutated(edit):
    tmp = Path(tempfile.mkdtemp(prefix="pf_")) / "p"
    shutil.copytree(src, tmp, ignore=shutil.ignore_patterns("blueprint", "manuscript", "tests", ".lake", "__pycache__"))
    edit(tmp)
    res = v.static_checks(tmp)
    shutil.rmtree(tmp.parent)
    return res

def sub(path, old, new, count=1):
    def f(tmp):
        p = tmp / path; s = p.read_text(encoding="utf-8"); assert old in s, (path, old)
        p.write_text(s.replace(old, new, count), encoding="utf-8")
    return f

def append(path, text):
    def f(tmp):
        p = tmp / path; p.write_text(p.read_text(encoding="utf-8") + text, encoding="utf-8")
    return f

cases = [
 ("clean copy", lambda t: None, 0, 0),
 ("root forgets a module", sub("DiophantineNP.lean", "import DiophantineNP.TailRadix\n", ""), 1, 0),
 ("root imports a ghost", append("DiophantineNP.lean", "import DiophantineNP.DoesNotExist\n"), 1, 0),
 ("unimported new module", lambda t: (t / "DiophantineNP" / "Stray.lean").write_text("theorem stray : True := trivial\n"), 1, 0),
 ("sorry in a proof", append("DiophantineNP/Wallis.lean", "\ntheorem bad : 1 = 2 := by sorry\n"), 1, 0),
 ("axiom declared", append("DiophantineNP/Wallis.lean", "\naxiom bad : 1 = 2\n"), 1, 0),
 ("native_decide", append("DiophantineNP/Wallis.lean", "\ntheorem t : 2 + 2 = 4 := by native_decide\n"), 1, 0),
 ("sorry only in comments and strings", append("DiophantineNP/Wallis.lean",
     "\n-- sorry\n/- sorry /- nested sorry -/ still a comment: axiom -/\ndef msg := \"sorry -- axiom\"\n"), 0, 0),
 ("module imports a ghost", sub("DiophantineNP/Corollary.lean", "import DiophantineNP.Main", "import DiophantineNP.Mian"), 1, 0),
 ("lakefile pin edited", sub("lakefile.toml", 'rev = "v4.24.0"', 'rev = "v4.25.0"'), 1, 1),
 ("toolchain garbage", lambda t: (t / "lean-toolchain").write_text("stable\n"), 1, 1),
 ("manifest rev shortened", sub("lake-manifest.json", "f897ebcf72cd16f89ab4577d0c826cd14afaafc7", "f897ebcf"), 1, 0),
 ("audit name typo", sub("Audit.lean", "#check DiophantineNP.classEquality_of_packing", "#check DiophantineNP.classEquality_of_paking"), 0, 1),
 ("audit removed", lambda t: (t / "Audit.lean").unlink(), 1, 0),
]
ok = True
for name, edit, want_err, want_warn in cases:
    errors, warnings, _ = mutated(edit)
    good = (len(errors) >= want_err and (want_err > 0 or not errors)) and (len(warnings) >= want_warn and (want_warn > 0 or not warnings))
    ok &= good
    print(("PASS" if good else "FAIL"), f"{name}: {len(errors)} error(s), {len(warnings)} warning(s)", (errors + warnings)[:1])
sys.exit(0 if ok else 1)
