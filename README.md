# Native bitwise inclusion and the Adleman–Manders conjecture

This is a proposed proof of the Adleman–Manders equality for binary numerical languages. The central theorem constructs one integer polynomial for all input widths. A true bitwise-inclusion instance has a root of polynomial total bit length, and every root implies a true instance. The companion Lean development derives `Classes.D = Classes.NP` from this theorem.

**Read the revised paper** in [PDF](lean/DiophantineNP/manuscript/Native_Bitwise_Inclusion_Revised.pdf) or [TeX](lean/DiophantineNP/manuscript/Native_Bitwise_Inclusion_Revised.tex).
| To review | Start here |
| --- | --- |
| Exact claims and quantifiers | [Native polynomial statement](lean/DiophantineNP/DiophantineNP/Statement.lean), [class definitions](lean/DiophantineNP/DiophantineNP/Classes.lean), [closed theorems](lean/DiophantineNP/DiophantineNP/HABVerified.lean) |
| NP verifier and certificate conventions | [Clocked TM2 equivalence](lean/DiophantineNP/DiophantineNP/ClockedVerifier.lean), [binary certificate encoding](lean/DiophantineNP/DiophantineNP/BinaryCertificates.lean) and [clocked scan of a raw certificate](lean/DiophantineNP/review/CertificateTransducer.lean) |
| Reproduce the proof checks | [Project instructions](lean/DiophantineNP/README.md) and [verification record](lean/DiophantineNP/VERIFICATION.txt) |
| HAB Corollary 6.3 | [Source comparison](lean/DiophantineNP/HAB_REVIEW.md) and [standalone Lean project](lean/DiophantineNP/review/standalone/HAB63.zip) |
| Rank of curve 37a1 | [Descent guide](lean/DiophantineNP/RANK_REVIEW.md) and [standalone Lean project](lean/DiophantineNP/review/standalone/Rank37.zip) |
| The printed implication from (49) to (50) | [Source transcription, counterexamples and local correction](lean/DiophantineNP/JONES_REVIEW.md) |

From the repository root, with Git, elan and Python 3 installed, run

```sh
cd lean/DiophantineNP
python3 verify.py --strict --extras -j 2
python3 tests/test_preflight.py
bash verification/replay.sh project
lake env lean -DautoImplicit=false review/CertificateTransducer.lean
```

The build uses Lean 4.24.0 and the pinned mathlib revision. The GitHub Actions workflow runs these checks on a fresh checkout and retains their logs. A manual `fresh` option requests kernel replay of the external dependency closure as well. [Workflow](.github/workflows/verify.yml)
