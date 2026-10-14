# Verification record

Checks of release v1.0.0, commit `38116e1a08b2b3427f24d6043fffd5560fba6905`, on 2026-10-14. Each run started from a fresh clone of this repository with the published `lake-manifest.json`, fetched the Mathlib cache and used 10 threads on the author's Mac. v1.0.1 changes only comments and adds [Verification/NonVacuity.lean](../Verification/NonVacuity.lean); no Lean statement or proof differs from v1.0.0.

| Check | Command | Result |
| --- | --- | --- |
| Build | `lake build` | exit 0, 9780 jobs |
| Axioms | `lake env lean Verification/Axioms.lean` | `'AndersonAC.Blueprint.anderson_challenge' depends on axioms: [propext, Classical.choice, Quot.sound]`, and the same three for every package theorem |
| Kernel replay | `lake env leanchecker --fresh AndersonAC.Blueprint.Main` | exit 0 |
| Comparator | challenge: [AndersonAC/Challenge.lean](../AndersonAC/Challenge.lean) with `AndersonAC.Blueprint.anderson_challenge : AndersonChallenge.Statement` added as `sorry`; `definition_names` empty; nanoda enabled | exit 0: "nanoda kernel accepts the solution", "Lean default kernel accepts the solution", "Your solution is okay!" |
| Non-vacuity | `lake env lean Verification/NonVacuity.lean` | `hypotheses_satisfiable` and `conclusion_witnessed` depend only on `propext`, `Classical.choice` and `Quot.sound` |

Comparator compares the final theorem's type and the three definitions of `Challenge.lean` (Mathlib definitions only) with the library's. With `definition_names` empty, the bodies of those definitions are compared too; a name listed there would be checked by name and type only.

Tool versions: Comparator `ca04cfc72b550331658ec314bf47685281bfd4bf`, lean4export `076e8e57707e813375e8f9da8bf989799ace9680`, nanoda_lib `3a2407216ee84a75f9e1aead6803d0578be06ae7`. Comparator ran with its development `fake-landrun.sh`, not the Landrun sandbox.

## Controls

- nanoda accepted a correct proof and rejected a proof by `sorry` (exit 1) and an export with a tampered numeral (exit 101).
- With the challenge's dimension condition changed from `3 ≤ d` to `2 ≤ d`, Comparator rejected the solution: "Const does not match between challenge and target 'AndersonChallenge.Statement'".
