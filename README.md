# anderson-ac-lean4

A Lean 4 formalization of absolutely continuous spectrum for the weak-disorder Anderson model in dimensions at least three. It answers the energy-range question of Simon's Problem 1 for uniform site potentials.

- **Author:** Yao Xu ([@cadamcat](https://github.com/cadamcat)); see [authorship and attribution](AUTHORS.md).
- **Mathematics:** OpenAI, *Absolutely Continuous Spectrum for Weak-Disorder Anderson Models in Dimensions at Least Three* (2026), Theorem 1.1. The manuscript and the library it builds on are in [openai/math](https://github.com/openai/math).
- Developed with AI assistance (Claude Code, Codex, OpenCode and Gemini); all proofs are verified by the Lean 4 kernel.

## Main result

`AndersonAC.Blueprint.anderson_challenge : AndersonChallenge.Statement`, in [Blueprint/Main.lean](AndersonAC/Blueprint/Main.lean).

The statement is in [Challenge.lean](AndersonAC/Challenge.lean), which imports only Mathlib. On `ℓ²(ℤ^d)` the operator is `(h u)(n) = Σ_{|j|=1} u(n + j) + V(n) u(n)` (Simon, Example 2.1). For every `d ≥ 3` there is `δ > 0` such that for all `a < b` with `b - a < δ` there is a nonempty open interval `(E₁, E₂)` with the following property. Let the potentials `V(n)` be any independent family of random variables, each uniform on `[a, b]`, on any probability space. Then almost surely:

1. the operator exists;
2. `(E₁, E₂)` lies in its spectrum;
3. every spectral measure, restricted to `(E₁, E₂)`, is absolutely continuous with respect to Lebesgue measure;
4. some vector has nonzero spectral weight in `(E₁, E₂)`.

A spectral measure of a vector `v` is a finite Borel measure on `ℝ` whose moments are `⟪v, hᵏ v⟫`.

The interval may depend on `a` and `b`. The proof gives a fixed interval translated by the centre `(a + b)/2`; see `AndersonAC.Blueprint.SimonProblem` in [Blueprint/Target.lean](AndersonAC/Blueprint/Target.lean). Theorem 1.1 in the form of the manuscript is `AndersonAC.Blueprint.paperTheorem_blueprint`.

The final theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. No proof in the repository uses `sorry` or an added axiom.

## Build and verify

Requirements: Git and [elan](https://github.com/leanprover/elan), with `lake` on `PATH`. Run from the repository root:

```sh
lake exe cache get
./scripts/verify.sh
```

The first command fetches the compiled Mathlib cache. The script builds the library and prints the axioms of the final theorem and of each package theorem ([Verification/Axioms.lean](Verification/Axioms.lean)). It fails if any of them uses `sorryAx` or an axiom other than the three above.

[Verification/NonVacuity.lean](Verification/NonVacuity.lean) checks that the statement is not vacuous. For every `d` and `a < b`, an i.i.d. family uniform on `[a, b]` exists. For `d ≥ 3`, the theorem then yields a potential, an operator, a vector and a spectral measure of it with nonzero mass on the interval. Run it after the build with `lake env lean Verification/NonVacuity.lean`. The recorded outputs of these checks, with Comparator and kernel replay, are in [docs/verification.md](docs/verification.md).

## Layout

[Blueprint/Main.lean](AndersonAC/Blueprint/Main.lean) assembles the final theorem from the package theorems `AndersonAC.Blueprint.Packages.*`, whose statements are in the [Blueprint](AndersonAC/Blueprint) directory. Directory names `S2` to `S9` follow the sections of the manuscript; directories named `Agent…` hold further parts of the same proofs.

| Package | Module |
| --- | --- |
| `spectral` | [Spectral/SpectralProof](AndersonAC/Spectral/SpectralProof.lean) |
| `boundary` | [BoundaryFinite/Package](AndersonAC/BoundaryFinite/Package.lean) |
| `ward` | [S2/WardPackage](AndersonAC/S2/WardPackage.lean) |
| `binary` | [Prob/Binary](AndersonAC/Prob/Binary.lean) |
| `initialization` | [S3/InitializationPackage](AndersonAC/S3/InitializationPackage.lean) |
| `concentration` | [S45/ConcentrationPackageProof](AndersonAC/S45/ConcentrationPackageProof.lean) |
| `deletion` | [S45/Deletion](AndersonAC/S45/Deletion.lean) |
| `scattering` | [S6/Package](AndersonAC/S6/Package.lean) |
| `reset` | [S78/Reset](AndersonAC/S78/Reset.lean) |
| `certificates` | [S78/CertificatesPackage](AndersonAC/S78/CertificatesPackage.lean) |
| `averaging` | [S9/AveragingPackage](AndersonAC/S9/AveragingPackage.lean) |
| `readout` | [S9/ReadoutPackage](AndersonAC/S9/ReadoutPackage.lean) |
| `purity` | [S9/PurityPackage](AndersonAC/S9/PurityPackage.lean) |
| `lawTransport` | [Transport/Law](AndersonAC/Transport/Law.lean) |
| `signTransport` | [Transport/Sign](AndersonAC/Transport/Sign.lean) |
| `spectralTransport` | [Transport/Spectral](AndersonAC/Transport/Spectral.lean) |
| `challengeBridge` | [Bridge/Bridge](AndersonAC/Bridge/Bridge.lean) |

## Fixed dependencies

- Lean `v4.34.1`, selected by [lean-toolchain](lean-toolchain).
- OpenAI's library `OAI` (directory `lean` of [openai/math](https://github.com/openai/math)), commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
- Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612` and the other packages, through OAI's manifest. All revisions are fixed by [lake-manifest.json](lake-manifest.json).

## License

Apache-2.0; see [LICENSE](LICENSE). Ported code is credited in [THIRD_PARTY.md](THIRD_PARTY.md).
