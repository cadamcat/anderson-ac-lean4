[English](README.md) | [简体中文](README_zh.md)

# anderson-ac-lean4

至少三维弱无序 Anderson 模型绝对连续谱的 Lean 4 形式化。对于格点势服从均匀分布的情形，它回答了 Simon 问题 1 中关于能量范围的问题。

- **作者：** Yao Xu ([@cadamcat](https://github.com/cadamcat))；见[作者与署名说明](AUTHORS.md)。
- **数学结果：** OpenAI，*Absolutely Continuous Spectrum for Weak-Disorder Anderson Models in Dimensions at Least Three*（2026），定理 1.1。论文稿及其所依托的库见 [openai/math](https://github.com/openai/math)。
- 本项目在 AI 协助下开发；所有证明均由 Lean 4 内核验证。

## 主要结果

`AndersonAC.Blueprint.anderson_challenge : AndersonChallenge.Statement`，位于 [Blueprint/Main.lean](AndersonAC/Blueprint/Main.lean)。

陈述位于 [Challenge.lean](AndersonAC/Challenge.lean)，该文件只导入 Mathlib。在 ℓ²(ℤ^d) 上，算子为 (h u)(n) = Σ_{|j|=1} u(n + j) + V(n) u(n)（Simon，例 2.1）。对每个 d ≥ 3，存在 δ > 0，使得对所有满足 b - a < δ 的 a < b，都存在一个非空开区间 (E₁, E₂)，具有以下性质。令势 V(n) 为任意概率空间上的独立随机变量族，且每个随机变量都在 [a, b] 上服从均匀分布。那么几乎必然：

1. 算子存在；
2. (E₁, E₂) 包含在其谱中；
3. 每个谱测度限制在 (E₁, E₂) 上时，均关于勒贝格测度绝对连续；
4. 存在一个向量，其在 (E₁, E₂) 上的谱权非零。

向量 v 的谱测度是 ℝ 上的有限 Borel 测度，其矩为 ⟪v, hᵏ v⟫。

该区间可以依赖于 a 和 b。证明给出一个以中心 (a + b)/2 平移的固定区间；见 [Blueprint/Target.lean](AndersonAC/Blueprint/Target.lean) 中的 `AndersonAC.Blueprint.SimonProblem`。论文表述下的定理 1.1 是 `AndersonAC.Blueprint.paperTheorem_blueprint`。

最终定理只使用公理 `propext`、`Classical.choice` 和 `Quot.sound`。仓库中的证明均未使用 `sorry` 或新增公理。

## 构建与验证

环境要求：Git 和 [elan](https://github.com/leanprover/elan)，并确保 `lake` 在 `PATH` 中。在仓库根目录运行：

```sh
lake exe cache get
./scripts/verify.sh
```

第一条命令获取编译后的 Mathlib 缓存。脚本会构建库，并打印最终定理和各工作包定理所依赖的公理（[Verification/Axioms.lean](Verification/Axioms.lean)）。如果其中任何定理使用 `sorryAx` 或上述三个公理以外的公理，脚本就会失败。

[Verification/NonVacuity.lean](Verification/NonVacuity.lean) 检查该陈述并非空泛。对每个 d 和 a < b，都存在一个在 [a, b] 上独立同分布的均匀随机变量族。若 d ≥ 3，则定理推出一个势、一个算子、一个向量及其谱测度，且该谱测度在区间上具有非零质量。构建后运行 `lake env lean Verification/NonVacuity.lean`。这些检查的记录结果（含 Comparator 和内核重放）见 [docs/verification.md](docs/verification.md)。

## 目录结构

[Blueprint/Main.lean](AndersonAC/Blueprint/Main.lean) 将最终定理由工作包定理 `AndersonAC.Blueprint.Packages.*` 组装而成；各定理的陈述位于 [Blueprint](AndersonAC/Blueprint) 目录。目录名 `S2` 至 `S9` 对应论文的章节；名为 `Agent…` 的目录存放同一证明的其他部分。

| 工作包 | 模块 |
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

## 固定依赖

- Lean `v4.34.1`，由 [lean-toolchain](lean-toolchain) 选定。
- OpenAI 的库 `OAI`（[openai/math](https://github.com/openai/math) 的 `lean` 目录），提交 `adc7f1241b42e322a6451854ab7e4b4c146bf78a`。
- Mathlib 提交 `d13f23b723b8a846827a245b89c10fc7d3f11612`，以及通过 OAI 清单指定的其他软件包。所有版本均固定在 [lake-manifest.json](lake-manifest.json) 中。

## 许可证

Apache-2.0；见 [LICENSE](LICENSE)。移植的代码已在 [THIRD_PARTY.md](THIRD_PARTY.md) 中注明来源。
