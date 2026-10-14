import AndersonAC.S9.Core

/-! Finite §9 definitions copied verbatim from the definitions. -/

noncomputable section

open MeasureTheory Filter OAI.Anderson
open scoped Topology ComplexConjugate

namespace AndersonAC.S9

structure CertificateBounds where
  B : ℝ
  pMin : ℝ
  pMax : ℝ
  qMin : ℝ
  B_nonneg : 0 ≤ B
  pMin_pos : 0 < pMin
  pMin_le_pMax : pMin ≤ pMax
  qMin_pos : 0 < qMin

def comparisonConstant (b : CertificateBounds) : ℝ :=
  1 + (b.B + 1) / b.pMin

def columnConstant (b : CertificateBounds) : ℝ :=
  b.qMin / (b.pMax * comparisonConstant b ^ 2)

def cutMultiplier (ε : ℝ) : ℝ := 1 + ε⁻¹ ^ 2

def truncatedReadout (b : CertificateBounds) (ε q : ℝ) : ℝ :=
  min (2 * cutMultiplier ε * q) (columnConstant b)

section Finite

variable {n : Type*} [Fintype n] [DecidableEq n]

def matrixResolvent (H : Matrix n n ℂ) (E η : ℝ) : Matrix n n ℂ :=
  (H - ((E : ℂ) + η * Complex.I) • 1)⁻¹

def scalarQ (H : Matrix n n ℂ) (E η : ℝ) (i : n) : ℝ :=
  (matrixResolvent H E η i i).im

def matrixCertificate (H : Matrix n n ℂ) (E η : ℝ) (b : CertificateBounds) : Prop :=
  ∃ (A : Finset n) (r : n → ℂ) (G : Matrix n n ℂ),
    Fintype.card n ≤ 2 * A.card ∧
    (∀ i ∈ A, ‖r i‖ ≤ b.B ∧ b.pMin ≤ (r i).im ∧ (r i).im ≤ b.pMax) ∧
    (H - (E : ℂ) • 1 - (η : ℂ) • Matrix.diagonal (fun i => if i ∈ A then r i else 0)) * G = 1 ∧
    G * (H - (E : ℂ) • 1 - (η : ℂ) • Matrix.diagonal (fun i => if i ∈ A then r i else 0)) = 1 ∧
    (∀ i ∈ A, b.qMin ≤ (G i i).im)

def allPrincipalInvertible (H : Matrix n n ℂ) (E : ℝ) : Prop :=
  ∀ A : Finset n, IsUnit ((H - (E : ℂ) • 1).submatrix
    (fun i : A => (i : n)) (fun i : A => (i : n)))

def compress (A : Finset n) (T : Matrix n n ℂ) : Matrix A A ℂ :=
  T.submatrix (fun i : A => (i : n)) (fun i : A => (i : n))

def activeSchur (H : Matrix n n ℂ) (E : ℝ) (A : Finset n) : Matrix A A ℂ :=
  let H0 := H - (E : ℂ) • 1
  let Ac := Finset.univ \ A
  compress A H0 -
    H0.submatrix (fun i : A => (i : n)) (fun j : Ac => (j : n)) *
    (compress Ac H0)⁻¹ *
    H0.submatrix (fun j : Ac => (j : n)) (fun i : A => (i : n))

def dampingFunction (η : ℝ) (B : Matrix n n ℂ) : Matrix n n ℂ :=
  B * (1 - (η * Complex.I) • B)⁻¹

def windowProjection (H : Matrix n n ℂ) (hH : H.IsHermitian) (E δ : ℝ) :
    Matrix n n ℂ := by
  classical
  exact (hH.eigenvectorUnitary : Matrix n n ℂ) *
    Matrix.diagonal (fun i => if |hH.eigenvalues i - E| ≤ δ then 1 else 0) *
    star (hH.eigenvectorUnitary : Matrix n n ℂ)

def windowRank (H : Matrix n n ℂ) (hH : H.IsHermitian) (E δ : ℝ) : ℕ :=
  Matrix.rank (windowProjection H hH E δ)

def cutInverse (H : Matrix n n ℂ) (hH : H.IsHermitian) (E η ε : ℝ) :
    Matrix n n ℂ :=
  (H - (E : ℂ) • 1)⁻¹ * (1 - windowProjection H hH E (ε * η))

def columnNormSq (G : Matrix n n ℂ) (i : n) : ℝ := ∑ j, ‖G j i‖ ^ 2

def hilbertSchmidtSq (G : Matrix n n ℂ) : ℝ := ∑ i, columnNormSq G i

def matrixOpNorm (G : Matrix n n ℂ) : ℝ :=
  ‖G.toEuclideanLin.toContinuousLinearMap‖

def matrixImaginaryPart (G : Matrix n n ℂ) : Matrix n n ℂ :=
  ((2 * Complex.I)⁻¹ : ℂ) • (G - star G)

end Finite

def trueCertificateEvent (d m : ℕ) (coupling E η : ℝ) (b : CertificateBounds) :
    Set (TorusConfiguration d m) :=
  {ω | matrixCertificate (periodicHamiltonian coupling ω) E η b}


end AndersonAC.S9
