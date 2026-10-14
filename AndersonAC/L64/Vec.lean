import Mathlib

/-!
# Lemma 6.4 support: elementary finite-dimensional estimates

Vectors are plain functions `B → ℂ`; `nsq y = ∑ b, ‖y b‖²` is the squared Euclidean norm and
`fro D = ∑ a b, ‖D a b‖²` the squared Frobenius norm. We record Cauchy–Schwarz in the forms used in
the proof of Lemma 6.4 of `06-clearing.tex`.
-/

open Matrix Finset ComplexConjugate

set_option linter.unusedSectionVars false

namespace AndersonAC.L64

section Sums

variable {ι : Type*}

/-- Cauchy–Schwarz for complex finite sums. -/
lemma norm_sum_mul_le (S : Finset ι) (a b : ι → ℂ) :
    ‖∑ i ∈ S, a i * b i‖ ≤ √(∑ i ∈ S, ‖a i‖ ^ 2) * √(∑ i ∈ S, ‖b i‖ ^ 2) := by
  calc ‖∑ i ∈ S, a i * b i‖ ≤ ∑ i ∈ S, ‖a i‖ * ‖b i‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- Cauchy–Schwarz for complex finite sums, squared form. -/
lemma norm_sum_mul_sq_le (S : Finset ι) (a b : ι → ℂ) :
    ‖∑ i ∈ S, a i * b i‖ ^ 2 ≤ (∑ i ∈ S, ‖a i‖ ^ 2) * ∑ i ∈ S, ‖b i‖ ^ 2 := by
  have h := norm_sum_mul_le S a b
  have h0 : 0 ≤ ‖∑ i ∈ S, a i * b i‖ := norm_nonneg _
  have ha : 0 ≤ ∑ i ∈ S, ‖a i‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hb : 0 ≤ ∑ i ∈ S, ‖b i‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  calc ‖∑ i ∈ S, a i * b i‖ ^ 2 ≤ (√(∑ i ∈ S, ‖a i‖ ^ 2) * √(∑ i ∈ S, ‖b i‖ ^ 2)) ^ 2 :=
        pow_le_pow_left₀ h0 h 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb]

/-- Real Cauchy–Schwarz with weights: `∑ aᵢ bᵢ ≤ √(∑ aᵢ²) √(∑ bᵢ²)`. -/
lemma sum_mul_le_sqrt (S : Finset ι) (a b : ι → ℝ) :
    ∑ i ∈ S, a i * b i ≤ √(∑ i ∈ S, a i ^ 2) * √(∑ i ∈ S, b i ^ 2) :=
  Real.sum_mul_le_sqrt_mul_sqrt _ _ _

lemma conj_mul_self_eq (z : ℂ) : conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma mul_conj_self_eq (z : ℂ) : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma ofReal_norm_sq_eq (z : ℂ) : ((‖z‖ : ℂ)) ^ 2 = conj z * z := by
  rw [conj_mul_self_eq]; push_cast; ring

end Sums

section Vectors

variable {B : Type*} [Fintype B]

/-- Squared Euclidean norm of a complex vector. -/
noncomputable def nsq (y : B → ℂ) : ℝ := ∑ b, ‖y b‖ ^ 2

lemma nsq_nonneg (y : B → ℂ) : 0 ≤ nsq y := sum_nonneg fun _ _ => sq_nonneg _

lemma nsq_star (y : B → ℂ) : nsq (star y) = nsq y := by
  simp [nsq]

lemma nsq_smul (a : ℂ) (y : B → ℂ) : nsq (a • y) = ‖a‖ ^ 2 * nsq y := by
  simp [nsq, mul_pow, mul_sum]

lemma nsq_neg (y : B → ℂ) : nsq (-y) = nsq y := by
  simp [nsq]

lemma nsq_single [DecidableEq B] (b : B) : nsq (Pi.single b (1 : ℂ)) = 1 := by
  simp [nsq, Pi.single_apply, apply_ite]

lemma nsq_zero : nsq (0 : B → ℂ) = 0 := by
  simp [nsq]

lemma norm_add_sq_le (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 := norm_add_le a b
  have h2 : 0 ≤ ‖a + b‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

lemma nsq_add_le (y z : B → ℂ) : nsq (y + z) ≤ 2 * nsq y + 2 * nsq z := by
  unfold nsq
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_le_sum fun b _ => by simpa using norm_add_sq_le (y b) (z b)

lemma star_dotProduct_self_eq (y : B → ℂ) : star y ⬝ᵥ y = (nsq y : ℂ) := by
  simp only [dotProduct, nsq, Pi.star_apply, Complex.ofReal_sum]
  exact sum_congr rfl fun b _ => conj_mul_self_eq (y b)

lemma dotProduct_star_self_eq (y : B → ℂ) : y ⬝ᵥ star y = (nsq y : ℂ) := by
  rw [dotProduct_comm]; exact star_dotProduct_self_eq y

/-- Cauchy–Schwarz for the bilinear dot product. -/
lemma norm_dotProduct_sq_le (y z : B → ℂ) : ‖y ⬝ᵥ z‖ ^ 2 ≤ nsq y * nsq z :=
  norm_sum_mul_sq_le _ _ _

lemma norm_dotProduct_le (y z : B → ℂ) : ‖y ⬝ᵥ z‖ ≤ √(nsq y) * √(nsq z) :=
  norm_sum_mul_le _ _ _

lemma nsq_le_of_sum (y : B → ℂ) (b : B) : ‖y b‖ ^ 2 ≤ nsq y :=
  single_le_sum (f := fun b => ‖y b‖ ^ 2) (fun _ _ => sq_nonneg _) (mem_univ b)

/-- Squared Frobenius norm of a square matrix. -/
noncomputable def fro (D : Matrix B B ℂ) : ℝ := ∑ a, ∑ b, ‖D a b‖ ^ 2

lemma fro_nonneg (D : Matrix B B ℂ) : 0 ≤ fro D :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _

lemma fro_eq_sum_nsq (D : Matrix B B ℂ) : fro D = ∑ a, nsq (D a) := rfl

lemma nsq_mulVec_le (D : Matrix B B ℂ) (z : B → ℂ) : nsq (D *ᵥ z) ≤ fro D * nsq z := by
  unfold nsq fro
  rw [sum_mul]
  refine sum_le_sum fun a _ => ?_
  exact norm_dotProduct_sq_le (D a) z

lemma norm_dotProduct_mulVec_le (D : Matrix B B ℂ) (y z : B → ℂ) :
    ‖y ⬝ᵥ (D *ᵥ z)‖ ≤ √(nsq y) * √(fro D) * √(nsq z) := by
  calc ‖y ⬝ᵥ (D *ᵥ z)‖ ≤ √(nsq y) * √(nsq (D *ᵥ z)) := norm_dotProduct_le _ _
    _ ≤ √(nsq y) * √(fro D * nsq z) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (nsq_mulVec_le D z)) (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_mul (fro_nonneg D), mul_assoc]

lemma fro_vecMulVec (y z : B → ℂ) : fro (vecMulVec y z) = nsq y * nsq z := by
  simp only [fro, nsq, vecMulVec_apply, norm_mul, mul_pow, sum_mul, mul_sum]
  exact sum_comm

lemma fro_smul (a : ℂ) (D : Matrix B B ℂ) : fro (a • D) = ‖a‖ ^ 2 * fro D := by
  simp [fro, mul_pow, mul_sum]

lemma norm_add3_sq_le (a b c : ℂ) :
    ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have h1 : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
    (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
  have h2 : 0 ≤ ‖a + b + c‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖a‖ - ‖c‖),
    norm_nonneg a, norm_nonneg b, norm_nonneg c]

lemma fro_add3_le (X Y Z : Matrix B B ℂ) :
    fro (X + Y + Z) ≤ 3 * (fro X + fro Y + fro Z) := by
  unfold fro
  simp only [← sum_add_distrib, mul_sum]
  exact sum_le_sum fun a _ => sum_le_sum fun b _ => by
    simpa using norm_add3_sq_le (X a b) (Y a b) (Z a b)

lemma vecMulVec_mulVec' (p q y : B → ℂ) : vecMulVec p q *ᵥ y = (q ⬝ᵥ y) • p := by
  ext a
  simp [mulVec, dotProduct, vecMulVec_apply, mul_sum, mul_comm, mul_left_comm]

lemma dotProduct_vecMulVec_mulVec (p a q y : B → ℂ) :
    p ⬝ᵥ (vecMulVec a q *ᵥ y) = (p ⬝ᵥ a) * (q ⬝ᵥ y) := by
  rw [vecMulVec_mulVec', dotProduct_smul, smul_eq_mul, mul_comm]

lemma trace_vecMulVec_mul (Y : Matrix B B ℂ) (p q : B → ℂ) :
    trace (vecMulVec p q * Y) = q ⬝ᵥ (Y *ᵥ p) := by
  simp only [trace, Matrix.diag, mul_apply, vecMulVec_apply, dotProduct, mulVec]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun b _ => by ring

lemma trace_mul_vecMulVec (Y : Matrix B B ℂ) (p q : B → ℂ) :
    trace (Y * vecMulVec p q) = q ⬝ᵥ (Y *ᵥ p) := by
  rw [trace_mul_comm, trace_vecMulVec_mul]

lemma trace_vecMulVec_star (y : B → ℂ) : trace (vecMulVec (star y) y) = (nsq y : ℂ) := by
  simp only [trace, Matrix.diag, vecMulVec_apply, nsq, Pi.star_apply, Complex.star_def,
    Complex.ofReal_sum]
  exact sum_congr rfl fun b _ => conj_mul_self_eq _

lemma norm_dotProduct_star_comm (p u : B → ℂ) : ‖p ⬝ᵥ star u‖ = ‖u ⬝ᵥ star p‖ := by
  rw [dotProduct_star, norm_star]

/-- For a Hermitian matrix the squared Frobenius norm is `tr D²`. -/
lemma fro_eq_trace_mul_self (D : Matrix B B ℂ) (hD : Dᴴ = D) :
    ((fro D : ℝ) : ℂ) = trace (D * D) := by
  have h : ∀ a b, D b a = conj (D a b) := fun a b => by
    conv_lhs => rw [← hD]
    simp [conjTranspose_apply]
  simp only [fro, trace, Matrix.diag, mul_apply, Complex.ofReal_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [h a b, mul_conj_self_eq]

lemma mulVec_star_eq_star (D : Matrix B B ℂ) (hD : Dᴴ = D) (w : B → ℂ) :
    w ᵥ* D = star (D *ᵥ star w) := by
  rw [star_mulVec, star_star, hD]

/-- `‖u + z x‖² = ‖u‖² + 2 Re(z (x · ū)) + |z|² ‖x‖²`. -/
lemma nsq_add_smul (u x : B → ℂ) (z : ℂ) :
    nsq (u + z • x) = nsq u + 2 * (z * (x ⬝ᵥ star u)).re + ‖z‖ ^ 2 * nsq x := by
  simp only [nsq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Pi.star_apply,
    Complex.star_def, mul_sum, Complex.re_sum, ← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  have h1 : ‖u b + z * x b‖ ^ 2 = ‖u b‖ ^ 2 + ‖z * x b‖ ^ 2 + 2 * (u b * conj (z * x b)).re := by
    simp only [Complex.sq_norm]; exact Complex.normSq_add _ _
  have h2 : (u b * conj (z * x b)).re = (z * (x b * conj (u b))).re := by
    rw [← Complex.conj_re]; simp only [map_mul, Complex.conj_conj]; ring_nf
  rw [h1, h2, norm_mul, mul_pow]; ring

end Vectors

end AndersonAC.L64
