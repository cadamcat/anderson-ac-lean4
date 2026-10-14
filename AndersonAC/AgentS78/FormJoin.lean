import AndersonAC.S3H.Dual
import AndersonAC.S78.Definitions

/-!
Real/complex charge join between the §3 complex matrix forms (`S3.form`,
`S3.inverseOnConstants`, `S3.connectedLaplacian`) and the real variational
forms of §§7–8 (`S78.inverseEnergy`, `S78.constantKernel`).

For a connected Laplacian `D` with real entries whose complex form restricts on
real potentials to a real functional `Q`, the variational inverse energy of `Q`
on a real neutral charge equals the complex pseudoinverse form, and `Q` has
exactly the constant kernel. Also: a scalar-damped Ward identity, and the
equality of the S78 Euclidean operator norm with the Blueprint `opNorm`.
-/

open scoped BigOperators
open Matrix

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

variable {A : Type} [Fintype A]

/-- Complexification of a real potential or charge. -/
def cx (f : A → ℝ) : A → ℂ := fun i => (f i : ℂ)

theorem pairing_cx (y f : A → ℝ) :
    AndersonAC.S3.pairing (cx y) (cx f) = ∑ i, y i * f i := by
  unfold AndersonAC.S3.pairing cx
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re]

theorem pairing_cx_left (y : A → ℝ) (w : A → ℂ) :
    AndersonAC.S3.pairing (cx y) w = ∑ i, y i * (w i).re := by
  unfold AndersonAC.S3.pairing cx
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re]

/-- The complex form of a matrix with real entries splits into real and imaginary parts. -/
theorem form_real_split (D : Matrix A A ℂ) (hD : ∀ i j, (D i j).im = 0) (v : A → ℂ) :
    AndersonAC.S3.form D v =
      AndersonAC.S3.form D (cx fun i => (v i).re) + AndersonAC.S3.form D (cx fun i => (v i).im) := by
  unfold AndersonAC.S3.form AndersonAC.S3.pairing cx
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Complex.re_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := hD i j
  simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, h]
  ring

variable [DecidableEq A] [Nonempty A]

theorem neutral_cx (y : A → ℝ) (hy : ∑ i, y i = 0) : AndersonAC.S3.neutral (cx y) := by
  unfold AndersonAC.S3.neutral cx
  rw [← Complex.ofReal_sum, hy, Complex.ofReal_zero]

/-- Real variational inverse energy equals the complex pseudoinverse form on real neutral charges. -/
theorem inverseEnergy_eq_form (Q : (A → ℝ) → ℝ) (D : Matrix A A ℂ)
    (hDim : ∀ i j, (D i j).im = 0) (hD : AndersonAC.S3.connectedLaplacian D)
    (hQ : ∀ f, Q f = AndersonAC.S3.form D (cx f)) (y : A → ℝ) (hy : ∑ i, y i = 0) :
    AndersonAC.S78.inverseEnergy Finset.univ Q y =
      AndersonAC.S3.form (AndersonAC.S3.inverseOnConstants D) (cx y) := by
  have hyn := neutral_cx y hy
  set V := AndersonAC.S3.form (AndersonAC.S3.inverseOnConstants D) (cx y) with hV
  have hub : ∀ f : A → ℝ, 2 * (∑ i ∈ Finset.univ, y i * f i) - Q f ≤ V := by
    intro f
    have h := AndersonAC.S3H.young_D_X D hD (cx f) (cx y) hyn
    rw [pairing_cx] at h
    rw [hQ]
    linarith
  set w := AndersonAC.S3.inverseOnConstants D *ᵥ cx y with hw
  have hatt := AndersonAC.S3H.dual_D_attains D hD (cx y) hyn
  rw [← hw] at hatt
  set f0 : A → ℝ := fun i => (w i).re with hf0
  have hpair : AndersonAC.S3.pairing (cx y) w = ∑ i, y i * f0 i := pairing_cx_left y w
  have hsplit := form_real_split D hDim w
  have hnonneg := (hD.2 (cx fun i => (w i).im)).1
  have hval : V ≤ 2 * (∑ i ∈ Finset.univ, y i * f0 i) - Q f0 := by
    rw [hQ]
    rw [hpair] at hatt
    have : AndersonAC.S3.form D (cx f0) = AndersonAC.S3.form D (cx fun i => (w i).re) := rfl
    linarith
  have hbdd : BddAbove (Set.range fun f : A → ℝ => 2 * (∑ i ∈ Finset.univ, y i * f i) - Q f) :=
    ⟨V, by rintro _ ⟨f, rfl⟩; exact hub f⟩
  unfold AndersonAC.S78.inverseEnergy
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨f, rfl⟩
    exact hub f
  · exact le_trans hval (le_csSup hbdd ⟨f0, rfl⟩)

/-- A real functional represented by a connected Laplacian has exactly the constant kernel. -/
theorem constantKernel_of_form (Q : (A → ℝ) → ℝ) (D : Matrix A A ℂ)
    (hD : AndersonAC.S3.connectedLaplacian D)
    (hQ : ∀ f, Q f = AndersonAC.S3.form D (cx f)) :
    AndersonAC.S78.constantKernel Finset.univ Q := by
  intro f
  rw [hQ]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := (hD.2 (cx f)).2.mp h
    refine ⟨c.re, fun i _ => ?_⟩
    have hi := congrFun hc i
    simp only [cx] at hi
    rw [← hi, Complex.ofReal_re]
  · rintro ⟨c, hc⟩
    apply (hD.2 _).2.mpr
    exact ⟨(c : ℂ), funext fun i => by simp [cx, hc i (Finset.mem_univ _)]⟩

end AndersonAC.AgentS78

namespace AndersonAC.AgentS78

/-- The S78 Euclidean operator norm is the Blueprint operator norm. -/
theorem matrixNorm_eq_opNorm {ι : Type} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ) :
    AndersonAC.S78.matrixNorm B = AndersonAC.Blueprint.opNorm B := by
  unfold AndersonAC.S78.matrixNorm AndersonAC.Blueprint.opNorm
  congr 1

/-- Ward identity for a Hermitian matrix with scalar complex shift: rows and columns. -/
theorem ward_scalar {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (hM : M.conjTranspose = M) (z : ℂ) (G : Matrix ι ι ℂ)
    (h1 : (M - z • (1 : Matrix ι ι ℂ)) * G = 1) (h2 : G * (M - z • (1 : Matrix ι ι ℂ)) = 1) (i : ι) :
    (G i i).im = z.im * ∑ j, ‖G i j‖ ^ 2 ∧ (G i i).im = z.im * ∑ j, ‖G j i‖ ^ 2 := by
  set B := M - z • (1 : Matrix ι ι ℂ) with hB
  have hBH : B.conjTranspose = M - (starRingEnd ℂ z) • (1 : Matrix ι ι ℂ) := by
    rw [hB, Matrix.conjTranspose_sub, hM, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    rfl
  have h1H : G.conjTranspose * B.conjTranspose = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have h2H : B.conjTranspose * G.conjTranspose = 1 := by
    rw [← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one]
  have hdiff : B.conjTranspose - B = (z - starRingEnd ℂ z) • (1 : Matrix ι ι ℂ) := by
    rw [hBH, hB, sub_smul]; abel
  -- rows: G - Gᴴ = G (Bᴴ - B) Gᴴ
  have hrow : G - G.conjTranspose = (z - starRingEnd ℂ z) • (G * G.conjTranspose) := by
    have e : G * (B.conjTranspose - B) * G.conjTranspose = G - G.conjTranspose := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, h2H, Matrix.mul_one, h2, Matrix.one_mul]
    rw [← e, hdiff, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  -- columns: G - Gᴴ = Gᴴ (Bᴴ - B) G
  have hcol : G - G.conjTranspose = (z - starRingEnd ℂ z) • (G.conjTranspose * G) := by
    have e : G.conjTranspose * (B.conjTranspose - B) * G = G - G.conjTranspose := by
      rw [Matrix.mul_sub, Matrix.sub_mul, h1H, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
    rw [← e, hdiff, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have key : ∀ (S : ℝ), G i i - starRingEnd ℂ (G i i) = (z - starRingEnd ℂ z) * (S : ℂ) →
      (G i i).im = z.im * S := by
    intro S h
    have him := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.mul_im, Complex.conj_re, Complex.sub_re,
      Complex.ofReal_re, Complex.ofReal_im] at him
    linarith
  constructor
  · apply key
    have e := congrFun (congrFun hrow i) i
    simp only [Matrix.sub_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply] at e
    rw [show star (G i i) = starRingEnd ℂ (G i i) from rfl] at e
    rw [e]
    congr 1
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Complex.mul_conj' _
  · apply key
    have e := congrFun (congrFun hcol i) i
    simp only [Matrix.sub_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply] at e
    rw [show star (G i i) = starRingEnd ℂ (G i i) from rfl] at e
    rw [e]
    congr 1
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    exact Complex.mul_conj' _

end AndersonAC.AgentS78
