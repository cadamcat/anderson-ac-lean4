import AndersonAC.S6.Definitions
import AndersonAC.S6.Projection

/-! Positive-ridge scalar derivative for fixed matrices.
Independent of the ridge-limit helper. -/

noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator ComplexOrder
open Filter

namespace AndersonAC.SolS6RidgeLim

theorem tau_smul_eq (w : ℂ) (τ : ℝ) : ((τ : ℂ) • w) = τ • w := by
  simp [smul_eq_mul, RCLike.real_smul_eq_coe_mul]

theorem star_mul_self_re (z : ℂ) : RCLike.re (star z * z) = ‖z‖ ^ 2 := by
  simp [RCLike.star_def, RCLike.mul_re, RCLike.conj_re, RCLike.conj_im,
    RCLike.norm_sq_eq_def]

theorem tau_dotProduct_re (B : Type*) [Fintype B] [DecidableEq B] (τ : ℝ) (z : B → ℂ) :
    RCLike.re (star z ⬝ᵥ ((((τ : ℂ)) • (1 : Matrix (B) (B) ℂ)) *ᵥ z))
      = τ * ∑ i, ‖z i‖ ^ 2 := by
  have h1 : ((((τ : ℂ)) • (1 : Matrix (B) (B) ℂ)) *ᵥ z) = (τ : ℂ) • z := by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [h1]
  have h2 : star z ⬝ᵥ ((τ : ℂ) • z) = (τ : ℂ) • (star z ⬝ᵥ z) :=
    dotProduct_smul _ _ _
  rw [h2, tau_smul_eq, RCLike.smul_re]
  congr 1
  have h4 : RCLike.re (star z ⬝ᵥ z) = ∑ i, ‖z i‖ ^ 2 := by
    have hdot : star z ⬝ᵥ z = ∑ i, star (z i) * z i := rfl
    rw [hdot, map_sum]
    congr 1
    funext i
    exact star_mul_self_re _
  exact h4

theorem ridgeGram_injective (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (τ : ℝ) (hτ : 0 < τ) :
    Function.Injective (AndersonAC.S6.ridgeGram C τ).mulVec := by
  intro x y hxy
  have hsub : (AndersonAC.S6.ridgeGram C τ) *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  suffices hz : x - y = 0 by
    exact sub_eq_zero.mp hz
  set z := x - y with hzdef
  have hGz : (AndersonAC.S6.ridgeGram C τ) *ᵥ z = 0 := hsub
  have hdot : star z ⬝ᵥ ((AndersonAC.S6.ridgeGram C τ) *ᵥ z) = 0 := by
    rw [hGz]
    simp [dotProduct]
  have hGdef : AndersonAC.S6.ridgeGram C τ =
      AndersonAC.S6.gram C + ((τ : ℂ) • (1 : Matrix (B) (B) ℂ)) := rfl
  have hmul : (AndersonAC.S6.ridgeGram C τ) *ᵥ z =
      (AndersonAC.S6.gram C) *ᵥ z +
        ((((τ : ℂ)) • (1 : Matrix (B) (B) ℂ)) *ᵥ z) := by
    rw [hGdef, Matrix.add_mulVec]
  have hdot_split : star z ⬝ᵥ ((AndersonAC.S6.ridgeGram C τ) *ᵥ z) =
      (star z ⬝ᵥ ((AndersonAC.S6.gram C) *ᵥ z)) +
        (star z ⬝ᵥ (((((τ : ℂ)) • (1 : Matrix (B) (B) ℂ)) *ᵥ z))) := by
    rw [hmul, dotProduct_add]
  have hGram_nonneg : 0 ≤ RCLike.re (star z ⬝ᵥ ((AndersonAC.S6.gram C) *ᵥ z)) := by
    have hpsd : Matrix.PosSemidef ((Cᴴ * C : Matrix (B) (B) ℂ)) :=
      Matrix.posSemidef_conjTranspose_mul_self C
    have hgram : AndersonAC.S6.gram C = Cᴴ * C := rfl
    rw [hgram]
    exact hpsd.re_dotProduct_nonneg z
  have hTau : RCLike.re
      (star z ⬝ᵥ (((((τ : ℂ)) • (1 : Matrix (B) (B) ℂ)) *ᵥ z)))
      = τ * ∑ i, ‖z i‖ ^ 2 := tau_dotProduct_re B τ z
  have hre : RCLike.re (star z ⬝ᵥ ((AndersonAC.S6.ridgeGram C τ) *ᵥ z)) =
      RCLike.re (star z ⬝ᵥ ((AndersonAC.S6.gram C) *ᵥ z)) +
        (τ * ∑ i, ‖z i‖ ^ 2) := by
    rw [hdot_split, map_add, hTau]
  rw [hdot] at hre
  simp only [map_zero] at hre
  have hsum_nonneg : 0 ≤ ∑ i, ‖z i‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro i _
    positivity
  have htau_mul_nonneg : 0 ≤ τ * ∑ i, ‖z i‖ ^ 2 :=
    mul_nonneg (le_of_lt hτ) hsum_nonneg
  have htau_eq : τ * ∑ i, ‖z i‖ ^ 2 = 0 := by
    linarith
  have hsum_eq : ∑ i, ‖z i‖ ^ 2 = 0 := by
    have hτne : τ ≠ 0 := ne_of_gt hτ
    exact (mul_eq_zero.mp htau_eq).resolve_left hτne
  have heach : ∀ i, ‖z i‖ ^ 2 = 0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
      (f := fun i => ‖z i‖ ^ 2) (fun i _ => by positivity)).mp hsum_eq
    intro i
    exact h i (Finset.mem_univ i)
  have hz_zero : ∀ i, z i = 0 := by
    intro i
    have hi := heach i
    have hnorm : ‖z i‖ = 0 := by
      nlinarith [norm_nonneg (z i)]
    exact norm_eq_zero.mp hnorm
  funext i
  exact hz_zero i

theorem ridgeGram_isUnit (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (τ : ℝ) (hτ : 0 < τ) : IsUnit (AndersonAC.S6.ridgeGram C τ) :=
  (Matrix.mulVec_injective_iff_isUnit.mp (ridgeGram_injective B R C τ hτ))

theorem ridgeGram_isUnit_det (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (τ : ℝ) (hτ : 0 < τ) : IsUnit (AndersonAC.S6.ridgeGram C τ).det :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (ridgeGram_isUnit B R C τ hτ))

theorem ridgeGram_det_ne (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (τ : ℝ) (hτ : 0 < τ) : (AndersonAC.S6.ridgeGram C τ).det ≠ 0 :=
  IsUnit.ne_zero (ridgeGram_isUnit_det B R C τ hτ)

theorem gram_entry_deriv_diag (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (p : B) (τ : ℝ) :
    HasDerivAt (fun s : ℝ => AndersonAC.S6.ridgeGram C s p p) 1 τ := by
  have hfun : (fun s : ℝ => AndersonAC.S6.ridgeGram C s p p) =
      (fun s : ℝ => AndersonAC.S6.gram C p p + (s : ℂ)) := by
    funext s
    simp [AndersonAC.S6.ridgeGram, AndersonAC.S6.gram, Matrix.add_apply,
      Matrix.smul_apply]
  rw [hfun]
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 τ := by
    have h := (hasDerivAt_id τ).ofReal_comp
    simpa using h
  have h2 := (hasDerivAt_const τ (AndersonAC.S6.gram C p p)).add h1
  have hzero : (0 : ℂ) + 1 = 1 := zero_add _
  rw [hzero] at h2
  exact h2

theorem gram_entry_deriv_offdiag (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (p q : B) (hpq : p ≠ q) (τ : ℝ) :
    HasDerivAt (fun s : ℝ => AndersonAC.S6.ridgeGram C s p q) 0 τ := by
  have hfun : (fun s : ℝ => AndersonAC.S6.ridgeGram C s p q) =
      (fun _ : ℝ => AndersonAC.S6.gram C p q) := by
    funext s
    simp [AndersonAC.S6.ridgeGram, AndersonAC.S6.gram, Matrix.add_apply,
      Matrix.smul_apply, hpq]
  rw [hfun]
  exact hasDerivAt_const τ _

theorem gram_entry_differentiable (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (τ : ℝ) (p q : B) :
    DifferentiableAt ℝ (fun s => AndersonAC.S6.ridgeGram C s p q) τ := by
  by_cases h : p = q
  · subst h
    exact (gram_entry_deriv_diag B R C _ τ).differentiableAt
  · have hder := gram_entry_deriv_offdiag B R C p q h τ
    exact hder.differentiableAt

theorem det_differentiable_of_entry {B : Type*} [Fintype B] [DecidableEq B]
    {M : ℝ → Matrix B B ℂ} {τ : ℝ}
    (hM : ∀ p q, DifferentiableAt ℝ (fun s => M s p q) τ) :
    DifferentiableAt ℝ (fun s => (M s).det) τ := by
  have hdet_eq : (fun s : ℝ => (M s).det) =
      (fun s : ℝ => ∑ σ : Equiv.Perm B, (((Equiv.Perm.sign σ : ℤ)) : ℂ) *
        ∏ i, M s (σ i) i) := by
    funext s
    exact Matrix.det_apply' (M s)
  rw [hdet_eq]
  apply DifferentiableAt.fun_sum
  intro σ _
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.fun_finsetProd
  intro i _
  exact hM _ _

theorem ridgeGram_det_differentiable (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (τ : ℝ) : DifferentiableAt ℝ (fun s => (AndersonAC.S6.ridgeGram C s).det) τ :=
  det_differentiable_of_entry (fun p q => gram_entry_differentiable B R C τ p q)

theorem updateRow_entry_differentiable (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (τ : ℝ) (q p : B) (a c : B) :
    DifferentiableAt ℝ
      (fun s => ((AndersonAC.S6.ridgeGram C s).updateRow q (Pi.single p 1)) a c) τ := by
  have happly : ∀ s : ℝ, ((AndersonAC.S6.ridgeGram C s).updateRow q (Pi.single p 1)) a c =
      (if a = q then ((Pi.single p (1 : ℂ) : B → ℂ) c)
        else AndersonAC.S6.ridgeGram C s a c) := by
    intro s
    simp only [Matrix.updateRow_apply]
  by_cases h : a = q
  · have hfun : (fun s : ℝ =>
        ((AndersonAC.S6.ridgeGram C s).updateRow q (Pi.single p 1)) a c) =
        (fun _ : ℝ => ((Pi.single p (1 : ℂ) : B → ℂ) c)) := by
      funext s
      rw [happly s, if_pos h]
    rw [hfun]
    exact differentiableAt_const _
  · have hfun : (fun s : ℝ =>
        ((AndersonAC.S6.ridgeGram C s).updateRow q (Pi.single p 1)) a c) =
        (fun s : ℝ => AndersonAC.S6.ridgeGram C s a c) := by
      funext s
      rw [happly s, if_neg h]
    rw [hfun]
    exact gram_entry_differentiable B R C τ a c

theorem ridgeGram_adj_differentiable (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (τ : ℝ) (p q : B) :
    DifferentiableAt ℝ (fun s => (AndersonAC.S6.ridgeGram C s).adjugate p q) τ := by
  have hadj_eq : (fun s : ℝ => (AndersonAC.S6.ridgeGram C s).adjugate p q) =
      (fun s : ℝ => (((AndersonAC.S6.ridgeGram C s).updateRow q (Pi.single p 1)).det)) := by
    funext s
    exact Matrix.adjugate_apply _ p q
  rw [hadj_eq]
  apply det_differentiable_of_entry
  intro a c
  exact updateRow_entry_differentiable B R C τ q p a c

theorem ridgeGram_inv_entry_differentiable (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (τ : ℝ) (hτ : 0 < τ) (p q : B) :
    DifferentiableAt ℝ (fun s => ((AndersonAC.S6.ridgeGram C s)⁻¹) p q) τ := by
  have hdet_ne : (AndersonAC.S6.ridgeGram C τ).det ≠ 0 :=
    ridgeGram_det_ne B R C τ hτ
  have hdet_diff : DifferentiableAt ℝ (fun s => (AndersonAC.S6.ridgeGram C s).det) τ :=
    ridgeGram_det_differentiable B R C τ
  have hadj_diff : DifferentiableAt ℝ
      (fun s => (AndersonAC.S6.ridgeGram C s).adjugate p q) τ :=
    ridgeGram_adj_differentiable B R C τ p q
  have hinv_eq : (fun s : ℝ => ((AndersonAC.S6.ridgeGram C s)⁻¹) p q) =
      (fun s : ℝ => ((AndersonAC.S6.ridgeGram C s).det)⁻¹ *
        (AndersonAC.S6.ridgeGram C s).adjugate p q) := by
    funext s
    rw [Matrix.inv_def]
    simp [Pi.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  rw [hinv_eq]
  exact (hdet_diff.inv hdet_ne).mul hadj_diff

theorem gram_entry_hasDerivAt (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (τ : ℝ) (p q : B) :
    HasDerivAt (fun s : ℝ => AndersonAC.S6.ridgeGram C s p q)
      (if p = q then 1 else 0) τ := by
  by_cases h : p = q
  · subst h
    simp only [if_true]
    exact gram_entry_deriv_diag B R C _ τ
  · simp only [h, ↓reduceIte]
    -- need if_false? Actually simp with h gives if_false? Use ite?
    have hder := gram_entry_deriv_offdiag B R C p q h τ
    simpa using hder

-- H' as deriv, and its HasDerivAt
theorem inv_entry_hasDerivAt (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (τ : ℝ) (hτ : 0 < τ) (p q : B) :
    HasDerivAt (fun s : ℝ => ((AndersonAC.S6.ridgeGram C s)⁻¹) p q)
      (deriv (fun s : ℝ => ((AndersonAC.S6.ridgeGram C s)⁻¹) p q) τ) τ :=
  (ridgeGram_inv_entry_differentiable B R C τ hτ p q).hasDerivAt

theorem inv_entry_deriv_eq (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (τ : ℝ) (hτ : 0 < τ) (p q : B) :
    deriv (fun s : ℝ => ((AndersonAC.S6.ridgeGram C s)⁻¹) p q) τ =
      -(((AndersonAC.S6.ridgeGram C τ)⁻¹ * (AndersonAC.S6.ridgeGram C τ)⁻¹) p q) := by
  -- Notation
  set G : ℝ → Matrix (B) (B) ℂ := fun s => AndersonAC.S6.ridgeGram C s with hG
  set H : ℝ → Matrix (B) (B) ℂ := fun s => (AndersonAC.S6.ridgeGram C s)⁻¹ with hH
  set Gτ := AndersonAC.S6.ridgeGram C τ with hGτ
  set Hτ := (AndersonAC.S6.ridgeGram C τ)⁻¹ with hHτ
  -- G' and H'
  have hGderiv : ∀ i k, HasDerivAt (fun s => G s i k) (if i = k then 1 else 0) τ := by
    intro i k
    exact gram_entry_hasDerivAt B R C τ i k
  have hHderiv : ∀ k j, HasDerivAt (fun s => H s k j)
      (deriv (fun s => H s k j) τ) τ := by
    intro k j
    exact inv_entry_hasDerivAt B R C τ hτ k j
  -- For fixed i j, F(s) = ∑ k, G s i k * H s k j, derivative
  have hFderiv : ∀ i j, HasDerivAt (fun s => ∑ k, G s i k * H s k j)
      (∑ k, ((if i = k then (1 : ℂ) else 0) * Hτ k j + Gτ i k * deriv (fun s => H s k j) τ)) τ := by
    intro i j
    apply HasDerivAt.fun_sum
    intro k _
    exact (hGderiv i k).mul (hHderiv k j)
  -- F(s) = 1 i j eventually (where det ≠ 0)
  have hdet_cont : ContinuousAt (fun s => (AndersonAC.S6.ridgeGram C s).det) τ :=
    (ridgeGram_det_differentiable B R C τ).continuousAt
  have hev : ∀ᶠ s in nhds τ, (AndersonAC.S6.ridgeGram C s).det ≠ 0 := by
    have hne : (AndersonAC.S6.ridgeGram C τ).det ≠ 0 :=
      ridgeGram_det_ne B R C τ hτ
    exact hdet_cont.eventually_ne hne
  have hF_eq : ∀ i j, (fun s => ∑ k, G s i k * H s k j) =ᶠ[nhds τ]
      (fun _ => (1 : Matrix (B) (B) ℂ) i j) := by
    intro i j
    filter_upwards [hev] with s hs
    have hunit : IsUnit (AndersonAC.S6.ridgeGram C s).det := isUnit_iff_ne_zero.mpr hs
    have hmul : AndersonAC.S6.ridgeGram C s * (AndersonAC.S6.ridgeGram C s)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ hunit
    have hentry : (AndersonAC.S6.ridgeGram C s * (AndersonAC.S6.ridgeGram C s)⁻¹) i j =
        (1 : Matrix (B) (B) ℂ) i j := by rw [hmul]
    simp only [Matrix.mul_apply] at hentry
    exact hentry
  -- Hence derivative sum = 0
  have hsum_zero : ∀ i j, (∑ k, ((if i = k then (1 : ℂ) else 0) * Hτ k j +
      Gτ i k * deriv (fun s => H s k j) τ)) = 0 := by
    intro i j
    have hconst : HasDerivAt (fun _ : ℝ => (1 : Matrix (B) (B) ℂ) i j) 0 τ :=
      hasDerivAt_const τ _
    have hF0 : HasDerivAt (fun s => ∑ k, G s i k * H s k j) 0 τ :=
      hconst.congr_of_eventuallyEq (hF_eq i j)
    have hF1 := hFderiv i j
    have hunique := hF1.unique hF0
    -- hunique : ∑ ... = 0
    exact hunique
  -- Simplify ∑ G' * H = H i j
  have hGprime_mul : ∀ i j, (∑ k, ((if i = k then (1 : ℂ) else 0) * Hτ k j)) = Hτ i j := by
    intro i j
    have : ∀ k : B, ((if i = k then (1 : ℂ) else 0) * Hτ k j) =
        (if k = i then Hτ k j else 0) := by
      intro k
      by_cases hk : k = i
      · subst hk
        simp
      · have hik : ¬ (i = k) := fun h => hk h.symm
        simp [hik, hk]
    simp only [this]
    rw [Finset.sum_ite_eq']
    simp
  -- Hence ∑ G * H' = -H
  have hGHprime : ∀ i j, (∑ k, Gτ i k * deriv (fun s => H s k j) τ) = -Hτ i j := by
    intro i j
    have h0 := hsum_zero i j
    rw [Finset.sum_add_distrib, hGprime_mul i j] at h0
    -- h0 : H + S = 0, want S = -H
    have hcomm : (∑ k, Gτ i k * deriv (fun s => H s k j) τ) + Hτ i j = 0 := by
      rw [add_comm]
      exact h0
    have hsub : (∑ k, Gτ i k * deriv (fun s => H s k j) τ) - (-Hτ i j) = 0 := by
      rw [sub_neg_eq_add]
      exact hcomm
    exact sub_eq_zero.mp hsub
  -- Now H' = -H*H via left-multiply by H
  -- H' p q = ∑ k, Hτ p k * (G*H') k q = ∑ k, Hτ p k * (-Hτ k q) = -(H*H) p q
  have hHG : Hτ * Gτ = 1 := by
    have hunit := ridgeGram_isUnit_det B R C τ hτ
    exact Matrix.nonsing_inv_mul _ hunit
  -- H'mat as matrix
  set H'mat : Matrix (B) (B) ℂ := fun k j => deriv (fun s => H s k j) τ with hHmat
  have hHmat_eq : H'mat = Hτ * (Gτ * H'mat) := by
    calc H'mat = 1 * H'mat := (Matrix.one_mul _).symm
      _ = (Hτ * Gτ) * H'mat := by rw [hHG]
      _ = Hτ * (Gτ * H'mat) := Matrix.mul_assoc _ _ _
  have hGH_entry : ∀ k q', ((Gτ * H'mat) k q') = -Hτ k q' := by
    intro k q'
    rw [Matrix.mul_apply]
    -- H'mat k' q' is deriv..., matches hGHprime
    exact hGHprime k q'
  have hfinal : H'mat p q = -((Hτ * Hτ) p q) := by
    calc H'mat p q = ((Hτ * (Gτ * H'mat)) p q) := by rw [← hHmat_eq]
      _ = ∑ k, Hτ p k * ((Gτ * H'mat) k q) := Matrix.mul_apply
      _ = ∑ k, Hτ p k * (-Hτ k q) := by simp only [hGH_entry]
      _ = -(∑ k, Hτ p k * Hτ k q) := by
        simp only [mul_neg, Finset.sum_neg_distrib]
      _ = -((Hτ * Hτ) p q) := by rw [Matrix.mul_apply]
  -- H'mat p q = deriv...
  have hentry_H : H'mat p q = deriv (fun s => H s p q) τ := rfl
  rw [hentry_H] at hfinal
  -- hfinal : deriv = -((H*H) p q), goal is deriv = -(((H*H)) p q) with Hτ = (Gτ)⁻¹
  -- Need to unfold Hτ, Gτ? They are set to ridgeGram inv, so rfl?
  exact hfinal

theorem ridgeProjection_entry_eq (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (s : ℝ) (i j : R) :
    AndersonAC.S6.ridgeProjection C s i j =
      ∑ q, ∑ p, C i p * ((AndersonAC.S6.ridgeGram C s)⁻¹ p q) * Cᴴ q j := by
  simp only [AndersonAC.S6.ridgeProjection, Matrix.mul_apply, Finset.sum_mul,
    Finset.mul_sum]

theorem ridgeProjection_hasDerivAt (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (τ : ℝ) (hτ : 0 < τ) (i j : R) :
    HasDerivAt (fun s => AndersonAC.S6.ridgeProjection C s i j)
      (-((C * (((AndersonAC.S6.ridgeGram C τ)⁻¹ *
        (AndersonAC.S6.ridgeGram C τ)⁻¹)) * Cᴴ) i j)) τ := by
  have hHderiv : ∀ p q, HasDerivAt (fun s => ((AndersonAC.S6.ridgeGram C s)⁻¹) p q)
      (-(((AndersonAC.S6.ridgeGram C τ)⁻¹ *
        (AndersonAC.S6.ridgeGram C τ)⁻¹) p q)) τ := by
    intro p q
    have h1 := inv_entry_hasDerivAt B R C τ hτ p q
    have h2 := inv_entry_deriv_eq B R C τ hτ p q
    rw [h2] at h1
    exact h1
  have hterm : ∀ q p, HasDerivAt
      (fun s => C i p * ((AndersonAC.S6.ridgeGram C s)⁻¹ p q) * Cᴴ q j)
      (C i p * (-(((AndersonAC.S6.ridgeGram C τ)⁻¹ *
        (AndersonAC.S6.ridgeGram C τ)⁻¹) p q)) * Cᴴ q j) τ := by
    intro q p
    have h1 : HasDerivAt (fun s => C i p * ((AndersonAC.S6.ridgeGram C s)⁻¹ p q))
        (C i p * (-(((AndersonAC.S6.ridgeGram C τ)⁻¹ *
          (AndersonAC.S6.ridgeGram C τ)⁻¹) p q))) τ :=
      HasDerivAt.const_mul _ (hHderiv p q)
    exact h1.mul_const _
  have hsum : HasDerivAt (fun s => ∑ q, ∑ p,
        C i p * ((AndersonAC.S6.ridgeGram C s)⁻¹ p q) * Cᴴ q j)
      (∑ q, ∑ p, C i p *
        (-(((AndersonAC.S6.ridgeGram C τ)⁻¹ *
          (AndersonAC.S6.ridgeGram C τ)⁻¹) p q)) * Cᴴ q j) τ := by
    apply HasDerivAt.fun_sum
    intro q _
    apply HasDerivAt.fun_sum
    intro p _
    exact hterm q p
  have hLHS : (fun s => ∑ q, ∑ p,
        C i p * ((AndersonAC.S6.ridgeGram C s)⁻¹ p q) * Cᴴ q j) =
      (fun s => AndersonAC.S6.ridgeProjection C s i j) := by
    funext s
    exact (ridgeProjection_entry_eq B R C s i j).symm
  have hRHS : (∑ q, ∑ p, C i p *
        (-(((AndersonAC.S6.ridgeGram C τ)⁻¹ *
          (AndersonAC.S6.ridgeGram C τ)⁻¹) p q)) * Cᴴ q j) =
      -((C * (((AndersonAC.S6.ridgeGram C τ)⁻¹ *
        (AndersonAC.S6.ridgeGram C τ)⁻¹)) * Cᴴ) i j) := by
    have hentry : ((C * (((AndersonAC.S6.ridgeGram C τ)⁻¹ *
        (AndersonAC.S6.ridgeGram C τ)⁻¹)) * Cᴴ) i j) =
        ∑ q, ∑ p, C i p * ((((AndersonAC.S6.ridgeGram C τ)⁻¹ *
          (AndersonAC.S6.ridgeGram C τ)⁻¹) p q)) * Cᴴ q j := by
      simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [hentry]
    simp only [mul_neg, neg_mul, Finset.sum_neg_distrib]
  rw [hLHS] at hsum
  rw [hRHS] at hsum
  exact hsum

theorem ridgeGram_isHermitian (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ) (τ : ℝ) :
    (AndersonAC.S6.ridgeGram C τ).IsHermitian := by
  have hgram : (AndersonAC.S6.gram C).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self C
  -- (τ:ℂ)•1 Hermitian since τ real
  have hself : IsSelfAdjoint ((τ : ℂ)) := by
    rw [IsSelfAdjoint]
    simp
  have hone : ((τ : ℂ) • (1 : Matrix (B) (B) ℂ)).IsHermitian :=
    Matrix.isHermitian_one.smul hself
  have hdef : AndersonAC.S6.ridgeGram C τ =
      AndersonAC.S6.gram C + ((τ : ℂ) • (1 : Matrix (B) (B) ℂ)) := rfl
  rw [hdef]
  exact hgram.add hone

theorem ridgeGram_inv_isHermitian (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (τ : ℝ) : ((AndersonAC.S6.ridgeGram C τ)⁻¹).IsHermitian :=
  (ridgeGram_isHermitian B R C τ).inv

theorem mul_star_self_re (z : ℂ) : RCLike.re (z * star z) = ‖z‖ ^ 2 := by
  simp [RCLike.star_def, RCLike.mul_re, RCLike.conj_re, RCLike.conj_im,
    RCLike.norm_sq_eq_def, mul_comm]

theorem ridge_projection_nonneg (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] (C : Matrix (R) (B) ℂ)
    (τ : ℝ) (i : R) :
    0 ≤ ((C * (((AndersonAC.S6.ridgeGram C τ)⁻¹ *
      (AndersonAC.S6.ridgeGram C τ)⁻¹)) * Cᴴ) i i).re := by
  set H := (AndersonAC.S6.ridgeGram C τ)⁻¹ with hH
  have hHherm : Hᴴ = H := (ridgeGram_inv_isHermitian B R C τ).eq
  set B := C * H with hB
  have hM : C * (H * H) * Cᴴ = B * Bᴴ := by
    rw [hB]
    calc C * (H * H) * Cᴴ = C * (H * Hᴴ) * Cᴴ := by rw [hHherm]
      _ = (C * H) * (C * H)ᴴ := by
        simp [Matrix.mul_assoc, Matrix.conjTranspose_mul]
  rw [hM]
  have hdot : (B * Bᴴ) i i = ∑ k, B i k * star (B i k) := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hre : RCLike.re ((B * Bᴴ) i i) = ∑ k, ‖B i k‖ ^ 2 := by
    rw [hdot, map_sum]
    congr 1
    funext k
    exact mul_star_self_re _
  have hnonneg : 0 ≤ RCLike.re ((B * Bᴴ) i i) := by
    rw [hre]
    apply Finset.sum_nonneg
    intro k _
    positivity
  exact hnonneg

/-- The inverse-square quadratic form is positive for each nonzero row of `C`. -/
theorem ridge_projection_pos_of_row_nonzero
    (B R : Type*) [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (C : Matrix R B ℂ) (τ : ℝ) (hτ : 0 < τ) (i : R)
    (hi : ∃ b, C i b ≠ 0) :
    0 < ((C * ((AndersonAC.S6.ridgeGram C τ)⁻¹ *
      (AndersonAC.S6.ridgeGram C τ)⁻¹) * Cᴴ) i i).re := by
  let G := AndersonAC.S6.ridgeGram C τ
  let H := G⁻¹
  let A := C * H
  have hGdet : IsUnit G.det := ridgeGram_isUnit_det B R C τ hτ
  have hHG : H * G = 1 := Matrix.nonsing_inv_mul _ hGdet
  have hHherm : Hᴴ = H := (ridgeGram_inv_isHermitian B R C τ).eq
  have hAA : C * (H * H) * Cᴴ = A * Aᴴ := by
    rw [show A = C * H by rfl]
    calc C * (H * H) * Cᴴ = C * (H * Hᴴ) * Cᴴ := by rw [hHherm]
      _ = (C * H) * (C * H)ᴴ := by
        simp [Matrix.mul_assoc, Matrix.conjTranspose_mul]
  have hdiag : (A * Aᴴ) i i = ∑ k, A i k * star (A i k) := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hsum_eq :
      ((C * (H * H) * Cᴴ) i i).re = ∑ k, ‖A i k‖ ^ 2 := by
    calc
      ((C * (H * H) * Cᴴ) i i).re = ((A * Aᴴ) i i).re := by rw [hAA]
      _ = (∑ k, A i k * star (A i k)).re := by rw [hdiag]
      _ = ∑ k, RCLike.re (A i k * star (A i k)) := by
        change RCLike.re (∑ k, A i k * star (A i k)) = _
        rw [map_sum]
      _ = ∑ k, ‖A i k‖ ^ 2 := by
        congr 1
        funext k
        exact mul_star_self_re _
  have hrow : ∃ k, A i k ≠ 0 := by
    by_contra hA
    have hArow : ∀ k, A i k = 0 := by
      intro k
      by_contra hk
      exact hA ⟨k, hk⟩
    have hAG : A * G = C := by
      dsimp [A, H, G]
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hGdet, Matrix.mul_one]
    obtain ⟨b, hb⟩ := hi
    apply hb
    calc C i b = (A * G) i b := by rw [hAG]
      _ = 0 := by simp [Matrix.mul_apply, hArow]
  obtain ⟨k, hk⟩ := hrow
  have hterm : 0 < ‖A i k‖ ^ 2 := by
    exact sq_pos_of_pos (norm_pos_iff.mpr hk)
  have hsum : 0 < ∑ k, ‖A i k‖ ^ 2 := by
    exact lt_of_lt_of_le hterm
      (Finset.single_le_sum (f := fun j => ‖A i j‖ ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ k))
  rw [hsum_eq]
  exact hsum

-- Final assembly: leverage derivative via Re + nonneg
theorem ridgeDerivative_proof
    {B R : Type*} [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (C : Matrix R B ℂ) (i : R) (τ : ℝ) (hτ : 0 < τ) :
    HasDerivAt (fun s => AndersonAC.S6.leverage C s i)
      (-((C * ((AndersonAC.S6.ridgeGram C τ)⁻¹ *
        (AndersonAC.S6.ridgeGram C τ)⁻¹) * Cᴴ) i i).re) τ ∧
    0 ≤ ((C * ((AndersonAC.S6.ridgeGram C τ)⁻¹ *
      (AndersonAC.S6.ridgeGram C τ)⁻¹) * Cᴴ) i i).re := by
  constructor
  · have hP := ridgeProjection_hasDerivAt B R C τ hτ i i
    -- leverage = Re(ridgeProjection)
    have hcomp := Complex.reCLM.hasFDerivAt.comp_hasDerivAt τ hP
    -- hcomp : HasDerivAt (reCLM ∘ P) (reCLM P') ; need to convert to leverage form
    have hRe : HasDerivAt (fun s => ((AndersonAC.S6.ridgeProjection C s i i).re))
        (((-((C * (((AndersonAC.S6.ridgeGram C τ)⁻¹ *
          (AndersonAC.S6.ridgeGram C τ)⁻¹)) * Cᴴ) i i)).re)) τ := by
      exact hcomp
    simpa [AndersonAC.S6.leverage] using hRe
  · exact ridge_projection_nonneg B R C τ i

end AndersonAC.SolS6RidgeLim
