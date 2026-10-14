import AndersonAC.S45.Definitions
import AndersonAC.S45.SchurProof
import AndersonAC.S45.FormDualityProof
import AndersonAC.S45.SweepEndpointProof

/-! `AndersonAC.S45.prestate_of_prefix` (04-sweep.tex:291–322): a numerical
prefix given by the cumulative Schur identities and the global caps is a
prestate. Uses the proved `schur_contraction_proof` and
`schur_dual_transport_proof`; never imports `Statements.lean`. -/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder

namespace AndersonAC.AgentS45
open AndersonAC.S45

namespace PrefixPrestate

/-- The survivors of a prefix, `Fin n ≃ (image e)ᶜᶜ`. -/
def surv {n n0 : ℕ} (e : Fin n ↪ Fin n0) :
    Fin n ≃ (↑((Finset.univ.image e)ᶜᶜ : Finset (Fin n0)) : Type) :=
  Equiv.ofBijective (fun i => ⟨e i, by simp⟩)
    ⟨fun i j h => e.injective (congrArg Subtype.val h), fun x => by
      obtain ⟨x, hx⟩ := x
      have hx' : x ∈ Finset.univ.image e := by simpa using hx
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hx'
      exact ⟨i, Subtype.ext hi⟩⟩

theorem surv_apply {n n0 : ℕ} (e : Fin n ↪ Fin n0) (i : Fin n) :
    ((surv e i : (↑((Finset.univ.image e)ᶜᶜ : Finset (Fin n0)) : Type)) : Fin n0) = e i := rfl

theorem embedCharge_apply_e {n n0 : ℕ} (e : Fin n ↪ Fin n0) (y : Fin n → ℝ) (j : Fin n) :
    embedCharge e y (e j) = y j := by
  unfold embedCharge
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk; simp [e.injective.ne hk]
  · simp

theorem embedCharge_apply_not {n n0 : ℕ} (e : Fin n ↪ Fin n0) (y : Fin n → ℝ) (i : Fin n0)
    (hi : i ∉ Finset.univ.image e) : embedCharge e y i = 0 := by
  unfold embedCharge
  refine Finset.sum_eq_zero fun j _ => ?_
  have : e j ≠ i := fun h => hi (Finset.mem_image.2 ⟨j, Finset.mem_univ _, h⟩)
  simp [this]

theorem pad_eq_embed {n n0 : ℕ} (e : Fin n ↪ Fin n0) (y : Fin n → ℝ) :
    (fun i => if hi : i ∈ (Finset.univ.image e)ᶜᶜ then (y ∘ (surv e).symm) ⟨i, hi⟩ else 0) =
      embedCharge e y := by
  funext i
  by_cases hi : i ∈ (Finset.univ.image e)ᶜᶜ
  · rw [dif_pos hi]
    have hi' : i ∈ Finset.univ.image e := by simpa using hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hi'
    have : (surv e).symm ⟨e j, hi⟩ = j := by
      rw [Equiv.symm_apply_eq]; rfl
    simp only [Function.comp_apply, this, embedCharge_apply_e]
  · rw [dif_neg hi, embedCharge_apply_not]
    simpa using hi

theorem embedCharge_neutral {n n0 : ℕ} (e : Fin n ↪ Fin n0) (y : Fin n → ℝ)
    (hy : neutral y) : neutral (embedCharge e y) := by
  unfold neutral embedCharge at *
  rw [Finset.sum_comm]
  simpa using hy

theorem embedCharge_weighted {n n0 : ℕ} (e : Fin n ↪ Fin n0) (y : Fin n → ℝ)
    (p : Fin n → ℝ) (p0 : Fin n0 → ℝ) (hp : ∀ i, p i = p0 (e i)) :
    (∑ i, embedCharge e y i ^ 2 / p0 i ^ 2) = ∑ j, y j ^ 2 / p j ^ 2 := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e))]
  · rw [Finset.sum_image (fun a _ b _ h => e.injective h)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [embedCharge_apply_e, hp]
  · intro i _ hi
    rw [embedCharge_apply_not e y i hi]; simp

theorem constantKernel_submatrix {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (Φ : κ ≃ ι) (A : RMat ι) (hA : constantKernel A) :
    constantKernel (A.submatrix Φ Φ) := by
  rcases hA with ⟨hsym, hnn, hzero⟩
  refine ⟨hsym.submatrix Φ, fun f => ?_, fun f => ?_⟩
  · rw [qform_submatrix]; exact hnn _
  · rw [qform_submatrix]
    constructor
    · intro hf
      rcases (hzero (f ∘ Φ.symm)).mp hf with ⟨a, ha⟩
      exact ⟨a, fun i => by simpa using ha (Φ i)⟩
    · rintro ⟨a, ha⟩
      exact (hzero _).mpr ⟨a, fun i => by simpa using ha (Φ.symm i)⟩

theorem constantKernel_fin0 (A : RMat (Fin 0)) : constantKernel A := by
  refine ⟨Matrix.IsSymm.ext fun i => i.elim0, fun f => by simp [qform], fun f => ?_⟩
  exact ⟨fun _ => ⟨0, fun i => i.elim0⟩, fun _ => by simp [qform]⟩

theorem power_nonneg' {x e : ℝ} (hx : 0 ≤ x) : 0 ≤ power x e := Real.rpow_nonneg hx e

theorem l1_nonneg' {ι : Type*} [Fintype ι] (y : ι → ℝ) : 0 ≤ l1 y :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem l2sq_nonneg' {ι : Type*} [Fintype ι] (y : ι → ℝ) : 0 ≤ l2sq y :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- The scalar comparison behind the `sharp` field. -/
theorem sharp_scalar {X Q Λ a ε C t : ℝ} (hC : 1 ≤ C) (ht : 0 ≤ t) (hQ : 0 ≤ Q) (hΛ : 0 ≤ Λ)
    (hε0 : 0 ≤ ε) (hεa : ε ≤ a) (ha : a ≤ 1 / 2)
    (hX : X ≤ ((1 + a) * Q + C * t * Λ) / (1 - ε)) :
    X ≤ (1 + 4 * C * a) * Q + 4 * C * t * Λ := by
  have h1ε : 0 < 1 - ε := by linarith
  refine hX.trans ((div_le_iff₀ h1ε).2 ?_)
  have ha0 : 0 ≤ a := hε0.trans hεa
  have hA : (1 + a) * Q ≤ (1 + 4 * C * a) * Q * (1 - ε) := by
    have hCε : 1 ≤ 2 * C * (1 - ε) := by nlinarith
    have h2a : 2 * a ≤ 4 * C * a * (1 - ε) := by
      nlinarith [mul_le_mul_of_nonneg_left hCε ha0]
    have : 1 + a ≤ (1 + 4 * C * a) * (1 - ε) := by nlinarith
    nlinarith
  have hB : C * t * Λ ≤ 4 * C * t * Λ * (1 - ε) := by
    have hCtΛ : 0 ≤ C * t * Λ := by positivity
    nlinarith
  nlinarith

end PrefixPrestate

open PrefixPrestate in
theorem prestate_of_prefix_proof : ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
    ∀ (n n0 : ℕ) (t : ℝ) (s : State (Fin n)) (K0 : CMat (Fin n0))
    (D0 L : RMat (Fin n0)) (J : CMat (Fin n0)) (p0 : Fin n0 → ℝ)
    (e : Fin n ↪ Fin n0) (Λ0 : Form (Fin n0)) (Λplus Wstar : Form (Fin n)),
    0 < t → t < t0 →
    (∀ i, ‖s.r i‖ ≤ C ∧ 1 / C ≤ s.p i ∧ s.p i ≤ C ∧ s.p i = p0 (e i)) →
    s.g.IsSymm → s.ward t → ‖K0‖ ≤ 1 / 3 → constantKernel D0 →
    L.IsSymm → L *ᵥ (fun _ => 1) = 0 →
    ‖J‖ ≤ power t (delta / 10) → formAbsLe (qform L) (qform D0) (power t (delta / 10)) →
    let E := (Finset.univ.image e)ᶜ
    (∀ i j, (1 - s.K t) i j =
      schur (1 - K0 - J) E ⟨e i, by simp [E]⟩ ⟨e j, by simp [E]⟩) →
    (∀ i j, s.D t i j = schur (D0 + L) E ⟨e i, by simp [E]⟩ ⟨e j, by simp [E]⟩) →
    (∀ y, neutral y → dualForm (qform D0) y ≤
      (1 + power t kappa) * (∑ i, y i^2 / p0 i^2) + C * t * Λ0 y) →
    (∀ y, neutral y → 0 ≤ Λ0 y) →
    (∀ y, Λplus y = Λ0 (embedCharge e y)) →
    (∀ y, neutral y → Λplus y ≤ C * power (l1 y) (4 / 3) * power (l2sq y) (1 / 3)) →
    (∀ y, neutral y → Wstar y ≤
      l2sq y + C * t * power (l1 y) (4 / 3) * power (l2sq y) (1 / 3)) →
    1 / (n : ℝ) ≤ C * power t (1 + delta + kappa) →
    (∀ i, s.fourthRow t Finset.univ i ≤ rowCap t ∧ ‖s.lag t i‖ ≤ power t beta) →
    Prestate t C' Λplus Wstar s := by
  intro C hC
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  have hδ : (0 : ℝ) < delta / 10 := by norm_num [delta]
  have hκ : (0 : ℝ) < kappa := by norm_num [kappa, delta]
  have hκδ : kappa ≤ delta / 10 := by norm_num [kappa, delta]
  obtain ⟨t1, ht1, hpow1⟩ := power_small hδ (show (0 : ℝ) < 1 / 6 by norm_num)
  obtain ⟨t2, ht2, hpow2⟩ := power_small hκ (show (0 : ℝ) < 1 / 2 by norm_num)
  refine ⟨4 * C, by positivity, min 1 (min t1 t2), lt_min one_pos (lt_min ht1 ht2), ?_⟩
  intro n n0 t s K0 D0 L J p0 e Λ0 Λplus Wstar ht htt hbroad hsym hward hK0 hD0 hL hL1 hJ
    hcap E hK hD hdual0 hΛ0 hΛ hfour hdfour hvol hrowlag
  have ht1' : t < 1 := lt_of_lt_of_le htt (min_le_left _ _)
  have htt1 : t < t1 := lt_of_lt_of_le htt ((min_le_right _ _).trans (min_le_left _ _))
  have htt2 : t < t2 := lt_of_lt_of_le htt ((min_le_right _ _).trans (min_le_right _ _))
  set ε := power t (delta / 10) with hεdef
  set a := power t kappa with hadef
  have hε0 : 0 ≤ ε := power_nonneg' ht.le
  have hε6 : ε < 1 / 6 := hpow1 t ht htt1
  have ha2 : a < 1 / 2 := hpow2 t ht htt2
  have hεa : ε ≤ a := Real.rpow_le_rpow_of_exponent_ge ht ht1'.le hκδ
  have hC4 : C ≤ 4 * C := by linarith
  -- survivors
  let Φ := surv e
  have hKmat : 1 - s.K t = (schur (1 - (K0 + J)) E).submatrix Φ Φ := by
    ext i j; rw [hK i j, ← sub_sub]; rfl
  have hDmat : s.D t = (schur (D0 + L) E).submatrix Φ Φ := by
    ext i j; rw [hD i j]; rfl
  -- contraction
  have hB : ‖K0 + J‖ ≤ 1 / 3 + ε := (norm_add_le _ _).trans (add_le_add hK0 hJ)
  have hcon := (schur_contraction_proof (K0 + J) E (1 / 3 + ε)
    ⟨by positivity, by linarith⟩ hB).2
  have hKeq : s.K t = (1 - schur (1 - (K0 + J)) E).submatrix Φ Φ := by
    have hsub : (1 - schur (1 - (K0 + J)) E).submatrix Φ Φ =
        1 - (schur (1 - (K0 + J)) E).submatrix Φ Φ := by
      ext i j; simp [Matrix.one_apply]
    rw [hsub, ← hKmat]; abel
  have hKcap : ‖s.K t‖ ≤ 1 / 2 := by
    rw [hKeq, norm_submatrix_equiv]; linarith
  have hKlt : ‖s.K t‖ < 1 := by linarith
  have hunit : IsUnit (1 - s.K t) := (Units.oneSub (s.K t) hKlt).isUnit
  -- kernel and dual transport
  have hkernel_sharp : constantKernel (s.D t) ∧ ∀ y, neutral y →
      s.X t y ≤ ((1 + a) * (∑ i, y i ^ 2 / s.p i ^ 2) + C * t * Λplus y) / (1 - ε) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      refine ⟨constantKernel_fin0 _, fun y _ => ?_⟩
      have hX0 : s.X t y = 0 := dualForm_qform_fin0 _ _
      rw [hX0]
      have hΛy : 0 ≤ Λplus y := by
        rw [hΛ]; exact hΛ0 _ (embedCharge_neutral e y (by simp [neutral]))
      apply div_nonneg _ (by linarith)
      have : (∑ i : Fin 0, y i ^ 2 / s.p i ^ 2) = 0 := by simp
      rw [this, mul_zero, zero_add]
      exact mul_nonneg (mul_nonneg hC0.le ht.le) hΛy
    · have hproper : E ≠ Finset.univ := by
        intro hE
        have hmem : e ⟨0, hn⟩ ∈ E := hE ▸ Finset.mem_univ _
        simp [E] at hmem
      have hT := schur_dual_transport_proof D0 L E ε ⟨hε0, by linarith⟩ hD0 hL hL1 hcap hproper
      refine ⟨hDmat ▸ constantKernel_submatrix Φ _ hT.1, fun y hy => ?_⟩
      have hyΦ : neutral (y ∘ Φ.symm) := by
        unfold neutral at *
        rw [← hy]
        exact Fintype.sum_equiv Φ.symm _ _ (fun _ => rfl)
      have hup := (hT.2 (y ∘ Φ.symm) hyΦ).2
      have hpad := pad_eq_embed e y
      change (fun i => if hi : i ∈ Eᶜ then (y ∘ Φ.symm) ⟨i, hi⟩ else 0) = embedCharge e y
        at hpad
      rw [hpad] at hup
      have hX : s.X t y = dualForm (qform (schur (D0 + L) E)) (y ∘ Φ.symm) := by
        change dualForm (qform (s.D t)) y = _
        rw [hDmat, dualForm_submatrix]
      rw [hX]
      refine hup.trans (div_le_div_of_nonneg_right ?_ (by linarith))
      have h0 := hdual0 _ (embedCharge_neutral e y hy)
      rw [embedCharge_weighted e y s.p p0 (fun i => (hbroad i).2.2.2), ← hΛ] at h0
      exact h0
  refine
    { scale := ⟨ht, ht1'⟩
      broad := fun i => ⟨(hbroad i).1.trans hC4,
        le_trans (one_div_le_one_div_of_le hC0 hC4) (hbroad i).2.1, (hbroad i).2.2.1.trans hC4⟩
      symmetric := hsym
      ward := hward
      K_cap := hKcap
      invertible := hunit
      kernel := hkernel_sharp.1
      row_cap := fun i => (hrowlag i).1
      lag_cap := fun i => (hrowlag i).2
      sharp := ?_
      fourier := ?_
      dual_fourier := ?_
      volume := ?_ }
  · intro y hy
    have hΛy : 0 ≤ Λplus y := by rw [hΛ]; exact hΛ0 _ (embedCharge_neutral e y hy)
    have hQ : 0 ≤ ∑ i, y i ^ 2 / s.p i ^ 2 :=
      Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (sq_nonneg _)
    have := sharp_scalar hC ht.le hQ hΛy hε0 hεa ha2.le (hkernel_sharp.2 y hy)
    simpa [mul_assoc] using this
  · intro y hy
    refine (hfour y hy).trans ?_
    have := mul_nonneg (power_nonneg' (e := 4 / 3) (l1_nonneg' y))
      (power_nonneg' (e := 1 / 3) (l2sq_nonneg' y))
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right hC4 this
  · intro y hy
    refine (hdfour y hy).trans ?_
    have := mul_nonneg (mul_nonneg ht.le (power_nonneg' (e := 4 / 3) (l1_nonneg' y)))
      (power_nonneg' (e := 1 / 3) (l2sq_nonneg' y))
    have h2 := mul_le_mul_of_nonneg_right hC4 this
    simp only [mul_assoc] at h2 ⊢
    linarith
  · rw [Fintype.card_fin]
    exact hvol.trans (mul_le_mul_of_nonneg_right hC4 (power_nonneg' ht.le))

end AndersonAC.AgentS45
