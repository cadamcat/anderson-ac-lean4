import AndersonAC.AgentS78.Construction.StagePhaseDoneCoreAlg
import AndersonAC.AgentS78.Construction.StagePhaseDoneParts
import AndersonAC.S6.CoreSupport
import AndersonAC.S6Compl.CompletionBounds
import AndersonAC.AgentS78.ResetJoin

/-!
# The DONE exit of a clearing attempt: core completion on the scratch data. Proof of the sub-statement `DoneCoreStatement` (Lemma 6.1,
06-clearing.tex:82–182, applied at the core-phase snapshot, 07-assembly.tex:399–413).

With `G` the snapshot inverse on `A`, `g'` the final inverse on `A' = A \ core` and
`dg = g' − G` on `A'`, the scattering change `ds = 2it √p dg √p` (zero off `A'`)

* factors through the cross block: `ds = C Y Cᵀ` with `C = xCross` (`coreElim_repr`), so
  `Π_C ds = ds`;
* is a difference of the new scattering matrix and a compression of the old one, so
  `‖ds‖ ≤ 2` (unitarity, `scattering_from_inverse`);
* is symmetric.

`SolS6.completionBounds_proof` then gives the Lemma 6.1 bounds from the projection cap
`xReady` (`l = t^{1+e0}`).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78.DoneA

open AndersonAC.S78 AndersonAC.AgentS78
open scoped BigOperators Matrix Matrix.Norms.L2Operator

variable {d m : ℕ}

theorem fullInv_symm (A : Finset (Torus d m)) (M : Matrix (Torus d m) (Torus d m) ℝ) (t : ℝ)
    (r : Torus d m → ℂ) (hM : ∀ i k, M i k = M k i) (i k : Torus d m) :
    fullInv A M t r i k = fullInv A M t r k i := by
  by_cases hik : i ∈ A ∧ k ∈ A
  · rw [fullInv_entry A M t r ⟨i, hik.1⟩ ⟨k, hik.2⟩, fullInv_entry A M t r ⟨k, hik.2⟩ ⟨i, hik.1⟩]
    set 𝓜 := AndersonAC.S6.dampedMatrix (restrictM A M) t (fun a : A => r a)
    have hT : 𝓜ᵀ = 𝓜 := by
      ext a b
      rw [Matrix.transpose_apply]
      refine (dampedMatrix_entry A M t r b a).trans (Eq.trans ?_ (dampedMatrix_entry A M t r a b).symm)
      unfold dEnt
      rw [hM b.val a.val]
      by_cases hab : (b : Torus d m) = a
      · rw [hab]
      · rw [if_neg hab, if_neg (Ne.symm hab)]
    have h := congrFun (congrFun (Matrix.transpose_nonsing_inv 𝓜) ⟨k, hik.2⟩) ⟨i, hik.1⟩
    rw [Matrix.transpose_apply, hT] at h
    exact h
  · have h1 : ¬ (k ∈ A ∧ i ∈ A) := fun h => hik ⟨h.2, h.1⟩
    unfold fullInv
    rw [dif_neg hik, dif_neg h1]

theorem xCross_entry (t : ℝ) (r : Torus d m → ℂ) (A core : Finset (Torus d m))
    (Mh : Matrix (Torus d m) (Torus d m) ℝ) (hcA : core ⊆ A) (i : Torus d m)
    (b : {b // b ∈ core}) :
    xCross t r A (restrictM A Mh) core i b =
      if i ∈ A ∧ i ∉ core then (2 * Complex.I * (t : ℂ)) *
        ((Real.sqrt ((r i).im) : ℂ) * fullInv A Mh t r i b * (Real.sqrt ((r b).im) : ℂ))
      else 0 := by
  have hb : (b : Torus d m) ∈ A := hcA b.2
  unfold xCross
  by_cases hi : i ∈ A
  · by_cases hic : i ∈ core
    · rw [dif_pos hi, if_pos hic, if_neg (fun h => h.2 hic)]
    · rw [dif_pos hi, if_neg hic, dif_pos hb, if_pos ⟨hi, hic⟩]
      have hne : (⟨i, hi⟩ : {i // i ∈ A}) ≠ ⟨b, hb⟩ := fun h => hic (by
        have := congrArg Subtype.val h; simp only at this; rw [this]; exact b.2)
      unfold fullInv
      rw [dif_pos ⟨hi, hb⟩]
      simp only [AndersonAC.S6.scatteringOfDamping, AndersonAC.S6.sqrtDamping,
        AndersonAC.S6.imagDamping, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add,
        Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_mul, Matrix.mul_diagonal]
  · rw [dif_neg hi, if_neg (fun h => hi h.1)]

/-- The change of the damped inverse on the survivors, zero elsewhere. -/
def chgDg (t : ℝ) (r : Torus d m → ℂ) (A : Finset (Torus d m))
    (Mh : Matrix (Torus d m) (Torus d m) ℝ) (A' : Finset (Torus d m))
    (M' : Matrix (Torus d m) (Torus d m) ℝ) : Matrix (Torus d m) (Torus d m) ℂ := fun i k =>
  if i ∈ A' ∧ k ∈ A' then fullInv A' M' t r i k - fullInv A Mh t r i k else 0

/-- The corresponding scattering change `2it √p dg √p`. -/
def chgDs (t : ℝ) (r : Torus d m → ℂ) (A : Finset (Torus d m))
    (Mh : Matrix (Torus d m) (Torus d m) ℝ) (A' : Finset (Torus d m))
    (M' : Matrix (Torus d m) (Torus d m) ℝ) : Matrix (Torus d m) (Torus d m) ℂ :=
  (2 * Complex.I * (t : ℂ)) • (AndersonAC.S6.sqrtDamping (fun i => (r i).im) *
    chgDg t r A Mh A' M' * AndersonAC.S6.sqrtDamping (fun i => (r i).im))

/-- **The scattering change of sequential eliminations is a supported contraction**:
`‖ds‖ ≤ 2`, `Π_C ds = ds` for the cross block `C = xCross` of the eliminated set, `ds`
symmetric. -/
theorem supported_change (t : ℝ) (r : Torus d m → ℂ) (core A A' : Finset (Torus d m))
    (Mh M' : Matrix (Torus d m) (Torus d m) ℝ) (ht : 0 < t) (hr : ∀ i, 0 < (r i).im)
    (hsym : ∀ i k, Mh i k = Mh k i) (hcA : core ⊆ A) (hce : CoreElim core A Mh A' M')
    (hdisj : Disjoint core A') :
    ‖chgDs t r A Mh A' M'‖ ≤ 2 ∧
      AndersonAC.S6.rangeProjection (xCross t r A (restrictM A Mh) core) * chgDs t r A Mh A' M' =
        chgDs t r A Mh A' M' ∧ (chgDs t r A Mh A' M').IsSymm := by
  obtain ⟨hA'A, hAA'⟩ := hce.sub
  have hA'mem : ∀ i, i ∈ A' ↔ i ∈ A ∧ i ∉ core := by
    intro i
    constructor
    · intro hi
      exact ⟨hA'A hi, fun hc => Finset.disjoint_left.mp hdisj hc hi⟩
    · rintro ⟨hi, hic⟩
      by_contra hni
      exact hic (hAA' (Finset.mem_sdiff.mpr ⟨hi, hni⟩))
  obtain ⟨hM', X, hXs, hX⟩ := coreElim_repr core A Mh t r hsym ht hr hce
  set G := fullInv A Mh t r with hG
  set g' := fullInv A' M' t r with hg'
  set p : Torus d m → ℝ := fun i => (r i).im with hp
  set dg := chgDg t r A Mh A' M' with hdg
  set ds := chgDs t r A Mh A' M' with hds
  have hdg_apply : ∀ i k, dg i k = if i ∈ A' ∧ k ∈ A' then g' i k - G i k else 0 :=
    fun i k => rfl
  set C := xCross t r A (restrictM A Mh) core with hC
  set τ : ℂ := 2 * Complex.I * (t : ℂ) with hτ
  have hτ0 : τ ≠ 0 := by
    rw [hτ]
    exact mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr ht.ne')
  have hsq0 : ∀ i, (Real.sqrt (p i) : ℂ) ≠ 0 := fun i =>
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hr i)).ne'
  have hds_entry : ∀ i k, ds i k = τ * ((Real.sqrt (p i) : ℂ) * dg i k * (Real.sqrt (p k) : ℂ)) := by
    intro i k
    simp only [hds, chgDs, ← hdg, ← hp, AndersonAC.S6.sqrtDamping, Matrix.smul_apply, smul_eq_mul,
      Matrix.diagonal_mul, Matrix.mul_diagonal]
    rfl
  -- the support of the change
  have hGsym := fullInv_symm A Mh t r hsym
  set Y : Matrix {b // b ∈ core} {b // b ∈ core} ℂ := fun b b' =>
    X b b' / (τ * (Real.sqrt (p b) : ℂ) * (Real.sqrt (p b') : ℂ)) with hY
  have hXsum : ∀ i k, ∑ b, ∑ b', G i b * X b b' * G b' k =
      ∑ b : {b // b ∈ core}, ∑ b' : {b // b ∈ core}, G i b * X b b' * G b' k := by
    intro i k
    have h1 : ∀ f : Torus d m → ℂ, (∀ b, b ∉ core → f b = 0) →
        ∑ b, f b = ∑ b : {b // b ∈ core}, f b := by
      intro f hf
      rw [Finset.sum_coe_sort core f]
      exact (Finset.sum_subset (Finset.subset_univ core) fun b _ hb => hf b hb).symm
    rw [h1 _ (fun b hb => Finset.sum_eq_zero fun b' _ => by
      have : X b b' = 0 := by
        by_contra hz; exact hb (hXs b b' hz).1.1
      rw [this, mul_zero, zero_mul])]
    refine Finset.sum_congr rfl fun b _ => ?_
    exact h1 _ (fun b' hb' => by
      have : X b b' = 0 := by
        by_contra hz; exact hb' (hXs b b' hz).2.1
      rw [this, mul_zero, zero_mul])
  have hfac : ds = C * Y * Cᵀ := by
    ext i k
    rw [hds_entry, Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    by_cases hik : i ∈ A' ∧ k ∈ A'
    · have hi := (hA'mem i).mp hik.1
      have hk := (hA'mem k).mp hik.2
      have hdgik : dg i k = ∑ b : {b // b ∈ core}, ∑ b' : {b // b ∈ core},
          G i b * X b b' * G b' k := by
        rw [hdg_apply, if_pos hik]
        rw [hX i hik.1 k hik.2, ← hXsum]
        ring
      rw [hdgik]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun b _ => ?_
      have hsb := hsq0 b
      have hsb' := hsq0 b'
      have hsi := hsq0 i
      have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
      simp only [hC, xCross_entry t r A core Mh hcA, if_pos hi, if_pos hk, hY, hτ, hp] at hsb hsb' hsi ⊢
      have hG' : G (b' : Torus d m) k = fullInv A Mh t r k b' := hGsym b' k
      have hGib : G i (b : Torus d m) = fullInv A Mh t r i b := rfl
      rw [hG', hGib]
      field_simp
    · have h0 : dg i k = 0 := by rw [hdg_apply, if_neg hik]
      rw [h0, mul_zero, zero_mul, mul_zero]
      symm
      rcases not_and_or.mp hik with hi | hk
      · have hCi : ∀ b, C i b = 0 := fun b => by
          rw [hC, xCross_entry t r A core Mh hcA, if_neg (fun h => hi ((hA'mem i).mpr h))]
        exact Finset.sum_eq_zero fun b' _ => by
          rw [Finset.sum_eq_zero fun b _ => by rw [hCi b, zero_mul], zero_mul]
      · have hCk : ∀ b, C k b = 0 := fun b => by
          rw [hC, xCross_entry t r A core Mh hcA, if_neg (fun h => hk ((hA'mem k).mpr h))]
        exact Finset.sum_eq_zero fun b' _ => by rw [hCk b', mul_zero]
  have hleft : AndersonAC.S6.rangeProjection C * ds = ds := by
    rw [hfac, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      AndersonAC.SolS6.projection_mul_source]
  -- symmetry
  have hg'sym := fullInv_symm A' M' t r hM'
  have hdsym : ds.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i k
    rw [hds_entry, hds_entry]
    have : dg k i = dg i k := by
      rw [hdg_apply, hdg_apply]
      by_cases hik : i ∈ A' ∧ k ∈ A'
      · rw [if_pos ⟨hik.2, hik.1⟩, if_pos hik]
        exact congrArg₂ (· - ·) (hg'sym k i) (hGsym k i)
      · rw [if_neg (fun h => hik ⟨h.2, h.1⟩), if_neg hik]
    rw [this]
    ring
  -- the norm
  have hnorm : ‖ds‖ ≤ 2 := by
    let incl : {a // a ∈ A'} → {a // a ∈ A} := fun a => ⟨a.val, hA'A a.2⟩
    have hincl : Function.Injective incl := fun a b h => by
      have h' := congrArg Subtype.val h
      exact Subtype.ext h'
    set g₂ := AndersonAC.S6.activeInverse (restrictM A' M') t (fun a : {a // a ∈ A'} => r a)
    set g₁ := AndersonAC.S6.activeInverse (restrictM A Mh) t (fun a : {a // a ∈ A} => r a)
    set S₂ := AndersonAC.S6.scattering t (fun a : {a // a ∈ A'} => r a) g₂
    set S₁ := AndersonAC.S6.scattering t (fun a : {a // a ∈ A} => r a) g₁
    have hpad : ds = padM A' (S₂ - S₁.submatrix incl incl) := by
      ext i k
      rw [hds_entry]
      unfold padM
      by_cases hi : i ∈ A'
      · by_cases hk : k ∈ A'
        · rw [dif_pos hi, dif_pos hk]
          have hdgik : dg i k = g' i k - G i k := by rw [hdg_apply, if_pos (And.intro hi hk)]
          rw [hdgik, hg', hG]
          unfold fullInv
          rw [dif_pos ⟨hi, hk⟩, dif_pos ⟨hA'A hi, hA'A hk⟩]
          simp only [S₂, S₁, Matrix.sub_apply, Matrix.submatrix_apply, incl,
            AndersonAC.S6.scattering, AndersonAC.S6.scatteringOfDamping,
            AndersonAC.S6.sqrtDamping, AndersonAC.S6.imagDamping, Matrix.add_apply,
            Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_mul, Matrix.mul_diagonal]
          by_cases hik : i = k
          · subst hik; simp only [Matrix.one_apply_eq]; rw [hτ]; ring
          · rw [Matrix.one_apply_ne (fun h => hik (congrArg Subtype.val h)),
              Matrix.one_apply_ne (fun h => hik (congrArg Subtype.val h))]
            rw [hτ]; ring
        · rw [dif_pos hi, dif_neg hk]
          have : dg i k = 0 := by rw [hdg_apply, if_neg (fun h => hk h.2)]
          rw [this]; ring
      · rw [dif_neg hi]
        have : dg i k = 0 := by rw [hdg_apply, if_neg (fun h => hi h.1)]
        rw [this]; ring
    have hunit : ∀ (B : Finset (Torus d m)) (M : Matrix (Torus d m) (Torus d m) ℝ),
        (∀ i k, M i k = M k i) →
        AndersonAC.S6.scattering t (fun a : {a // a ∈ B} => r a)
            (AndersonAC.S6.activeInverse (restrictM B M) t (fun a : {a // a ∈ B} => r a)) *
          (AndersonAC.S6.scattering t (fun a : {a // a ∈ B} => r a)
            (AndersonAC.S6.activeInverse (restrictM B M) t (fun a : {a // a ∈ B} => r a)))ᴴ = 1 := by
      intro B M hMs
      have hU := damped_unit B M t r hMs ht hr
      have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hU
      refine (AndersonAC.SolS6.scattering_from_inverse ((restrictM B M).map Complex.ofReal)
        (AndersonAC.S6.activeInverse (restrictM B M) t (fun a : {a // a ∈ B} => r a)) t
        (fun a : {a // a ∈ B} => r a) ?_ ?_ (fun a => (hr a).le) ?_).2
      · ext a b
        simp only [Matrix.transpose_apply, Matrix.map_apply, restrictM, Matrix.submatrix_apply]
        rw [hMs]
      · intro i k; simp
      · exact ⟨Matrix.mul_nonsing_inv _ hdet, Matrix.nonsing_inv_mul _ hdet⟩
    have h2 : ‖S₂‖ ≤ 1 := AndersonAC.SolS6.coisometry_norm_le _ (hunit A' M' hM')
    have h1 : ‖S₁.submatrix incl incl‖ ≤ 1 := by
      rw [← inclMat_block incl S₁]
      calc ‖(inclMat incl)ᴴ * S₁ * inclMat incl‖ ≤ ‖(inclMat incl)ᴴ * S₁‖ * ‖inclMat incl‖ :=
            Matrix.l2_opNorm_mul _ _
        _ ≤ (‖(inclMat incl)ᴴ‖ * ‖S₁‖) * ‖inclMat incl‖ := by
            gcongr; exact Matrix.l2_opNorm_mul _ _
        _ ≤ (1 * 1) * 1 := by
            rw [Matrix.l2_opNorm_conjTranspose]
            gcongr
            · exact norm_inclMat_le incl hincl
            · exact AndersonAC.SolS6.coisometry_norm_le _ (hunit A Mh hsym)
            · exact norm_inclMat_le incl hincl
        _ = 1 := by norm_num
    rw [hpad, norm_padM]
    calc ‖S₂ - S₁.submatrix incl incl‖ ≤ ‖S₂‖ + ‖S₁.submatrix incl incl‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add h2 h1
      _ = 2 := by norm_num
  exact ⟨hnorm, hleft, hdsym⟩

/-- **Proof of the core sub-statement.** -/
theorem doneCore_proof (d : ℕ) : DoneCoreStatement d := by
  intro cP CP hcP _hCP
  refine ⟨max 1 (2 / cP ^ 2 + 2 / cP), 1, le_max_left _ _, one_pos, ?_⟩
  intro m t r core A A' Mh M' ht _ hbroad hsym _hne hcA hcard hready hce hdisj
  have hr : ∀ i, 0 < (r i).im := fun i => hcP.trans_le (hbroad i).1
  obtain ⟨hnorm, hleft, hdsym⟩ := supported_change t r core A A' Mh M' ht hr hsym hcA hce hdisj
  set dg := chgDg t r A Mh A' M' with hdg
  set p : Torus d m → ℝ := fun i => (r i).im with hp
  set C := xCross t r A (restrictM A Mh) core with hC
  -- Lemma 6.1 bounds
  have hl : (0 : ℝ) ≤ AndersonAC.S6.leverageScale t := by
    unfold AndersonAC.S6.leverageScale; positivity
  obtain ⟨hb1, hb2, -, hb4⟩ := AndersonAC.SolS6.completionBounds_proof {b // b ∈ core} (Torus d m)
    t cP (AndersonAC.S6.leverageScale t) p C dg (chgDs t r A Mh A' M') ht hcP hl (fun i => (hbroad i).1)
    hnorm hleft hdsym rfl hready
  have hcd : coreDiff t r A Mh A' M' = AndersonAC.S6.scaledInverse t dg := by
    ext i k
    unfold coreDiff AndersonAC.S6.scaledInverse
    rw [Matrix.smul_apply, smul_eq_mul, hdg]
    unfold chgDg
    split_ifs <;> simp
  have hlev : AndersonAC.S6.leverageScale t = t * t ^ (0.44 * delta) := by
    unfold AndersonAC.S6.leverageScale
    rw [Real.rpow_add ht, Real.rpow_one]
    congr 2
    norm_num [AndersonAC.S6.e0, AndersonAC.S6.delta, delta]
  have hte : 0 ≤ t ^ (0.44 * delta) := Real.rpow_nonneg ht.le _
  have hCc1 : 2 / cP ≤ max 1 (2 / cP ^ 2 + 2 / cP) :=
    le_max_of_le_right (le_add_of_nonneg_left (by positivity))
  have hCc2 : 2 / cP ^ 2 ≤ max 1 (2 / cP ^ 2 + 2 / cP) :=
    le_max_of_le_right (le_add_of_nonneg_right (by positivity))
  refine ⟨?_, ?_, ?_⟩
  · intro i k
    rw [hcd, AndersonAC.S6.scaledInverse, Matrix.smul_apply, smul_eq_mul, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have h := hb1 i k
    rw [hlev] at h
    have h' : ‖dg i k‖ ≤ 2 / cP * t ^ (0.44 * delta) := by
      calc ‖dg i k‖ ≤ 2 * (t * t ^ (0.44 * delta)) / (t * cP) := h
        _ = 2 / cP * t ^ (0.44 * delta) := by field_simp
    calc Real.sqrt t * ‖dg i k‖ ≤ Real.sqrt t * (2 / cP * t ^ (0.44 * delta)) :=
          mul_le_mul_of_nonneg_left h' (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt t * (max 1 (2 / cP ^ 2 + 2 / cP) * t ^ (0.44 * delta)) := by
          gcongr
      _ = _ := by ring
  · intro i
    rw [hcd]
    have h := hb2 i
    rw [hlev] at h
    calc rowTwo (AndersonAC.S6.scaledInverse t dg) i
        = AndersonAC.S6.sqRow (AndersonAC.S6.scaledInverse t dg) i := rfl
      _ ≤ 2 * (t * t ^ (0.44 * delta)) / (t * cP ^ 2) := h
      _ = 2 / cP ^ 2 * t ^ (0.44 * delta) := by field_simp
      _ ≤ _ := by gcongr
  · rw [hcd]
    have h := hb4
    rw [Fintype.card_coe] at h
    have hcard' : ((core.card : ℝ)) / (t * cP ^ 2) ≤ 1 / cP ^ 2 * t ^ (-1 - nu d) := by
      rw [show (-1 - nu d) = -nu d + (-1) by ring, Real.rpow_add ht, Real.rpow_neg_one]
      rw [div_le_iff₀ (by positivity)]
      calc (core.card : ℝ) ≤ t ^ (-nu d) := hcard
        _ = 1 / cP ^ 2 * (t ^ (-nu d) * t⁻¹) * (t * cP ^ 2) := by field_simp
    calc frobeniusSq (AndersonAC.S6.scaledInverse t dg)
        = AndersonAC.S6.hsSq (AndersonAC.S6.scaledInverse t dg) := rfl
      _ ≤ _ := h
      _ ≤ 1 / cP ^ 2 * t ^ (-1 - nu d) := hcard'
      _ ≤ _ := by
          gcongr
          exact (div_le_div_of_nonneg_right (by norm_num) (by positivity)).trans hCc2

end AndersonAC.AgentS78.DoneA
