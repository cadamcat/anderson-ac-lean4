import AndersonAC.S3.HelperStatements2

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace AndersonAC.S3

private def quadStep (L : ℕ) : ℝ := 2 * Real.pi / (L : ℝ)

private def quadCorner {d L : ℕ} (q : Fin d → Fin L) : Frequency d :=
  fun j => -Real.pi + quadStep L * (q j).val

private def quadCell {d L : ℕ} (q : Fin d → Fin L) : Set (Frequency d) :=
  Set.pi Set.univ (fun j => Set.Ico (quadCorner q j) (quadCorner q j + quadStep L))

private def centeredCoord (L : ℕ) [NeZero L] : Fin L ≃ ZMod L :=
  (ZMod.finEquiv L).toEquiv.trans
    (Equiv.addRight ((L / 2 : ℕ) : ZMod L))

private def centeredTorusEquiv (d L : ℕ) [NeZero L] : (Fin d → Fin L) ≃ Torus d L :=
  Equiv.piCongrRight fun _ => centeredCoord L

private lemma centeredCoord_apply {L : ℕ} [NeZero L] (i : Fin L) :
    centeredCoord L i = (i.val : ZMod L) + ((L / 2 : ℕ) : ZMod L) := by
  have hfin : (ZMod.finEquiv L).toEquiv i = (i.val : ZMod L) := by
    cases L with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ L =>
      apply ZMod.val_injective (L + 1)
      simp only [ZMod.finEquiv, RingEquiv.refl_apply, ZMod.val_natCast,
        Nat.mod_eq_of_lt i.isLt]
      rfl
  change Equiv.addRight ((L / 2 : ℕ) : ZMod L) ((ZMod.finEquiv L).toEquiv i) = _
  rw [hfin, Equiv.coe_addRight]

private lemma quadStep_pos (L : ℕ) [NeZero L] : 0 < quadStep L := by
  unfold quadStep
  apply div_pos
  · positivity
  · exact_mod_cast NeZero.pos L

private lemma quadStep_mul_L (L : ℕ) [NeZero L] : quadStep L * (L : ℝ) = 2 * Real.pi := by
  unfold quadStep
  field_simp [NeZero.ne L]
  <;> ring

private lemma centered_gridAngle {d L : ℕ} [NeZero L] (hL : Even L)
    (q : Fin d → Fin L) (j : Fin d) :
    gridAngle (centeredTorusEquiv d L q) j = quadCorner q j := by
  have hLpos : 0 < L := NeZero.pos L
  have hhalf : L / 2 < L := by omega
  rcases hL with ⟨n, hn⟩
  have heq : L = 2 * (L / 2) := by omega
  have hhalfpos : 0 < L / 2 := by omega
  let i := q j
  have hval : (centeredCoord L i).val =
      if i.val < L / 2 then i.val + L / 2 else i.val - L / 2 := by
    rw [centeredCoord_apply]
    rw [ZMod.val_add]
    have hhalfmod : L / 2 % L = L / 2 := Nat.mod_eq_of_lt hhalf
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt, hhalfmod]
    by_cases hi : i.val < L / 2
    · have hsum : i.val + L / 2 < L := by omega
      rw [Nat.mod_eq_of_lt hsum, if_pos hi]
    · have hsum : i.val + L / 2 = L + (i.val - L / 2) := by omega
      rw [hsum, Nat.add_mod, Nat.mod_self, zero_add]
      have hsub : i.val - L / 2 < L := by omega
      rw [if_neg hi]
      simp [Nat.mod_eq_of_lt hsub]
  by_cases hi : i.val < L / 2
  · have hb : ¬ 2 * (centeredCoord L i).val < L := by
      rw [hval, if_pos hi]
      omega
    change (2 * Real.pi * (if 2 * (centeredCoord L i).val < L then
      ((centeredCoord L i).val : ℝ) else
      ((centeredCoord L i).val : ℝ) - (L : ℝ)) / (L : ℝ)) = _
    rw [if_neg hb, hval, if_pos hi]
    simp only [quadCorner, quadStep]
    push_cast
    field_simp [NeZero.ne L]
    rw [show (L : ℝ) = 2 * (L / 2 : ℕ) by exact_mod_cast heq]
    ring
  · have hi' : L / 2 ≤ i.val := Nat.le_of_not_gt hi
    have hb : 2 * (centeredCoord L i).val < L := by
      rw [hval, if_neg hi]
      omega
    change (2 * Real.pi * (if 2 * (centeredCoord L i).val < L then
      ((centeredCoord L i).val : ℝ) else
      ((centeredCoord L i).val : ℝ) - (L : ℝ)) / (L : ℝ)) = _
    rw [if_pos hb, hval, if_neg hi]
    simp only [quadCorner, quadStep]
    push_cast
    field_simp [NeZero.ne L]
    rw [show (L : ℝ) = 2 * (L / 2 : ℕ) by exact_mod_cast heq]
    rw [Nat.cast_sub hi']
    dsimp [i]
    ring

private lemma quadCell_measurable {d L : ℕ} (q : Fin d → Fin L) :
    MeasurableSet (quadCell q) := by
  change MeasurableSet (Set.pi Set.univ fun j =>
    Set.Ico (quadCorner q j) (quadCorner q j + quadStep L))
  exact MeasurableSet.pi Set.countable_univ fun j _ => measurableSet_Ico

private lemma quadCell_subset_cube {d L : ℕ} [NeZero L]
    (q : Fin d → Fin L) : quadCell q ⊆ torusCube d := by
  intro x hx
  change (∀ j ∈ Set.univ, x j ∈ Set.Ico (quadCorner q j)
    (quadCorner q j + quadStep L)) at hx
  change ∀ j ∈ Set.univ, x j ∈ Set.Ico (-Real.pi) Real.pi
  intro j _
  have hq : (q j).val < L := (q j).isLt
  have hδ : 0 < quadStep L := quadStep_pos L
  rcases hx j (Set.mem_univ _) with ⟨hleft, hupper⟩
  constructor
  · have hcorner : -Real.pi ≤ quadCorner q j := by
      unfold quadCorner
      have hprod : 0 ≤ quadStep L * ((q j).val : ℝ) :=
        mul_nonneg hδ.le (Nat.cast_nonneg _)
      linarith
    exact hcorner.trans hleft
  · have hright : quadCorner q j + quadStep L ≤ Real.pi := by
      rw [quadCorner]
      calc
        -Real.pi + quadStep L * (q j).val + quadStep L
            = -Real.pi + quadStep L * ((q j).val + 1) := by ring
        _ ≤ -Real.pi + quadStep L * L := by
          have hqR : ((q j).val : ℝ) + 1 ≤ (L : ℝ) := by
            exact_mod_cast (Nat.succ_le_iff.mpr hq)
          nlinarith [mul_le_mul_of_nonneg_left hqR hδ.le]
        _ = Real.pi := by rw [quadStep_mul_L]; ring
    exact lt_of_lt_of_le hupper hright

private lemma quadCell_union {d L : ℕ} [NeZero L] :
    Set.iUnion (fun q : Fin d → Fin L => quadCell q) = torusCube d := by
  ext x
  constructor
  · intro hx
    simp only [Set.mem_iUnion] at hx
    rcases hx with ⟨q, hq⟩
    exact quadCell_subset_cube q hq
  · intro hx
    change ∀ j ∈ Set.univ, x j ∈ Set.Ico (-Real.pi) Real.pi at hx
    classical
    let δ := quadStep L
    have hδ : 0 < δ := quadStep_pos L
    have hδL : δ * (L : ℝ) = 2 * Real.pi := quadStep_mul_L L
    have hcoord : ∀ j : Fin d, ∃ i : Fin L,
        x j ∈ Set.Ico (-Real.pi + δ * (i.val : ℝ))
          (-Real.pi + δ * (i.val : ℝ) + δ) := by
      intro j
      have hxj := hx j (Set.mem_univ _)
      let u := (x j + Real.pi) / δ
      have hu0 : 0 ≤ u := by
        dsimp [u]
        exact div_nonneg (by linarith [hxj.1]) hδ.le
      have huL : u < (L : ℝ) := by
        have : x j + Real.pi < 2 * Real.pi := by linarith [hxj.2]
        dsimp [u]
        rw [div_lt_iff₀ hδ]
        nlinarith [hδL]
      let n := ⌊u⌋₊
      have hn : n < L := (Nat.floor_lt' (NeZero.ne L)).2 huL
      refine ⟨⟨n, hn⟩, ?_⟩
      have hfloorlo : (n : ℝ) ≤ u := Nat.floor_le hu0
      have hfloorhi : u < (n : ℝ) + 1 := Nat.lt_floor_add_one u
      have hxu : x j = -Real.pi + δ * u := by
        dsimp [u]
        field_simp [ne_of_gt hδ]
        ring
      constructor
      · rw [hxu]
        gcongr
      · rw [hxu]
        have := mul_lt_mul_of_pos_left hfloorhi hδ
        linarith
    let q : Fin d → Fin L := fun j => Classical.choose (hcoord j)
    have hq : x ∈ quadCell q := by
      change ∀ j ∈ Set.univ, x j ∈ Set.Ico (quadCorner q j)
        (quadCorner q j + quadStep L)
      intro j _
      simpa [quadCorner, quadStep, q, δ] using Classical.choose_spec (hcoord j)
    exact Set.mem_iUnion.2 ⟨q, hq⟩

private lemma quadCell_pairwise {d L : ℕ} [NeZero L] :
    Set.Pairwise (Set.univ : Set (Fin d → Fin L))
      (fun q r => Disjoint (quadCell q) (quadCell r)) := by
  intro q _ r _ hqr
  rw [Set.disjoint_left]
  intro x hqx hrx
  have hdiff : ∃ j : Fin d, q j ≠ r j := by
    by_contra h
    push_neg at h
    exact hqr (funext h)
  obtain ⟨j, hj⟩ := hdiff
  have hqj := (Set.mem_pi.mp hqx) j (Set.mem_univ _)
  have hrj := (Set.mem_pi.mp hrx) j (Set.mem_univ _)
  have hδ : 0 < quadStep L := quadStep_pos L
  have hval : (q j).val < (r j).val ∨ (r j).val < (q j).val := by
    exact lt_or_gt_of_ne (by intro h; exact hj (Fin.ext h))
  rcases hval with hval | hval
  · have hsep : quadCorner q j + quadStep L ≤ quadCorner r j := by
      have hv : ((q j).val : ℝ) + 1 ≤ (r j).val := by exact_mod_cast Nat.succ_le_of_lt hval
      unfold quadCorner
      nlinarith [mul_le_mul_of_nonneg_left hv hδ.le]
    linarith [hqj.1, hqj.2, hrj.1, hrj.2]
  · have hsep : quadCorner r j + quadStep L ≤ quadCorner q j := by
      have hv : ((r j).val : ℝ) + 1 ≤ (q j).val := by exact_mod_cast Nat.succ_le_of_lt hval
      unfold quadCorner
      nlinarith [mul_le_mul_of_nonneg_left hv hδ.le]
    linarith [hqj.1, hqj.2, hrj.1, hrj.2]

private lemma quadCell_volume {d L : ℕ} [NeZero L] (q : Fin d → Fin L) :
    volume (quadCell q) = ENNReal.ofReal (quadStep L) ^ d := by
  change volume (Set.pi Set.univ fun j =>
    Set.Ico (quadCorner q j) (quadCorner q j + quadStep L)) = _
  rw [volume_pi_pi]
  simp_rw [Real.volume_Ico]
  have heq : ∀ j : Fin d,
      (quadCorner q j + quadStep L - quadCorner q j) = quadStep L := by
    intro j
    ring
  simp [heq, Finset.prod_const, Finset.card_univ]

private lemma quadCorner_dist_le {d L : ℕ} [NeZero L]
    {q : Fin d → Fin L} {x : Frequency d} (hx : x ∈ quadCell q) :
    dist (quadCorner q) x ≤ quadStep L := by
  apply (dist_pi_le_iff (quadStep_pos L).le).2
  intro j
  have hj := (Set.mem_pi.mp hx) j (Set.mem_univ _)
  rw [Real.dist_eq]
  rcases hj with ⟨hlo, hhi⟩
  calc
    |quadCorner q j - x j| = x j - quadCorner q j := by
      rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
      ring
    _ ≤ quadStep L := by linarith

private lemma integrableOn_cube {d : ℕ} (f : Frequency d → ℂ)
    (hf : Continuous f) : IntegrableOn f (torusCube d) volume := by
  have hc : IsCompact (Set.pi Set.univ (fun _ : Fin d => Set.Icc (-Real.pi) Real.pi)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hfi : IntegrableOn f
      (Set.pi Set.univ fun _ : Fin d => Set.Icc (-Real.pi) Real.pi) volume :=
    hf.continuousOn.integrableOn_compact (μ := volume) hc
  apply hfi.mono_set
  intro x hx
  change ∀ j ∈ Set.univ, x j ∈ Set.Ico (-Real.pi) Real.pi at hx
  change ∀ j ∈ Set.univ, x j ∈ Set.Icc (-Real.pi) Real.pi
  intro j _
  exact ⟨(hx j (Set.mem_univ _)).1,
    (hx j (Set.mem_univ _)).2.le⟩

private lemma centered_gridAngle_fun {d L : ℕ} [NeZero L] (hL : Even L)
    (q : Fin d → Fin L) :
    gridAngle (centeredTorusEquiv d L q) = quadCorner q := by
  funext j
  exact centered_gridAngle hL q j

private lemma centered_grid_sum {d L : ℕ} [NeZero L] (hL : Even L)
    (f : Frequency d → ℂ) :
    (∑ k : Torus d L, f (gridAngle k)) =
      ∑ q : Fin d → Fin L, f (quadCorner q) := by
  calc
    (∑ k : Torus d L, f (gridAngle k)) =
        ∑ q : Fin d → Fin L, f (gridAngle (centeredTorusEquiv d L q)) := by
      symm
      exact Equiv.sum_comp (centeredTorusEquiv d L) (fun k => f (gridAngle k))
    _ = ∑ q : Fin d → Fin L, f (quadCorner q) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [centered_gridAngle_fun hL]

private lemma quadCell_integral_error {d L : ℕ} [NeZero L]
    (f : Frequency d → ℂ) (K : ℝ≥0) (hf : LipschitzWith K f)
    (q : Fin d → Fin L) :
    ‖((quadStep L ^ d : ℝ) : ℂ) * f (quadCorner q) -
        ∫ x in quadCell q, f x‖ ≤
      (K : ℝ) * quadStep L * quadStep L ^ d := by
  have hδ : 0 < quadStep L := quadStep_pos L
  have hvol : (volume (quadCell q)).toReal = quadStep L ^ d := by
    rw [quadCell_volume]
    simp [ENNReal.toReal_ofReal, hδ.le]
  have hconst :
      ∫ x in quadCell q, (fun _ : Frequency d => f (quadCorner q)) x =
        (quadStep L ^ d : ℝ) • f (quadCorner q) := by
    rw [setIntegral_const]
    rw [← hvol]
    rfl
  have hfin : volume (quadCell q) < ∞ := by
    rw [quadCell_volume]
    finiteness
  have hbound : ∀ x ∈ quadCell q,
      ‖f (quadCorner q) - f x‖ ≤ (K : ℝ) * quadStep L := by
    intro x hx
    calc
      ‖f (quadCorner q) - f x‖ = dist (f (quadCorner q)) (f x) := by
        rw [dist_eq_norm]
      _ ≤ (K : ℝ) * dist (quadCorner q) x := hf.dist_le_mul _ _
      _ ≤ (K : ℝ) * quadStep L := by
        exact mul_le_mul_of_nonneg_left (quadCorner_dist_le hx) K.2
  have hnorm := norm_setIntegral_le_of_norm_le_const hfin hbound
  have hconstInt : IntegrableOn (fun _ : Frequency d => f (quadCorner q))
      (quadCell q) volume := by
    exact integrableOn_const (ne_of_lt hfin)
  have hconstC :
      ∫ x in quadCell q, (fun _ : Frequency d => f (quadCorner q)) x =
        ((quadStep L ^ d : ℝ) : ℂ) * f (quadCorner q) := by
    rw [hconst]
    simp [smul_eq_mul]
  calc
    _ = ‖∫ x in quadCell q, (f (quadCorner q) - f x)‖ := by
      rw [← hconstC, integral_sub hconstInt
        ((integrableOn_cube f hf.continuous).mono_set (quadCell_subset_cube q))]
    _ ≤ (K : ℝ) * quadStep L * (volume (quadCell q)).toReal := by
      simpa only [Measure.real_def, mul_assoc] using hnorm
    _ = (K : ℝ) * quadStep L * quadStep L ^ d := by rw [hvol]

private lemma torus_card_eq_pow {d L : ℕ} [NeZero L] : Fintype.card (Torus d L) = L ^ d := by
  simp [Torus, Fintype.card_pi_const]

theorem periodicGridQuadrature_proof : PeriodicGridQuadratureStatement := by
  intro d
  refine ⟨2 * Real.pi, mul_pos (by norm_num) Real.pi_pos, ?_⟩
  intro L instL hL4 hEven f K hf
  letI : NeZero L := instL
  let δ := quadStep L
  let α : ℝ := ((2 * Real.pi) ^ d)⁻¹
  have hδ : 0 < δ := quadStep_pos L
  have hα : 0 < α := by
    dsimp [α]
    positivity
  have hcard : Fintype.card (Torus d L) = L ^ d := torus_card_eq_pow
  have hcardQ : Fintype.card (Fin d → Fin L) = L ^ d := by
    simp [Fintype.card_pi_const]
  have hcoef : (Fintype.card (Torus d L) : ℝ)⁻¹ = α * δ ^ d := by
    rw [hcard]
    dsimp [α, δ, quadStep]
    have hLc : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
    rw [div_pow]
    field_simp [hLc, Real.pi_ne_zero]
    <;> ring_nf
    <;> norm_cast
  have hcoefC : (Fintype.card (Torus d L) : ℂ)⁻¹ =
      (α : ℂ) * (δ ^ d : ℂ) := by
    simpa using congrArg (fun x : ℝ => (x : ℂ)) hcoef
  have hcell : ∀ q : Fin d → Fin L, IntegrableOn f (quadCell q) volume := by
    intro q
    exact (integrableOn_cube f hf.continuous).mono_set (quadCell_subset_cube q)
  have hdisj : Pairwise (fun q r : Fin d → Fin L =>
      Disjoint (quadCell q) (quadCell r)) := by
    intro q r hqr
    exact quadCell_pairwise (Set.mem_univ q) (Set.mem_univ r) hqr
  have hsplit : ∫ x in torusCube d, f x =
      ∑ q : Fin d → Fin L, ∫ x in quadCell q, f x := by
    rw [← quadCell_union (d := d) (L := L)]
    exact integral_iUnion_fintype (fun q => quadCell_measurable q) hdisj hcell
  have hgrid : gridAvg (fun k : Torus d L => f (gridAngle k)) =
      (α : ℂ) * ∑ q : Fin d → Fin L, (δ ^ d : ℂ) * f (quadCorner q) := by
    unfold gridAvg
    rw [centered_grid_sum hEven f, hcoefC]
    calc
      _ = ∑ q : Fin d → Fin L, ((α : ℂ) * (δ ^ d : ℂ)) * f (quadCorner q) := by
        rw [Finset.mul_sum]
      _ = (α : ℂ) * ∑ q : Fin d → Fin L, (δ ^ d : ℂ) * f (quadCorner q) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring
  have halgebra :
      (α : ℂ) * (∑ q : Fin d → Fin L, (δ ^ d : ℂ) * f (quadCorner q)) -
          (α : ℂ) * (∑ q : Fin d → Fin L, ∫ x in quadCell q, f x) =
        (α : ℂ) * ∑ q : Fin d → Fin L,
          ((δ ^ d : ℂ) * f (quadCorner q) - ∫ x in quadCell q, f x) := by
    calc
      _ = (α : ℂ) * ((∑ q : Fin d → Fin L, (δ ^ d : ℂ) * f (quadCorner q)) -
          ∑ q : Fin d → Fin L, ∫ x in quadCell q, f x) := by ring
      _ = (α : ℂ) * ∑ q : Fin d → Fin L,
          ((δ ^ d : ℂ) * f (quadCorner q) - ∫ x in quadCell q, f x) := by
        congr 1
        exact (Finset.sum_sub_distrib (s := Finset.univ)
          (fun q : Fin d → Fin L => (δ ^ d : ℂ) * f (quadCorner q))
          (fun q => ∫ x in quadCell q, f x)).symm
  have hnormα : ‖(α : ℂ)‖ = α := by
    simp [abs_of_nonneg hα.le]
  have hsum_bound :
      ‖∑ q : Fin d → Fin L,
          ((δ ^ d : ℂ) * f (quadCorner q) - ∫ x in quadCell q, f x)‖ ≤
        ∑ q : Fin d → Fin L, ((K : ℝ) * δ * δ ^ d) := by
    calc
      _ ≤ ∑ q : Fin d → Fin L,
          ‖(δ ^ d : ℂ) * f (quadCorner q) - ∫ x in quadCell q, f x‖ := norm_sum_le _ _
      _ ≤ ∑ q : Fin d → Fin L, ((K : ℝ) * δ * δ ^ d) := by
        apply Finset.sum_le_sum
        intro q _
        simpa [δ] using quadCell_integral_error f K hf q
  have hsum_const :
      (∑ q : Fin d → Fin L, ((K : ℝ) * δ * δ ^ d)) =
        (L : ℝ) ^ d * ((K : ℝ) * δ * δ ^ d) := by
    simp [hcardQ]
  calc
    ‖gridAvg (fun k : Torus d L => f (gridAngle k)) -
        ((((2 * Real.pi) ^ d)⁻¹ : ℝ) : ℂ) * ∫ k in torusCube d, f k‖
        = ‖(α : ℂ) * ∑ q : Fin d → Fin L,
          ((δ ^ d : ℂ) * f (quadCorner q) - ∫ x in quadCell q, f x)‖ := by
          rw [hgrid, hsplit, halgebra]
    _ ≤ α * ∑ q : Fin d → Fin L, ((K : ℝ) * δ * δ ^ d) := by
          rw [norm_mul, hnormα]
          exact mul_le_mul_of_nonneg_left hsum_bound hα.le
    _ = (2 * Real.pi) * (K : ℝ) / (L : ℝ) := by
          rw [hsum_const]
          dsimp [α, δ, quadStep]
          have hLc : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
          rw [div_pow]
          field_simp [hLc, Real.pi_ne_zero]
          <;> ring_nf

end AndersonAC.S3
