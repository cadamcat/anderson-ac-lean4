import AndersonAC.S3.HelperStatements

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal
open AndersonAC.S3

attribute [local instance] Classical.propDecidable

namespace AndersonAC.S3H

/-- Centered integer representative of `v : ZMod L`: `val` if `2*val < L`, else `val - L`. -/
def centered (L : ℕ) (v : ZMod L) : ℤ :=
  if 2 * v.val < L then (v.val : ℤ) else (v.val : ℤ) - (L : ℤ)

/-- Max absolute centered coordinate, as a Nat. -/
def maxAbs (d L : ℕ) (ζ : Torus d L) : ℕ :=
  Finset.sup Finset.univ (fun j => (centered L (ζ j)).natAbs)

theorem centered_nonneg_of_lt {L : ℕ} (v : ZMod L) (h : 2 * v.val < L) :
    centered L v = (v.val : ℤ) := by
  unfold centered
  simp [h]

theorem centered_neg_of_not_lt {L : ℕ} (v : ZMod L) (h : ¬ 2 * v.val < L) :
    centered L v = (v.val : ℤ) - (L : ℤ) := by
  unfold centered
  simp [h]

theorem centered_eq_zero_iff {L : ℕ} [NeZero L] (v : ZMod L) :
    centered L v = 0 ↔ v = 0 := by
  constructor
  · intro h
    by_cases hb : 2 * v.val < L
    · rw [centered_nonneg_of_lt v hb] at h
      have hval : v.val = 0 := by exact_mod_cast h
      conv_lhs => rw [← ZMod.natCast_zmod_val v, hval]
      simp
    · rw [centered_neg_of_not_lt v hb] at h
      have hval : (v.val : ℤ) = (L : ℤ) := by omega
      have hL : v.val = L := by exact_mod_cast hval
      have hlt := ZMod.val_lt v
      omega
  · intro h
    subst h
    unfold centered
    have hval : (0 : ZMod L).val = 0 := ZMod.val_zero
    simp [hval]

theorem centered_injective {L : ℕ} [NeZero L] : Function.Injective (centered L) := by
  intro v w h
  unfold centered at h
  by_cases hv : 2 * v.val < L <;> by_cases hw : 2 * w.val < L
  · simp only [hv, hw, ↓reduceIte] at h
    have hval : v.val = w.val := by exact_mod_cast h
    exact ZMod.val_injective L hval
  · simp only [hv, hw, ↓reduceIte] at h
    have hvnn : (0 : ℤ) ≤ (v.val : ℤ) := Int.natCast_nonneg _
    have hwnn : (0 : ℤ) ≤ (w.val : ℤ) := Int.natCast_nonneg _
    have hLnn : (0 : ℤ) ≤ (L : ℤ) := Int.natCast_nonneg _
    have hlt_w : (w.val : ℤ) < (L : ℤ) := by
      exact_mod_cast ZMod.val_lt w
    omega
  · simp only [hv, hw, ↓reduceIte] at h
    have hvnn : (0 : ℤ) ≤ (v.val : ℤ) := Int.natCast_nonneg _
    have hwnn : (0 : ℤ) ≤ (w.val : ℤ) := Int.natCast_nonneg _
    have hlt_v : (v.val : ℤ) < (L : ℤ) := by
      exact_mod_cast ZMod.val_lt v
    omega
  · simp only [hv, hw, ↓reduceIte] at h
    have hval : (v.val : ℤ) = (w.val : ℤ) := by omega
    have hvaln : v.val = w.val := by exact_mod_cast hval
    exact ZMod.val_injective L hvaln

theorem centered_real_eq {L : ℕ} (v : ZMod L) :
    (centered L v : ℝ) =
      (if 2 * v.val < L then ((v.val : ℝ)) else ((v.val : ℝ)) - (L : ℝ)) := by
  unfold centered
  by_cases h : 2 * v.val < L
  · simp only [h, ↓reduceIte]
    norm_cast
  · simp only [h, ↓reduceIte]
    push_cast
    rfl

theorem gridAngle_eq {d L : ℕ} [NeZero L] (k : Torus d L) (j : Fin d) :
    gridAngle k j = 2 * Real.pi * ((centered L (k j) : ℤ) : ℝ) / (L : ℝ) := by
  unfold gridAngle
  rw [centered_real_eq]

theorem card_torus (d L : ℕ) [NeZero L] :
    Fintype.card (Torus d L) = L ^ d := by
  unfold Torus
  rw [Fintype.card_pi]
  simp [ZMod.card L]

theorem centered_natAbs_le {L : ℕ} [NeZero L] (v : ZMod L) :
    (centered L v).natAbs ≤ L := by
  by_cases h : 2 * v.val < L
  · rw [centered_nonneg_of_lt v h, Int.natAbs_natCast]
    exact le_of_lt (ZMod.val_lt v)
  · rw [centered_neg_of_not_lt v h]
    have hle : v.val ≤ L := le_of_lt (ZMod.val_lt v)
    have hsub : ((v.val : ℤ) - (L : ℤ)) = -(((L - v.val : ℕ) : ℤ)) := by
      rw [Nat.cast_sub hle]
      ring
    rw [hsub, Int.natAbs_neg, Int.natAbs_natCast]
    exact Nat.sub_le L v.val

theorem maxAbs_le {d L : ℕ} [NeZero L] (ζ : Torus d L) : maxAbs d L ζ ≤ L := by
  unfold maxAbs
  apply Finset.sup_le
  intro j _
  exact centered_natAbs_le (ζ j)

theorem maxAbs_eq_zero_iff {d L : ℕ} [NeZero L] (ζ : Torus d L) :
    maxAbs d L ζ = 0 ↔ ζ = 0 := by
  constructor
  · intro h
    funext j
    have hle : (centered L (ζ j)).natAbs ≤ maxAbs d L ζ :=
      Finset.le_sup (f := fun j => (centered L (ζ j)).natAbs) (Finset.mem_univ j)
    rw [h] at hle
    have hc : centered L (ζ j) = 0 := Int.natAbs_eq_zero.mp (Nat.le_zero.mp hle)
    have := (centered_eq_zero_iff (ζ j)).mp hc
    simp [this]
  · intro h
    subst h
    unfold maxAbs
    apply Finset.sup_eq_zero.mpr
    intro j _
    simp [(centered_eq_zero_iff _).mpr rfl]

theorem radius_sq_eq (d : ℕ) (k : Fin d → ℝ) :
    radius k ^ 2 = ∑ j, k j ^ 2 := by
  unfold radius
  rw [Real.sq_sqrt]
  apply Finset.sum_nonneg
  intro j _
  exact sq_nonneg _

theorem gridAngle_sq_sum {d L : ℕ} [NeZero L] (ζ : Torus d L) :
    ∑ j, (gridAngle ζ j) ^ 2 =
      (2 * Real.pi / (L : ℝ)) ^ 2 * ∑ j, (((centered L (ζ j) : ℤ) : ℝ)) ^ 2 := by
  have hL : (L : ℝ) ≠ 0 := by
    have : 0 < L := NeZero.pos L
    positivity
  simp_rw [gridAngle_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sum_centered_sq_ge_maxAbs_sq {d L : ℕ} [NeZero L] (ζ : Torus d L) :
    ((maxAbs d L ζ : ℕ) : ℝ) ^ 2 ≤ ∑ j, (((centered L (ζ j) : ℤ) : ℝ)) ^ 2 := by
  by_cases hd : d = 0
  · subst hd
    have hmax : maxAbs 0 L ζ = 0 := by
      unfold maxAbs
      simp
    rw [hmax]
    simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have huniv : (Finset.univ : Finset (Fin d)).Nonempty :=
      ⟨⟨0, hdpos⟩, Finset.mem_univ _⟩
    obtain ⟨j₀, _, hj₀⟩ := Finset.exists_mem_eq_sup Finset.univ huniv
      (fun j => (centered L (ζ j)).natAbs)
    -- hj₀ : sup = f j₀
    have hsup : maxAbs d L ζ = (centered L (ζ j₀)).natAbs := hj₀
    rw [hsup]
    have hcast : ((((centered L (ζ j₀)).natAbs : ℕ) : ℝ)) ^ 2 =
        ((((centered L (ζ j₀) : ℤ) : ℝ))) ^ 2 := by
      rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
    rw [hcast]
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun j => ((((centered L (ζ j) : ℤ) : ℝ))) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ j₀)

theorem radius_sq_centered {d L : ℕ} [NeZero L] (ζ : Torus d L) :
    radius (gridAngle ζ) ^ 2 =
      (2 * Real.pi / (L : ℝ)) ^ 2 * ∑ j, ((((centered L (ζ j) : ℤ) : ℝ))) ^ 2 := by
  rw [radius_sq_eq, gridAngle_sq_sum]

theorem term_le_of_ne_zero {d L : ℕ} [NeZero L] {ζ : Torus d L} (hne : ζ ≠ 0) :
    ((radius (gridAngle ζ) ^ 2))⁻¹ ≤
      ((L : ℝ) / (2 * Real.pi)) ^ 2 * ((((maxAbs d L ζ : ℕ) : ℝ)) ^ 2)⁻¹ := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    have : 0 < L := NeZero.pos L
    positivity
  have hMpos : (0 : ℝ) < ((maxAbs d L ζ : ℕ) : ℝ) := by
    have hneM : maxAbs d L ζ ≠ 0 := by
      intro h0
      exact hne ((maxAbs_eq_zero_iff ζ).mp h0)
    exact_mod_cast Nat.pos_of_ne_zero hneM
  have hSum_ge : ((((maxAbs d L ζ : ℕ) : ℝ)) ^ 2) ≤
      ∑ j, ((((centered L (ζ j) : ℤ) : ℝ))) ^ 2 :=
    sum_centered_sq_ge_maxAbs_sq ζ
  have hSum_pos : (0 : ℝ) < ∑ j, ((((centered L (ζ j) : ℤ) : ℝ))) ^ 2 := by
    calc (0 : ℝ) < ((((maxAbs d L ζ : ℕ) : ℝ)) ^ 2) := by positivity
    _ ≤ _ := hSum_ge
  have hrad := radius_sq_centered ζ
  rw [hrad, mul_inv]
  have h1 : (((2 * Real.pi / (L : ℝ)) ^ 2))⁻¹ =
      (((L : ℝ) / (2 * Real.pi)) ^ 2) := by
    rw [← inv_pow, inv_div]
  rw [h1]
  have hM2pos : (0 : ℝ) < ((((maxAbs d L ζ : ℕ) : ℝ)) ^ 2) := by positivity
  have hCpos : (0 : ℝ) ≤ ((((L : ℝ) / (2 * Real.pi)) ^ 2)) := by positivity
  exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ hSum_pos hM2pos).mpr hSum_ge) hCpos

/-- Preimage of `|·| ≤ j` has at most `2j+1` elements. -/
theorem card_preimage_le (L j : ℕ) [NeZero L] :
    (Finset.univ.filter (fun v : ZMod L => (centered L v).natAbs ≤ j)).card ≤ 2 * j + 1 := by
  have hmaps : Set.MapsTo (centered L)
      ↑(Finset.univ.filter (fun v : ZMod L => (centered L v).natAbs ≤ j))
      ↑(Finset.Icc (-(j : ℤ)) (j : ℤ)) := by
    intro v hv
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hv
    simp only [Finset.coe_Icc, Set.mem_setOf_eq]
    have hle : (centered L v).natAbs ≤ j := hv
    have hmem := (by omega : -(j : ℤ) ≤ centered L v ∧ centered L v ≤ (j : ℤ))
    exact ⟨hmem.1, hmem.2⟩
  have hinj : Set.InjOn (centered L)
      ↑(Finset.univ.filter (fun v : ZMod L => (centered L v).natAbs ≤ j)) :=
    centered_injective.injOn
  have hle := Finset.card_le_card_of_injOn (centered L) hmaps hinj
  have hcard : (Finset.Icc (-(j : ℤ)) (j : ℤ)).card = 2 * j + 1 := by
    rw [Int.card_Icc]
    have heq : (j : ℤ) + 1 - (-(j : ℤ)) = ((2 * j + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [heq, Int.toNat_natCast]
  rw [hcard] at hle
  exact hle

/-- Preimage of `|·| = j` has at most 2 elements. -/
theorem card_preimage_eq (L j : ℕ) [NeZero L] :
    (Finset.univ.filter (fun v : ZMod L => (centered L v).natAbs = j)).card ≤ 2 := by
  have hmaps : Set.MapsTo (centered L)
      ↑(Finset.univ.filter (fun v : ZMod L => (centered L v).natAbs = j))
      ↑({(j : ℤ), (-(j : ℤ))} : Finset ℤ) := by
    intro v hv
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hv
    have heq : (centered L v).natAbs = j := hv
    have hmem : centered L v = (j : ℤ) ∨ centered L v = -((j : ℤ)) :=
      Int.natAbs_eq_iff.mp heq
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    exact hmem
  have hinj : Set.InjOn (centered L)
      ↑(Finset.univ.filter (fun v : ZMod L => (centered L v).natAbs = j)) :=
    centered_injective.injOn
  have hle := Finset.card_le_card_of_injOn (centered L) hmaps hinj
  have hcard : ({(j : ℤ), (-(j : ℤ))} : Finset ℤ).card ≤ 2 := by
    calc ({(j : ℤ), (-(j : ℤ))} : Finset ℤ).card
        ≤ ({(-(j : ℤ))} : Finset ℤ).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  exact hle.trans hcard

/-- Level set `{ζ : maxAbs = j}` for `j ≥ 1` has at most `2d(2j+1)^{d-1}` elements. -/
theorem card_level_le (d L j : ℕ) [NeZero L] (hj : 1 ≤ j) :
    (Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ = j)).card ≤
      2 * d * (2 * j + 1) ^ (d - 1) := by
  by_cases hd : d = 0
  · subst hd
    have hempty : Finset.univ.filter (fun ζ : Torus 0 L => maxAbs 0 L ζ = j) = ∅ := by
      apply Finset.filter_false_of_mem
      intro ζ _ hmem
      have h0 : maxAbs 0 L ζ = 0 := by unfold maxAbs; simp
      omega
    rw [hempty]
    simp
  · -- d ≥ 1: union bound over attaining coordinate
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    -- per-coordinate finsets
    let Ple : Finset (ZMod L) :=
      Finset.univ.filter (fun v => (centered L v).natAbs ≤ j)
    let Peq : Finset (ZMod L) :=
      Finset.univ.filter (fun v => (centered L v).natAbs = j)
    have hPle : Ple.card ≤ 2 * j + 1 := card_preimage_le L j
    have hPeq : Peq.card ≤ 2 := card_preimage_eq L j
    -- pi finsets per attaining coordinate
    have hsub : Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ = j) ⊆
        Finset.univ.biUnion (fun i : Fin d =>
          Fintype.piFinset (fun k => if k = i then Peq else Ple)) := by
      intro ζ hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      have hmax_eq : maxAbs d L ζ = j := hmem
      have hle_all : ∀ k, (centered L (ζ k)).natAbs ≤ j := by
        intro k
        have hle : (centered L (ζ k)).natAbs ≤ maxAbs d L ζ :=
          Finset.le_sup (f := fun k => (centered L (ζ k)).natAbs) (Finset.mem_univ k)
        omega
      have huniv : (Finset.univ : Finset (Fin d)).Nonempty :=
        ⟨⟨0, hdpos⟩, Finset.mem_univ _⟩
      obtain ⟨i₀, _, hi₀⟩ := Finset.exists_mem_eq_sup Finset.univ huniv
        (fun k => (centered L (ζ k)).natAbs)
      have hi_eq : (centered L (ζ i₀)).natAbs = j := by
        have hsup : maxAbs d L ζ = (centered L (ζ i₀)).natAbs := hi₀
        omega
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      refine ⟨i₀, ?_⟩
      rw [Fintype.mem_piFinset]
      intro k
      by_cases hk : k = i₀
      · rw [hk]
        simp only [ite_true]
        show ζ i₀ ∈ Peq
        simp only [Peq, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hi_eq
      · simp only [hk, ite_false]
        show ζ k ∈ Ple
        simp only [Ple, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hle_all k
    have hcard_le := Finset.card_le_card hsub
    have hbi_le := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin d)))
      (t := fun i : Fin d => Fintype.piFinset (fun k => if k = i then Peq else Ple))
    have hsum_eq : ∑ i : Fin d,
          (Fintype.piFinset (fun k => if k = i then Peq else Ple)).card =
        d * (Peq.card * Ple.card ^ (d - 1)) := by
      have hpi : ∀ i : Fin d,
          (Fintype.piFinset (fun k => if k = i then Peq else Ple)).card =
            Peq.card * Ple.card ^ (d - 1) := by
        intro i
        rw [Fintype.card_piFinset]
        have hcard_if : ∀ k : Fin d,
            ((if k = i then Peq else Ple : Finset (ZMod L)).card) =
              (if k = i then Peq.card else Ple.card) := by
          intro k
          by_cases hk : k = i <;> simp [hk]
        rw [Finset.prod_congr rfl (fun k _ => hcard_if k)]
        have hprod : ∏ k : Fin d, (if k = i then Peq.card else Ple.card) =
            Peq.card * Ple.card ^ (d - 1) := by
          have h1 : (∏ k : Fin d, (if k = i then Peq.card else Ple.card)) =
              Peq.card *
                ∏ k ∈ Finset.univ.erase i, (if k = i then Peq.card else Ple.card) := by
            rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
            simp
          rw [h1]
          have h2 : ∏ k ∈ Finset.univ.erase i,
                (if k = i then Peq.card else Ple.card) =
              Ple.card ^ (d - 1) := by
            have herase : ∀ k ∈ Finset.univ.erase i,
                (if k = i then Peq.card else Ple.card) = Ple.card := by
              intro k hk
              simp only [Finset.mem_erase] at hk
              simp [hk.1]
            rw [Finset.prod_congr rfl herase]
            rw [Finset.prod_const]
            have hcard_erase : (Finset.univ.erase i).card = d - 1 := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
              simp [Fintype.card_fin]
            rw [hcard_erase]
          rw [h2]
        exact hprod
      calc ∑ i : Fin d, (Fintype.piFinset (fun k => if k = i then Peq else Ple)).card
          = ∑ i : Fin d, (Peq.card * Ple.card ^ (d - 1)) :=
            Finset.sum_congr rfl (fun i _ => hpi i)
        _ = d * (Peq.card * Ple.card ^ (d - 1)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            ring
    have hmid : Peq.card * Ple.card ^ (d - 1) ≤ 2 * (2 * j + 1) ^ (d - 1) :=
      Nat.mul_le_mul hPeq (Nat.pow_le_pow_left hPle (d - 1))
    calc (Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ = j)).card
        ≤ (Finset.univ.biUnion (fun i : Fin d =>
            Fintype.piFinset (fun k => if k = i then Peq else Ple))).card :=
          hcard_le
      _ ≤ ∑ i : Fin d, (Fintype.piFinset (fun k => if k = i then Peq else Ple)).card :=
          hbi_le
      _ = d * (Peq.card * Ple.card ^ (d - 1)) := hsum_eq
      _ ≤ d * (2 * (2 * j + 1) ^ (d - 1)) :=
          Nat.mul_le_mul (Nat.le_refl d) hmid
      _ = 2 * d * (2 * j + 1) ^ (d - 1) := by ring

/-- The frequency sum is bounded uniformly in `L` for `d ≥ 3`. -/
theorem frequencySum_aux : FrequencySumStatement := by
  intro d hd
  -- C = d * 3^(d-1) / (2 * π^2)
  refine ⟨(d : ℝ) * (3 : ℝ) ^ (d - 1) / (2 * Real.pi ^ 2), by positivity, fun L _ hL => ?_⟩
  have hd3 : 3 ≤ d := hd
  have hdpos : 0 < d := by omega
  have hL4 : 4 ≤ L := hL
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    have : 0 < L := by omega
    positivity
  have hPipos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hNpos : (0 : ℝ) < ((Fintype.card (Torus d L) : ℕ) : ℝ) := by
    rw [card_torus]
    positivity
  have hNne : ((Fintype.card (Torus d L) : ℕ) : ℝ) ≠ 0 := ne_of_gt hNpos
  -- unfold gridAvgReal
  unfold gridAvgReal
  -- it suffices to bound the sum by C * N
  have hN : ((Fintype.card (Torus d L) : ℕ) : ℝ) = (L : ℝ) ^ d := by
    rw [card_torus, Nat.cast_pow]
  -- per-frequency bound
  have hterm : ∀ ζ : Torus d L,
      (if ζ = 0 then (0 : ℝ) else ((radius (gridAngle ζ) ^ 2))⁻¹) ≤
        ((L : ℝ) / (2 * Real.pi)) ^ 2 * (((((maxAbs d L ζ : ℕ) : ℝ)) ^ 2))⁻¹ := by
    intro ζ
    by_cases hζ : ζ = 0
    · simp [hζ]
      positivity
    · simp only [hζ, ↓reduceIte]
      exact term_le_of_ne_zero hζ
  have hsum_le : ∑ ζ : Torus d L,
        (if ζ = 0 then (0 : ℝ) else ((radius (gridAngle ζ) ^ 2))⁻¹) ≤
        ((L : ℝ) / (2 * Real.pi)) ^ 2 *
          ∑ ζ : Torus d L, (((((maxAbs d L ζ : ℕ) : ℝ)) ^ 2))⁻¹ := by
    calc ∑ ζ : Torus d L, (if ζ = 0 then (0:ℝ) else _) ≤
            ∑ ζ : Torus d L, (((L:ℝ)/(2*Real.pi))^2 * (((maxAbs d L ζ:ℕ):ℝ)^2)⁻¹) :=
          Finset.sum_le_sum (fun ζ _ => hterm ζ)
      _ = ((L:ℝ)/(2*Real.pi))^2 * ∑ ζ : Torus d L, (((maxAbs d L ζ:ℕ):ℝ)^2)⁻¹ := by
          rw [Finset.mul_sum]
  -- fiber over maxAbs values in Icc 0 L
  have hmem : ∀ ζ ∈ (Finset.univ : Finset (Torus d L)),
      maxAbs d L ζ ∈ Finset.Icc 0 L := by
    intro ζ _
    simp only [Finset.mem_Icc]
    exact ⟨Nat.zero_le _, maxAbs_le ζ⟩
  have hfib := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Torus d L)))
    (t := Finset.Icc 0 L) (g := maxAbs d L) hmem
    (f := fun ζ : Torus d L => (((((maxAbs d L ζ : ℕ) : ℝ)) ^ 2))⁻¹)
  -- hfib : Σ j∈Icc, Σ ζ∈univ with maxAbs=j, ... = Σ ζ, ...
  have hsum_fib : ∑ ζ : Torus d L, (((((maxAbs d L ζ : ℕ) : ℝ)) ^ 2))⁻¹ =
      ∑ j ∈ Finset.Icc 0 L,
        ∑ ζ ∈ Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ = j),
          (((((maxAbs d L ζ : ℕ) : ℝ)) ^ 2))⁻¹ := by
    have := hfib
    simp only [Finset.sum_filter] at this ⊢
    -- `∑ i with g i = j` is notation for filter; need to match
    exact this.symm
  -- each fiber sum = card * j^{-2}
  have hfib_eq : ∀ j ∈ Finset.Icc 0 L,
      (∑ ζ ∈ Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ = j),
        (((((maxAbs d L ζ : ℕ) : ℝ)) ^ 2))⁻¹) =
        ((Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ = j)).card : ℝ) *
          ((((j : ℕ) : ℝ)) ^ 2)⁻¹ := by
    intro j _
    have heq : ∀ ζ ∈ Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ = j),
        (((((maxAbs d L ζ : ℕ) : ℝ)) ^ 2))⁻¹ = ((((j : ℕ) : ℝ)) ^ 2)⁻¹ := by
      intro ζ hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      rw [hmem]
    rw [Finset.sum_congr rfl (fun ζ hmem => heq ζ hmem)]
    rw [Finset.sum_const, nsmul_eq_mul]
  -- bound fiber sums for j ≥ 1; j = 0 contributes 0
  have hbound : ∀ j ∈ Finset.Icc 0 L,
      ((Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ = j)).card : ℝ) *
        ((((j : ℕ) : ℝ)) ^ 2)⁻¹ ≤
        (2 * d * (2 * j + 1) ^ (d - 1) : ℕ) *
          ((((j : ℕ) : ℝ)) ^ 2)⁻¹ := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    by_cases hj0 : j = 0
    · subst hj0
      simp
    · have hj1 : 1 ≤ j := Nat.pos_of_ne_zero hj0
      have hcard : (Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ = j)).card ≤
          2 * d * (2 * j + 1) ^ (d - 1) := card_level_le d L j hj1
      have hpos : (0:ℝ) ≤ ((((j:ℕ):ℝ))^2)⁻¹ := by positivity
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hpos
  -- sum over j of bounds ≤ 2d*3^{d-1}*L^{d-2} (as Real)
  have hsum_bound : ∑ j ∈ Finset.Icc 0 L,
        ((Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ = j)).card : ℝ) *
          ((((j : ℕ) : ℝ)) ^ 2)⁻¹ ≤
        2 * (d:ℝ) * (3:ℝ)^(d-1) * (L:ℝ)^(d-2) := by
    have hsub_Icc : Finset.Icc 1 L ⊆ Finset.Icc 0 L := by
      intro j hj
      simp only [Finset.mem_Icc] at hj ⊢
      omega
    have hzero_out : ∀ x ∈ Finset.Icc 0 L, x ∉ Finset.Icc 1 L →
        ((Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ = x)).card : ℝ) *
          ((((x : ℕ) : ℝ)) ^ 2)⁻¹ = 0 := by
      intro x hx hx1
      simp only [Finset.mem_Icc] at hx hx1
      have hx0 : x = 0 := by omega
      subst hx0
      simp
    have h_eq : ∑ j ∈ Finset.Icc 1 L,
          ((Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ = j)).card : ℝ) *
            ((((j : ℕ) : ℝ)) ^ 2)⁻¹ =
          ∑ j ∈ Finset.Icc 0 L,
          ((Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ = j)).card : ℝ) *
            ((((j : ℕ) : ℝ)) ^ 2)⁻¹ :=
      Finset.sum_subset hsub_Icc hzero_out
    rw [← h_eq]
    calc ∑ j ∈ Finset.Icc 1 L, ((Finset.univ.filter _).card : ℝ) * ((((j:ℕ):ℝ))^2)⁻¹
        ≤ ∑ j ∈ Finset.Icc 1 L, (2 * d * (2 * j + 1) ^ (d - 1) : ℕ) *
            ((((j:ℕ):ℝ))^2)⁻¹ := by
          apply Finset.sum_le_sum
          intro j hj
          have hj0 : j ∈ Finset.Icc 0 L := hsub_Icc hj
          exact hbound j hj0
      _ ≤ ∑ j ∈ Finset.Icc 1 L, (2 * (d:ℝ) * (3:ℝ)^(d-1) * (L:ℝ)^(d-3)) := by
          apply Finset.sum_le_sum
          intro j hj
          simp only [Finset.mem_Icc] at hj
          have hj1 : 1 ≤ j := hj.1
          have hjL : j ≤ L := hj.2
          have hjpos : (0:ℝ) < ((j:ℕ):ℝ) := by exact_mod_cast hj1
          have h2j1 : ((2 * j + 1 : ℕ):ℝ) ≤ 3 * ((j:ℕ):ℝ) := by
            have h1 : (1:ℝ) ≤ ((j:ℕ):ℝ) := by exact_mod_cast hj1
            push_cast
            linarith
          have hpow : ((((2 * j + 1 : ℕ)):ℝ))^(d-1) ≤ (3 * ((j:ℕ):ℝ))^(d-1) := by
            apply pow_le_pow_left₀ (by positivity) h2j1
          have hpow3 : (3 * ((j:ℕ):ℝ))^(d-1) = (3:ℝ)^(d-1) * ((j:ℕ):ℝ)^(d-1) := by
            rw [mul_pow]
          have hd_sub : d - 1 = (d - 3) + 2 := by omega
          have hj_pow : ((((j:ℕ):ℝ)))^(d-1) * ((((j:ℕ):ℝ))^2)⁻¹ =
              ((((j:ℕ):ℝ)))^(d-3) := by
            rw [hd_sub, pow_add]
            have hne : ((((j:ℕ):ℝ))^2) ≠ 0 := by positivity
            field_simp
          have hj_le_L : ((((j:ℕ):ℝ)))^(d-3) ≤ ((((L:ℕ):ℝ)))^(d-3) := by
            apply pow_le_pow_left₀ (by positivity) _ (d-3)
            exact_mod_cast hjL
          have hA_le_C : ((((2*j+1:ℕ)):ℝ))^(d-1) ≤
              (3:ℝ)^(d-1) * ((j:ℕ):ℝ)^(d-1) := hpow3 ▸ hpow
          calc ((2 * d * (2 * j + 1) ^ (d - 1) : ℕ):ℝ) * ((((j:ℕ):ℝ))^2)⁻¹
              = 2 * (d:ℝ) * ((((2*j+1:ℕ)):ℝ)^(d-1)) * ((((j:ℕ):ℝ))^2)⁻¹ := by
                push_cast
                ring
            _ ≤ 2 * (d:ℝ) * ((3:ℝ)^(d-1) * ((j:ℕ):ℝ)^(d-1)) * ((((j:ℕ):ℝ))^2)⁻¹ := by
                have hnn : (0:ℝ) ≤ 2 * (d:ℝ) * ((((j:ℕ):ℝ))^2)⁻¹ := by positivity
                have := mul_le_mul_of_nonneg_left hA_le_C hnn
                linarith [this]
            _ = 2 * (d:ℝ) * (3:ℝ)^(d-1) * ((((j:ℕ):ℝ))^(d-3)) := by
                have : 2 * (d:ℝ) * ((3:ℝ)^(d-1) * ((j:ℕ):ℝ)^(d-1)) *
                    ((((j:ℕ):ℝ))^2)⁻¹ =
                    2 * (d:ℝ) * (3:ℝ)^(d-1) *
                      (((((j:ℕ):ℝ))^(d-1)) * ((((j:ℕ):ℝ))^2)⁻¹) := by ring
                rw [this, hj_pow]
            _ ≤ 2 * (d:ℝ) * (3:ℝ)^(d-1) * ((((L:ℕ):ℝ)))^(d-3) := by
                gcongr
      _ = 2 * (d:ℝ) * (3:ℝ)^(d-1) * (L:ℝ)^(d-2) := by
          have hcard : (Finset.Icc 1 L).card = L := by
            rw [Nat.card_Icc]
            omega
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
          have hd_sub2 : d - 2 = 1 + (d - 3) := by omega
          have hLpow : (L:ℝ)^(d-2) = (L:ℝ) * (L:ℝ)^(d-3) := by
            rw [hd_sub2, pow_add, pow_one]
          rw [hLpow]
          ring
  -- combine
  have hfinal_sum : ∑ ζ : Torus d L, (((((maxAbs d L ζ : ℕ) : ℝ)) ^ 2))⁻¹ ≤
      2 * (d:ℝ) * (3:ℝ)^(d-1) * (L:ℝ)^(d-2) := by
    rw [hsum_fib]
    calc ∑ j ∈ Finset.Icc 0 L, ∑ ζ ∈ Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ = j),
            (((((maxAbs d L ζ : ℕ) : ℝ)) ^ 2))⁻¹
        = ∑ j ∈ Finset.Icc 0 L, ((Finset.univ.filter _).card : ℝ) * ((((j:ℕ):ℝ))^2)⁻¹ := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hfib_eq j hj
      _ ≤ _ := hsum_bound
  have hC_mul : ((L:ℝ)/(2*Real.pi))^2 * (2 * (d:ℝ) * (3:ℝ)^(d-1) * (L:ℝ)^(d-2)) =
      ((d:ℝ) * (3:ℝ)^(d-1) / (2 * Real.pi^2)) * (L:ℝ)^d := by
    have hd_eq : d = (d - 2) + 2 := by omega
    have hLpow : (L:ℝ)^d = (L:ℝ)^(d-2) * (L:ℝ)^2 := by
      conv_lhs => rw [hd_eq, pow_add]
    rw [hLpow]
    field_simp
  have hsum_term_le : ∑ ζ : Torus d L,
        (if ζ = 0 then (0:ℝ) else ((radius (gridAngle ζ)^2))⁻¹) ≤
        ((d:ℝ) * (3:ℝ)^(d-1) / (2 * Real.pi^2)) * (L:ℝ)^d := by
    calc ∑ ζ : Torus d L, (if ζ = 0 then (0:ℝ) else _) ≤
            ((L:ℝ)/(2*Real.pi))^2 * ∑ ζ : Torus d L, (((maxAbs d L ζ:ℕ):ℝ)^2)⁻¹ :=
          hsum_le
      _ ≤ ((L:ℝ)/(2*Real.pi))^2 * (2 * (d:ℝ) * (3:ℝ)^(d-1) * (L:ℝ)^(d-2)) := by
          gcongr
      _ = _ := hC_mul
  -- divide by N
  calc ((Fintype.card (Torus d L):ℝ))⁻¹ *
          ∑ ζ : Torus d L, (if ζ = 0 then (0:ℝ) else _) ≤
        ((Fintype.card (Torus d L):ℝ))⁻¹ *
          (((d:ℝ) * (3:ℝ)^(d-1) / (2 * Real.pi^2)) * (L:ℝ)^d) := by
          gcongr
    _ = (d:ℝ) * (3:ℝ)^(d-1) / (2 * Real.pi^2) := by
        rw [hN]
        field_simp

/-- Grid spacing `S = 2π/L`. -/
def quadS (L : ℕ) : ℝ := 2 * Real.pi / (L : ℝ)

/-- Grid cell `gridAngle k + [0,S)^d`. -/
def quadCell (d L : ℕ) [NeZero L] (k : Torus d L) : Set (Fin d → ℝ) :=
  Set.pi Set.univ (fun j => Set.Ico (gridAngle k j) (gridAngle k j + quadS L))

/-- Minimal centered value `j_min = -(L/2)` (Nat division). -/
def jMin (L : ℕ) : ℤ := -(((L / 2 : ℕ) : ℤ))

theorem quadS_pos {L : ℕ} [NeZero L] : 0 < quadS L := by
  unfold quadS
  have hL : (0:ℝ) < (L:ℝ) := by
    have : 0 < L := NeZero.pos L
    positivity
  positivity

theorem gridAngle_eq_quadS {d L : ℕ} [NeZero L] (k : Torus d L) (j : Fin d) :
    gridAngle k j = quadS L * (((centered L (k j) : ℤ) : ℝ)) := by
  rw [gridAngle_eq]
  unfold quadS
  ring

theorem L_mul_quadS {L : ℕ} [NeZero L] : (L : ℝ) * quadS L = 2 * Real.pi := by
  unfold quadS
  have hL : (L:ℝ) ≠ 0 := by
    have : 0 < L := NeZero.pos L
    positivity
  field_simp

theorem floor_half_ge_one {L : ℕ} (hL : 4 ≤ L) : 1 ≤ L / 2 := by omega

theorem two_mul_half_ge {L : ℕ} : L - 1 ≤ 2 * (L / 2) := by
  have hmod : L % 2 < 2 := Nat.mod_lt _ (by omega)
  have heq := (Nat.div_add_mod L 2).symm
  omega

theorem two_mul_half_le {L : ℕ} : 2 * (L / 2) ≤ L := by omega

-- A = S * j_min ≤ -2 for L ≥ 4
theorem A_le_neg2 {L : ℕ} [NeZero L] (hL : 4 ≤ L) :
    quadS L * (((jMin L : ℤ)):ℝ) ≤ -2 := by
  have hpi3 : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hLposR : (0:ℝ) < (L:ℝ) := by
    have : 0 < L := NeZero.pos L
    positivity
  have hfloor1 : (1:ℝ) ≤ ((L/2 : ℕ):ℝ) := by
    have : 1 ≤ L / 2 := floor_half_ge_one hL
    exact_mod_cast this
  have h2floor : (L:ℝ) - 1 ≤ 2 * ((L/2:ℕ):ℝ) := by
    have hnat : L - 1 ≤ 2 * (L / 2) := by
      have h1 : 2 * (L / 2) + 1 ≥ L := by
        have hmod : L % 2 < 2 := Nat.mod_lt _ (by omega)
        have heq := (Nat.div_add_mod L 2).symm
        omega
      omega
    -- `Nat.cast_le` preserves ≤
    have hcast : ((L - 1 : ℕ):ℝ) ≤ ((2 * (L/2) : ℕ):ℝ) := by exact_mod_cast hnat
    push_cast at hcast ⊢
    have hL4 : (4:ℕ) ≤ L := hL
    -- (L-1 :ℕ) cast = (L:ℝ)-1 for L≥1
    have hsub : (((L - 1 : ℕ)):ℝ) = (L:ℝ) - 1 := by
      have h1L : 1 ≤ L := by omega
      rw [Nat.cast_sub h1L]
      simp
    linarith [hcast, hsub]
  have h3floor : (L:ℝ) ≤ 3 * ((L/2:ℕ):ℝ) := by
    linarith [h2floor, hfloor1]
  have hpi_floor : (L:ℝ) ≤ Real.pi * ((L/2:ℕ):ℝ) := by
    have h3le : (3:ℝ) ≤ Real.pi := le_of_lt hpi3
    have hnonneg : (0:ℝ) ≤ ((L/2:ℕ):ℝ) := by positivity
    calc (L:ℝ) ≤ 3 * ((L/2:ℕ):ℝ) := h3floor
      _ ≤ Real.pi * ((L/2:ℕ):ℝ) :=
        mul_le_mul_of_nonneg_right h3le hnonneg
  have h2pi_floor : 2 * (L:ℝ) ≤ 2 * Real.pi * ((L/2:ℕ):ℝ) := by
    linarith [hpi_floor]
  have hle_div : (2:ℝ) ≤ 2 * Real.pi * ((L/2:ℕ):ℝ) / (L:ℝ) := by
    rw [le_div_iff₀ hLposR]
    linarith [h2pi_floor]
  have hJ : (((jMin L : ℤ)):ℝ) = -(((L/2 : ℕ)):ℝ) := by unfold jMin; push_cast; rfl
  have hAeq : quadS L * (((jMin L : ℤ)):ℝ) = -(2 * Real.pi * ((L/2:ℕ):ℝ) / (L:ℝ)) := by
    rw [hJ]
    unfold quadS
    field_simp
  linarith [hle_div, hAeq]

-- A + 2π > 2 for L ≥ 4
theorem A_add_2pi_gt2 {L : ℕ} [NeZero L] (hL : 4 ≤ L) :
    2 < quadS L * (((jMin L : ℤ)):ℝ) + 2 * Real.pi := by
  have hpi3 : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hLposR : (0:ℝ) < (L:ℝ) := by
    have : 0 < L := NeZero.pos L
    positivity
  have h2floor_le : 2 * (L / 2) ≤ L := two_mul_half_le
  have h2floorR : 2 * ((L/2:ℕ):ℝ) ≤ (L:ℝ) := by exact_mod_cast h2floor_le
  have hLsub_nonneg : (0:ℝ) ≤ (L:ℝ) - ((L/2:ℕ):ℝ) := by linarith [h2floorR]
  have hLsub_gt : (0:ℝ) < (L:ℝ) - ((L/2:ℕ):ℝ) := by
    have hlt : ((L/2:ℕ):ℝ) < (L:ℝ) := by
      have hle : 2 * (L / 2) ≤ L := h2floor_le
      have h1L : 1 ≤ L := by omega
      have hcast : ((2 * (L/2) : ℕ):ℝ) ≤ (L:ℝ) := by exact_mod_cast hle
      push_cast at hcast
      linarith [hcast, hLposR]
    linarith
  have h3sub : (L:ℝ) ≤ 3 * ((L:ℝ) - ((L/2:ℕ):ℝ)) := by
    linarith [h2floorR]
  have hpi_sub : (L:ℝ) < Real.pi * ((L:ℝ) - ((L/2:ℕ):ℝ)) := by
    have h3lt : (3:ℝ) < Real.pi := hpi3
    calc (L:ℝ) ≤ 3 * ((L:ℝ) - ((L/2:ℕ):ℝ)) := h3sub
      _ < Real.pi * ((L:ℝ) - ((L/2:ℕ):ℝ)) :=
        mul_lt_mul_of_pos_right h3lt hLsub_gt
  have h2pi_sub : 2 * (L:ℝ) < 2 * Real.pi * ((L:ℝ) - ((L/2:ℕ):ℝ)) := by linarith [hpi_sub]
  have hgt_div : (2:ℝ) < 2 * Real.pi * ((L:ℝ) - ((L/2:ℕ):ℝ)) / (L:ℝ) := by
    rw [lt_div_iff₀ hLposR]
    linarith [h2pi_sub]
  have hJ : (((jMin L : ℤ)):ℝ) = -(((L/2 : ℕ)):ℝ) := by unfold jMin; push_cast; rfl
  have hAeq : quadS L * (((jMin L : ℤ)):ℝ) + 2 * Real.pi =
      2 * Real.pi * ((L:ℝ) - ((L/2:ℕ):ℝ)) / (L:ℝ) := by
    rw [hJ]
    unfold quadS
    have hLne : (L:ℝ) ≠ 0 := ne_of_gt hLposR
    field_simp
    ring
  linarith [hgt_div, hAeq]

theorem centered_bounds {L : ℕ} [NeZero L] (v : ZMod L) :
    jMin L ≤ centered L v ∧ centered L v < jMin L + (L : ℤ) := by
  have hv := ZMod.val_lt v
  have hm := Nat.mod_lt L (by omega : 0 < 2)
  have hd := Nat.div_add_mod L 2
  unfold centered jMin
  split_ifs <;> omega

theorem exists_centered {L : ℕ} [NeZero L] (n : ℤ)
    (hn : jMin L ≤ n ∧ n < jMin L + (L : ℤ)) :
    ∃ v : ZMod L, centered L v = n := by
  have hs : Finset.image (centered L) Finset.univ ⊆
      Finset.Ico (jMin L) (jMin L + (L : ℤ)) := by
    intro x hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Ico.mpr (centered_bounds v)
  have hc : (Finset.image (centered L) Finset.univ).card = L := by
    rw [Finset.card_image_of_injective _ centered_injective]
    simp [ZMod.card L]
  have ht : (Finset.Ico (jMin L) (jMin L + (L : ℤ))).card = L := by
    rw [Int.card_Ico]
    simp
  have he := Finset.eq_of_subset_of_card_le hs (by omega)
  have hmem : n ∈ Finset.image (centered L) Finset.univ := by
    rw [he]
    exact Finset.mem_Ico.mpr hn
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hmem
  exact ⟨v, hv⟩

/-- The shifted centered fundamental cube contains the support cube, including odd L. -/
theorem exists_grid_interval {L : ℕ} [NeZero L] (hL : 4 ≤ L) {t : ℝ} (ht : |t| ≤ 2) :
    ∃ v : ZMod L, t ∈ Set.Ico (quadS L * ((centered L v : ℤ):ℝ))
      (quadS L * ((centered L v : ℤ):ℝ) + quadS L) := by
  have hS := quadS_pos (L := L)
  have hlo : (jMin L : ℝ) ≤ t / quadS L := by
    rw [le_div_iff₀ hS]
    linarith [A_le_neg2 hL, (abs_le.mp ht).1]
  have hhi : t / quadS L < ((jMin L + (L : ℤ) : ℤ) : ℝ) := by
    rw [div_lt_iff₀ hS]
    push_cast
    have he := L_mul_quadS (L := L)
    nlinarith [A_add_2pi_gt2 hL, (abs_le.mp ht).2]
  obtain ⟨v, hv⟩ := exists_centered ⌊t / quadS L⌋
    ⟨Int.le_floor.mpr hlo, Int.floor_lt.mpr hhi⟩
  refine ⟨v, ?_⟩
  rw [hv]
  constructor
  · have hf := Int.floor_le (t / quadS L)
    have := (le_div_iff₀ hS).mp hf
    linarith
  · have hf := Int.lt_floor_add_one (t / quadS L)
    have := (div_lt_iff₀ hS).mp hf
    nlinarith

theorem quadCell_measurable {d L : ℕ} [NeZero L] (k : Torus d L) :
    MeasurableSet (quadCell d L k) :=
  MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)

theorem quadCell_volume {d L : ℕ} [NeZero L] (k : Torus d L) :
    volume (quadCell d L k) = ENNReal.ofReal (quadS L ^ d) := by
  unfold quadCell
  rw [Real.volume_pi_Ico]
  simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (ENNReal.ofReal_pow (quadS_pos (L := L)).le d).symm

theorem quadCell_volume_real {d L : ℕ} [NeZero L] (k : Torus d L) :
    volume.real (quadCell d L k) = quadS L ^ d := by
  rw [Measure.real, quadCell_volume,
    ENNReal.toReal_ofReal (pow_nonneg (quadS_pos (L := L)).le d)]

theorem quadCell_disjoint {d L : ℕ} [NeZero L] :
    Pairwise (fun k l => Disjoint (quadCell d L k) (quadCell d L l)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro x hx hy
  apply hkl
  funext j
  have hxj := hx j (Set.mem_univ j)
  have hyj := hy j (Set.mem_univ j)
  simp only [Set.mem_Ico, gridAngle_eq_quadS] at hxj hyj
  apply centered_injective
  by_contra hne
  have hS := quadS_pos (L := L)
  have hh : centered L (k j) + 1 ≤ centered L (l j) ∨
      centered L (l j) + 1 ≤ centered L (k j) := by omega
  rcases hh with hh | hh
  · have hr : (centered L (k j) : ℝ) + 1 ≤ (centered L (l j) : ℝ) := by exact_mod_cast hh
    nlinarith
  · have hr : (centered L (l j) : ℝ) + 1 ≤ (centered L (k j) : ℝ) := by exact_mod_cast hh
    nlinarith

theorem quadCell_cover {d L : ℕ} [NeZero L] (hL : 4 ≤ L) (x : Fin d → ℝ)
    (hx : ∀ j, |x j| ≤ 2) : x ∈ ⋃ k : Torus d L, quadCell d L k := by
  choose v hv using fun j => exists_grid_interval hL (hx j)
  apply Set.mem_iUnion.mpr
  refine ⟨v, ?_⟩
  intro j _
  simpa only [gridAngle_eq_quadS] using hv j

theorem quadCell_dist {d L : ℕ} [NeZero L] (k : Torus d L) (x : Fin d → ℝ)
    (hx : x ∈ quadCell d L k) : dist (gridAngle k) x ≤ quadS L := by
  apply (dist_pi_le_iff (quadS_pos (L := L)).le).mpr
  intro j
  have hj := hx j (Set.mem_univ j)
  rw [Real.dist_eq]
  apply abs_le.mpr
  constructor <;> linarith [hj.1, hj.2]

theorem quadCell_integrable {d L : ℕ} [NeZero L] (k : Torus d L)
    {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) : IntegrableOn f (quadCell d L k) := by
  apply (hf.integrableOn_Icc (a := gridAngle k)
    (b := fun j => gridAngle k j + quadS L)).mono_set
  intro x hx
  constructor
  · intro j
    exact (hx j (Set.mem_univ j)).1
  · intro j
    exact (hx j (Set.mem_univ j)).2.le


theorem quadCell_error {d L : ℕ} [NeZero L] (k : Torus d L)
    {f : (Fin d → ℝ) → ℂ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ‖((quadS L ^ d : ℝ) : ℂ) * f (gridAngle k) - ∫ x in quadCell d L k, f x‖ ≤
      (K : ℝ) * quadS L * quadS L ^ d := by
  have hfinite : volume (quadCell d L k) < ∞ := by
    rw [quadCell_volume]
    exact ENNReal.ofReal_lt_top
  have hc : IntegrableOn (fun _ : Fin d → ℝ => f (gridAngle k)) (quadCell d L k) :=
    integrableOn_const hfinite.ne
  have hi := quadCell_integrable k hf.continuous
  have heq : ((quadS L ^ d : ℝ) : ℂ) * f (gridAngle k) -
      ∫ x in quadCell d L k, f x =
      ∫ x in quadCell d L k, f (gridAngle k) - f x := by
    rw [integral_sub hc hi, setIntegral_const, quadCell_volume_real]
    rfl
  rw [heq]
  have hb := norm_setIntegral_le_of_norm_le_const hfinite (fun x hx =>
    show ‖f (gridAngle k) - f x‖ ≤ (K : ℝ) * quadS L from by
      rw [← dist_eq_norm]
      exact hf.dist_le_mul_of_le (quadCell_dist k x hx))
  simpa only [quadCell_volume_real] using hb

theorem gridQuadrature_aux : GridQuadratureStatement := by
  intro d
  refine ⟨2 * Real.pi, by positivity, ?_⟩
  intro L _ hL f K hf hsupp
  have hsum : (∫ x, f x) = ∑ k : Torus d L, ∫ x in quadCell d L k, f x := by
    rw [← integral_iUnion_fintype (s := quadCell d L)
      (fun k => quadCell_measurable k) quadCell_disjoint
      (fun k => quadCell_integrable k hf.continuous)]
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro x hx
    apply hsupp
    by_contra h
    push_neg at h
    exact hx (quadCell_cover hL x h)
  have hP : (2 * Real.pi) ^ d ≠ 0 := by positivity
  have hN : (Fintype.card (Torus d L) : ℝ) ≠ 0 := by
    rw [card_torus]
    push_cast
    have hpos : 0 < L := NeZero.pos L
    positivity
  have hS : quadS L ^ d = (2 * Real.pi) ^ d / (L : ℝ) ^ d := by
    simp only [quadS, div_pow]
  have hcoefR : (Fintype.card (Torus d L) : ℝ)⁻¹ =
      ((2 * Real.pi) ^ d)⁻¹ * quadS L ^ d := by
    rw [card_torus, Nat.cast_pow, hS]
    field_simp
  have hcoef : (Fintype.card (Torus d L) : ℂ)⁻¹ =
      ((((2 * Real.pi) ^ d)⁻¹ : ℝ) : ℂ) * ((quadS L ^ d : ℝ) : ℂ) := by
    have hc := congrArg (fun x : ℝ => (x : ℂ)) hcoefR
    simpa only [Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_mul] using hc
  let a : ℝ := ((2 * Real.pi) ^ d)⁻¹
  let e : Torus d L → ℂ := fun k =>
    ((quadS L ^ d : ℝ) : ℂ) * f (gridAngle k) - ∫ x in quadCell d L k, f x
  have heq : gridAvg (fun k : Torus d L => f (gridAngle k)) -
      (a : ℂ) * ∫ x, f x = (a : ℂ) * ∑ k, e k := by
    rw [gridAvg, hcoef, hsum]
    simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have han : ‖(a : ℂ)‖ = a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
  have hbound : ‖∑ k, e k‖ ≤
      (Fintype.card (Torus d L) : ℝ) * ((K : ℝ) * quadS L * quadS L ^ d) := by
    calc ‖∑ k, e k‖ ≤ ∑ k, ‖e k‖ := norm_sum_le _ _
      _ ≤ ∑ _k : Torus d L, (K : ℝ) * quadS L * quadS L ^ d :=
        Finset.sum_le_sum (fun k _ => quadCell_error k hf)
      _ = _ := by simp [nsmul_eq_mul]
  have hcancel : a * (Fintype.card (Torus d L) : ℝ) * quadS L ^ d = 1 := by
    dsimp [a]
    calc ((2 * Real.pi) ^ d)⁻¹ * (Fintype.card (Torus d L) : ℝ) * quadS L ^ d =
        (Fintype.card (Torus d L) : ℝ) * (((2 * Real.pi) ^ d)⁻¹ * quadS L ^ d) := by ring
      _ = 1 := by rw [← hcoefR]; exact mul_inv_cancel₀ hN
  rw [heq, norm_mul, han]
  calc a * ‖∑ k, e k‖ ≤
      a * ((Fintype.card (Torus d L) : ℝ) * ((K : ℝ) * quadS L * quadS L ^ d)) :=
        mul_le_mul_of_nonneg_left hbound ha
    _ = (K : ℝ) * quadS L * (a * (Fintype.card (Torus d L) : ℝ) * quadS L ^ d) := by ring
    _ = (K : ℝ) * quadS L := by rw [hcancel, mul_one]
    _ = 2 * Real.pi * K / L := by unfold quadS; ring


end AndersonAC.S3H

namespace AndersonAC.S3

theorem frequencySum_proof : FrequencySumStatement :=
  AndersonAC.S3H.frequencySum_aux

theorem gridQuadrature_proof : GridQuadratureStatement :=
  AndersonAC.S3H.gridQuadrature_aux

end AndersonAC.S3
