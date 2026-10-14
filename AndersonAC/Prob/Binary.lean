import AndersonAC.Blueprint.FiniteInputs

open MeasureTheory Measure Set Filter
open scoped ENNReal NNReal

namespace AndersonAC.MuseProb

noncomputable section

open AndersonAC.Blueprint

/-- Sign of a fair bit: `true ↦ 1`, `false ↦ -1` (paper `02-state.tex`, eq:history-binary). -/
def bitSign (b : Bool) : ℝ := if b then 1 else -1

lemma bitSign_abs (b : Bool) : |bitSign b| = 1 := by cases b <;> simp [bitSign]

lemma bitSign_eq (b : Bool) : bitSign b = (if b then (1 : ℝ) else -1) := rfl

/-- Each fair coin gives mass `1/2` to each outcome. -/
lemma coin_singleton (b : Bool) :
    (PMF.uniformOfFintype Bool).toMeasure {b} = (2 : ℝ≥0∞)⁻¹ := by
  have h := PMF.toMeasure_uniformOfFintype_apply (α := Bool) (s := ({b} : Set Bool))
    (MeasurableSet.singleton b)
  simpa using h

/-- The product bit law is a probability measure (instance, for explicit use). -/
instance bitLaw_prob : IsProbabilityMeasure bitLaw := by
  unfold bitLaw
  infer_instance

/-- Coordinate projections are independent fair bits. -/
lemma iIndepFun_bits :
    ProbabilityTheory.iIndepFun (fun (i : ℕ) (ε : BitSpace) => ε i) bitLaw := by
  unfold bitLaw
  exact ProbabilityTheory.iIndepFun_infinitePi (fun _ => measurable_id)

/-- Finite cylinder fixing the first `N` bits has mass `2⁻ᴺ`. -/
lemma cylinder_firstN_measure (N : ℕ) (p : Fin N → Bool) :
    bitLaw {ε : BitSpace | ∀ i : Fin N, ε (i : ℕ) = p i} = (2 : ℝ≥0∞)⁻¹ ^ N := by
  unfold bitLaw
  classical
  let t : ℕ → Set Bool := fun i => if h : i < N then {p ⟨i, h⟩} else Set.univ
  have hset : {ε : BitSpace | ∀ i : Fin N, ε (i : ℕ) = p i}
      = (↑(Finset.range N) : Set ℕ).pi t := by
    ext ε
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Finset.mem_coe, Finset.mem_range, t]
    constructor
    · intro h i hi
      simp only [hi, dite_true]
      exact h ⟨i, hi⟩
    · intro h i
      have hi : (i : ℕ) < N := i.isLt
      have h2 := h (i : ℕ) hi
      simp only [hi, dite_true] at h2
      simpa using h2
  rw [hset]
  have ht : ∀ i ∈ Finset.range N, MeasurableSet (t i) := by
    intro i hi
    have hiN : i < N := Finset.mem_range.mp hi
    simp only [t, hiN, dite_true]
    exact MeasurableSet.singleton _
  rw [Measure.infinitePi_pi _ ht]
  have hcoin : ∀ i ∈ Finset.range N,
      (PMF.uniformOfFintype Bool).toMeasure (t i) = (2 : ℝ≥0∞)⁻¹ := by
    intro i hi
    have hiN : i < N := Finset.mem_range.mp hi
    simp only [t, hiN, dite_true]
    exact coin_singleton _
  rw [Finset.prod_congr rfl hcoin]
  rw [Finset.prod_const, Finset.card_range]

/-- Summability of the binary series at every shift (geometric majorant). -/
lemma summable_binaryTail (h : ℕ) (ε : BitSpace) :
    Summable (fun n : ℕ => (if ε (n + h) then (1 : ℝ) else -1) / (2 : ℝ) ^ (n + h + 1)) := by
  apply Summable.of_abs
  have hgeo := summable_geometric_two
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) ?_ hgeo
  intro n
  have habs : |(if ε (n + h) then (1 : ℝ) else -1) / (2 : ℝ) ^ (n + h + 1)|
      = 1 / (2 : ℝ) ^ (n + h + 1) := by
    rw [abs_div]
    congr 1
    · cases ε (n + h) <;> simp
    · rw [abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [habs]
  have hle : (1 : ℝ) / (2 : ℝ) ^ (n + h + 1) ≤ ((1 : ℝ) / 2) ^ n := by
    have heq : ((1 : ℝ) / 2) ^ n = 1 / (2 : ℝ) ^ n := by rw [div_pow, one_pow]
    rw [heq]
    apply one_div_le_one_div_of_le (pow_pos (by norm_num) n)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  exact hle

/-- The binary tail is measurable. -/
lemma measurable_binaryTail (h : ℕ) : Measurable (binaryTail h) := by
  unfold binaryTail
  apply Measurable.tsum
  intro n
  have h1 : Measurable (fun ε : BitSpace => ε (n + h)) := measurable_pi_apply _
  have h2 : Measurable (fun b : Bool => (if b then (1 : ℝ) else -1)) :=
    Measurable.of_discrete
  exact (h2.comp h1).div_const _

/-- Pointwise bound for the tail: `|binaryTail h| ≤ 2⁻ʰ`. -/
lemma abs_binaryTail_le (h : ℕ) (ε : BitSpace) :
    |binaryTail h ε| ≤ ((2 : ℝ)⁻¹) ^ h := by
  have hnorm : Summable (fun n : ℕ =>
      ‖(if ε (n + h) then (1 : ℝ) else -1) / (2 : ℝ) ^ (n + h + 1)‖) := by
    have habs : ∀ n : ℕ,
        ‖(if ε (n + h) then (1 : ℝ) else -1) / (2 : ℝ) ^ (n + h + 1)‖
          = 1 / (2 : ℝ) ^ (n + h + 1) := by
      intro n
      rw [norm_div, norm_pow]
      congr 1
      · cases ε (n + h) <;> simp
      · simp [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp only [habs]
    have hgeo := summable_geometric_two
    refine Summable.of_nonneg_of_le (fun n => by positivity) ?_ hgeo
    intro n
    have heq : ((1 : ℝ) / 2) ^ n = 1 / (2 : ℝ) ^ n := by rw [div_pow, one_pow]
    rw [heq]
    apply one_div_le_one_div_of_le (pow_pos (by norm_num) n)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  -- evaluate the majorant tsum to 2⁻ʰ
  have htsum : (∑' n : ℕ, (1 : ℝ) / (2 : ℝ) ^ (n + h + 1)) = ((2 : ℝ)⁻¹) ^ h := by
    have heq : ∀ n : ℕ, (1 : ℝ) / (2 : ℝ) ^ (n + h + 1)
        = (((2 : ℝ)⁻¹) ^ h / 2) * (((1 : ℝ) / 2) ^ n) := by
      intro n
      rw [div_pow, one_pow]
      simp only [one_div, pow_add, mul_inv, inv_pow]
      ring
    simp only [heq]
    rw [tsum_mul_left, tsum_geometric_two]
    ring
  have hnorm_eq : (∑' n : ℕ,
      ‖(if ε (n + h) then (1 : ℝ) else -1) / (2 : ℝ) ^ (n + h + 1)‖)
      = ∑' n : ℕ, (1 : ℝ) / (2 : ℝ) ^ (n + h + 1) := by
    apply tsum_congr
    intro n
    rw [norm_div, norm_pow]
    congr 1
    · cases ε (n + h) <;> simp
    · simp [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have htail : binaryTail h ε
      = ∑' n : ℕ, (if ε (n + h) then (1 : ℝ) else -1) / (2 : ℝ) ^ (n + h + 1) := rfl
  rw [htail, ← Real.norm_eq_abs]
  calc ‖∑' n : ℕ, (if ε (n + h) then (1 : ℝ) else -1) / (2 : ℝ) ^ (n + h + 1)‖
        ≤ ∑' n : ℕ, ‖(if ε (n + h) then (1 : ℝ) else -1) / (2 : ℝ) ^ (n + h + 1)‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ = ∑' n : ℕ, (1 : ℝ) / (2 : ℝ) ^ (n + h + 1) := hnorm_eq
    _ = ((2 : ℝ)⁻¹) ^ h := htsum

/-- Finite partial sum of the h = 0 series (first `N` bits). -/
def partialSum0 (N : ℕ) (ε : BitSpace) : ℝ :=
  ∑ n ∈ Finset.range N, (if ε n then (1 : ℝ) else -1) / (2 : ℝ) ^ (n + 1)

/-- Prefix value: constant partial sum on a fixed first-`N`-bits cylinder. -/
def prefixVal0 (N : ℕ) (p : Fin N → Bool) : ℝ :=
  ∑ i : Fin N, (if p i then (1 : ℝ) else -1) / (2 : ℝ) ^ ((i : ℕ) + 1)

/-- Splitting the h = 0 series into prefix sum plus shifted tail. -/
lemma binaryTail_zero_split (N : ℕ) (ε : BitSpace) :
    binaryTail 0 ε = partialSum0 N ε + binaryTail N ε := by
  unfold binaryTail partialSum0
  have hsum := summable_binaryTail 0 ε
  have hsplit := hsum.sum_add_tsum_nat_add N
  simpa [Nat.add_zero] using hsplit.symm

/-- On a fixed-prefix cylinder, the partial sum is constant. -/
lemma partialSum0_eq_prefixVal {N : ℕ} {p : Fin N → Bool} {ε : BitSpace}
    (hε : ∀ i : Fin N, ε (i : ℕ) = p i) :
    partialSum0 N ε = prefixVal0 N p := by
  unfold partialSum0 prefixVal0
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [hε i]

/-- Cylinder maps into the closed dyadic interval (prefix plus tail bound). -/
lemma cylinder_subset_closedInterval {N : ℕ} (p : Fin N → Bool) :
    {ε : BitSpace | ∀ i : Fin N, ε (i : ℕ) = p i}
      ⊆ binaryTail 0 ⁻¹' Set.Icc (prefixVal0 N p - ((2 : ℝ)⁻¹) ^ N)
        (prefixVal0 N p + ((2 : ℝ)⁻¹) ^ N) := by
  intro ε hε
  simp only [Set.mem_preimage, Set.mem_Icc]
  have hsplit := binaryTail_zero_split N ε
  have hconst := partialSum0_eq_prefixVal (p := p) (fun i => hε i)
  have htail := abs_binaryTail_le N ε
  have heq : binaryTail 0 ε - prefixVal0 N p = binaryTail N ε := by
    rw [hsplit, hconst]
    ring
  have hmem := abs_le.mp htail
  constructor <;> linarith [heq, hmem.1, hmem.2]

def prefixInt (N : ℕ) (p : Fin N → Bool) : ℤ :=
  ∑ i : Fin N, (if p i then 1 else -1) * (2 : ℤ) ^ (N - 1 - (i : ℕ))

/-- Prefix values are odd multiples of `2⁻ᴺ`. -/
lemma prefixVal0_eq (N : ℕ) (hn : 0 < N) (p : Fin N → Bool) :
    prefixVal0 N p = (prefixInt N p : ℝ) / (2 : ℝ) ^ N := by
  unfold prefixVal0 prefixInt
  rw [Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have hiN : (i : ℕ) < N := i.isLt
  have hexp : N - 1 - (i : ℕ) + ((i : ℕ) + 1) = N := by omega
  have hpow : (2 : ℝ) ^ N
      = (2 : ℝ) ^ (N - 1 - (i : ℕ)) * (2 : ℝ) ^ ((i : ℕ) + 1) := by
    rw [← pow_add, hexp]
  have h2N : (2 : ℝ) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2i : (2 : ℝ) ^ ((i : ℕ) + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  by_cases hpi : p i = true
  · simp only [hpi, ite_true]
    push_cast
    rw [div_eq_div_iff h2i h2N, hpow]
    ring
  · simp only [hpi, ite_false]
    push_cast
    rw [div_eq_div_iff h2i h2N, hpow]
    ring

/-- Prefix numerators are odd (for `N ≥ 1`). -/
lemma prefixInt_odd (N : ℕ) (hn : 0 < N) (p : Fin N → Bool) :
    Odd (prefixInt N p) := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
  unfold prefixInt
  rw [Fin.sum_univ_castSucc]
  apply Even.add_odd
  · -- remaining terms are multiples of 2
    rw [even_iff_two_dvd]
    apply Finset.dvd_sum
    intro i _
    have hiM : (i : ℕ) < M := i.isLt
    have hval : ((i.castSucc : Fin (M + 1)) : ℕ) = (i : ℕ) := by
      simp [Fin.val_castSucc]
    have hexp_ge : 1 ≤ M + 1 - 1 - ((i.castSucc : Fin (M + 1)) : ℕ) := by
      rw [hval]
      omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : M + 1 - 1 - ((i.castSucc : Fin (M + 1)) : ℕ) ≠ 0)
    rw [hk, pow_succ, ← mul_assoc]
    exact dvd_mul_left _ _
  · -- last term is ±1, hence odd
    have hlast : ((Fin.last M : Fin (M + 1)) : ℕ) = M := Fin.val_last M
    by_cases hlastb : p (Fin.last M) = true
    · simp only [hlastb, ite_true]
      rw [show M + 1 - 1 - ((Fin.last M : Fin (M + 1)) : ℕ) = 0 by
        rw [hlast]; omega, pow_zero, mul_one]
      exact odd_one
    · have hfalse : p (Fin.last M) = false := Bool.eq_false_of_ne_true hlastb
      rw [hfalse]
      show Odd ((-1 : ℤ) * (2 : ℤ) ^ (M + 1 - 1 - ((Fin.last M : Fin (M + 1)) : ℕ)))
      rw [show M + 1 - 1 - ((Fin.last M : Fin (M + 1)) : ℕ) = 0 by
        rw [hlast]; omega, pow_zero, mul_one]
      exact ⟨-1, by ring⟩

/-- Integer separation: distinct prefix numerators differ by at least two. -/
lemma prefixInt_sep {N : ℕ} (hn : 0 < N) {p q : Fin N → Bool} (hne : p ≠ q) :
    2 ≤ |prefixInt N p - prefixInt N q| := by
  classical
  -- last differing index (maximal val among differing positions)
  obtain ⟨i0, hi0⟩ : ∃ i : Fin N, p i ≠ q i := Function.ne_iff.mp hne
  set D : Finset (Fin N) := Finset.univ.filter (fun i => p i ≠ q i) with hDdef
  have hDne : D.Nonempty := ⟨i0, by simp [hDdef, hi0]⟩
  set k : Fin N := D.max' hDne with hkdef
  have hkD : k ∈ D := D.max'_mem hDne
  have hkd : p k ≠ q k := by simpa [hDdef] using hkD
  have hmax : ∀ i : Fin N, p i ≠ q i → (i : ℕ) ≤ (k : ℕ) := by
    intro i hi
    have himem : i ∈ D := by simpa [hDdef, hi] using hi
    have hle := D.le_max' i himem
    simpa using hle
  have hkN : (k : ℕ) < N := k.isLt
  -- sign difference at k is ±2
  have hsgn_k : ((if p k then (1 : ℤ) else -1) - (if q k then (1 : ℤ) else -1))
      = (if p k then 2 else -2) := by
    by_cases hpk : p k = true
    · have hqk : q k = false := Bool.eq_false_of_ne_true (fun h => hkd (by rw [hpk, h]))
      simp [hpk, hqk]
    · have hpkf : p k = false := Bool.eq_false_of_ne_true hpk
      have hqk : q k = true := by
        by_contra hcon
        have hqf : q k = false := Bool.eq_false_of_ne_true hcon
        exact hkd (by rw [hpkf, hqf])
      simp [hpkf, hqk]
  -- split the difference sum at k; later indices match exactly
  have hsplit : prefixInt N p - prefixInt N q
      = (((if p k then (1 : ℤ) else -1) - (if q k then (1 : ℤ) else -1))
          * (2 : ℤ) ^ (N - 1 - (k : ℕ)))
        + ∑ i ∈ Finset.univ.erase k,
          (((if p i then (1 : ℤ) else -1) - (if q i then (1 : ℤ) else -1))
            * (2 : ℤ) ^ (N - 1 - (i : ℕ))) := by
    unfold prefixInt
    rw [← Finset.sum_sub_distrib]
    have hmem : k ∈ (Finset.univ : Finset (Fin N)) := Finset.mem_univ k
    rw [← Finset.add_sum_erase _ _ hmem]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  -- 2-adic level A = N - k ≥ 1 (kept explicit for omega with Nat subtraction)
  have hApos : 1 ≤ N - (k : ℕ) := by omega
  -- rest is a multiple of 2^(N-k+1): later indices match, earlier are even
  have hrest_dvd : (2 : ℤ) ^ (N - (k : ℕ) + 1) ∣ ∑ i ∈ Finset.univ.erase k,
      (((if p i then (1 : ℤ) else -1) - (if q i then (1 : ℤ) else -1))
        * (2 : ℤ) ^ (N - 1 - (i : ℕ))) := by
    apply Finset.dvd_sum
    intro i hi
    have hik : i ≠ k := Finset.ne_of_mem_erase hi
    have hvalne : (i : ℕ) ≠ (k : ℕ) := fun heq => hik (Fin.ext heq)
    rcases lt_or_gt_of_ne hvalne with hlt | hgt
    · -- earlier index: difference is even, power is large enough
      have hodd_p : Odd (if p i then (1 : ℤ) else -1) := by
        by_cases h : p i = true
        · simp [h]
        · have hf : p i = false := Bool.eq_false_of_ne_true h
          simp [hf]
      have hodd_q : Odd (if q i then (1 : ℤ) else -1) := by
        by_cases h : q i = true
        · simp [h]
        · have hf : q i = false := Bool.eq_false_of_ne_true h
          simp [hf]
      have hsgn_even : Even (((if p i then (1 : ℤ) else -1)
          - (if q i then (1 : ℤ) else -1))) :=
        hodd_p.sub_odd hodd_q
      obtain ⟨m, hm⟩ := even_iff_two_dvd.mp hsgn_even
      have h1 : (i : ℕ) + 1 ≤ (k : ℕ) := Nat.succ_le_of_lt hlt
      have h2 : N - (k : ℕ) ≤ N - ((i : ℕ) + 1) := Nat.sub_le_sub_left h1 N
      have h3 : N - (k : ℕ) + 1 ≤ N - ((i : ℕ) + 1) + 1 := Nat.add_le_add_right h2 1
      have heq : N - ((i : ℕ) + 1) + 1 = N - 1 - (i : ℕ) + 1 := by
        have e1 : (i : ℕ) + 1 = 1 + (i : ℕ) := add_comm _ _
        rw [e1, Nat.sub_add_eq]
      rw [heq] at h3
      have hexp : N - (k : ℕ) + 1 ≤ N - 1 - (i : ℕ) + 1 := h3
      have hsplit_pow : (2 : ℤ) ^ (N - 1 - (i : ℕ) + 1)
          = (2 : ℤ) ^ (N - (k : ℕ) + 1) * (2 : ℤ) ^ (N - 1 - (i : ℕ) + 1 - (N - (k : ℕ) + 1)) := by
        conv_lhs => rw [← Nat.add_sub_cancel' hexp, pow_add]
      have hsucc : (2 : ℤ) ^ (N - 1 - (i : ℕ) + 1)
          = (2 : ℤ) ^ (N - 1 - (i : ℕ)) * 2 := by
        rw [pow_succ]
      have hterm : (((if p i then (1 : ℤ) else -1) - (if q i then (1 : ℤ) else -1))
          * (2 : ℤ) ^ (N - 1 - (i : ℕ)))
          = (2 : ℤ) ^ (N - (k : ℕ) + 1) * (m * (2 : ℤ) ^ (N - 1 - (i : ℕ) + 1 - (N - (k : ℕ) + 1))) := by
        have hmain_eq : (((if p i then (1 : ℤ) else -1) - (if q i then (1 : ℤ) else -1))
            * (2 : ℤ) ^ (N - 1 - (i : ℕ)))
            = m * ((2 : ℤ) ^ (N - 1 - (i : ℕ)) * 2) := by
          rw [hm]
          ring
        rw [hmain_eq, ← hsucc, hsplit_pow]
        ring
      rw [hterm]
      exact dvd_mul_right _ _
    · -- later index: maximality forces equality, term vanishes
      have heq : p i = q i := by
        by_contra hcon
        have hle := hmax i hcon
        omega
      simp [heq]
  -- main term is ±2^A; total is 2^A times an odd number
  have hAeq : N - 1 - (k : ℕ) + 1 = (N - (k : ℕ)) := by omega
  have hmain2 : ((if p k then (1 : ℤ) else -1) - (if q k then (1 : ℤ) else -1))
        * (2 : ℤ) ^ (N - 1 - (k : ℕ)) = (if p k then (2 : ℤ) ^ (N - (k : ℕ)) else -((2 : ℤ) ^ (N - (k : ℕ)))) := by
    rw [hsgn_k]
    by_cases hpk : p k = true
    · simp [hpk]
      have hpow2 : (2 : ℤ) ^ (N - 1 - (k : ℕ)) * 2 = (2 : ℤ) ^ (N - (k : ℕ)) := by
        have he : N - 1 - (k : ℕ) + 1 = N - (k : ℕ) := by omega
        rw [← he, pow_succ]
      linarith [hpow2]
    · simp [hpk]
      have hpow2 : (2 : ℤ) ^ (N - 1 - (k : ℕ)) * 2 = (2 : ℤ) ^ (N - (k : ℕ)) := by
        have he : N - 1 - (k : ℕ) + 1 = N - (k : ℕ) := by omega
        rw [← he, pow_succ]
      linarith [hpow2]
  obtain ⟨t, ht⟩ := hrest_dvd
  -- combine into 2^A * odd and bound below by 2
  have hDeq : prefixInt N p - prefixInt N q
      = (2 : ℤ) ^ (N - (k : ℕ)) * ((if p k then 1 else -1) + 2 * t) := by
    rw [hsplit, hmain2, ht]
    by_cases hpk : p k = true
    · simp [hpk]
      ring
    · have hpkf : p k = false := Bool.eq_false_of_ne_true hpk
      simp [hpkf]
      ring
  have hodd : Odd ((if p k then (1 : ℤ) else -1) + 2 * t) := by
    by_cases hpk : p k = true
    · simp [hpk, odd_one]
    · have hpkf : p k = false := Bool.eq_false_of_ne_true hpk
      simp [hpkf]
      exact ⟨-1 + t, by ring⟩
  have habs1 : (1 : ℤ) ≤ |((if p k then (1 : ℤ) else -1) + 2 * t)| := by
    obtain ⟨m, hm⟩ := hodd
    rw [hm]
    have hne : (2 : ℤ) * m + 1 ≠ 0 := by
      intro hcon
      omega
    have hpos : 0 < |(2 : ℤ) * m + 1| := abs_pos.mpr hne
    omega
  have h2A : (2 : ℤ) ^ (N - (k : ℕ)) ≥ 2 := by
    calc (2 : ℤ) ^ (N - (k : ℕ)) ≥ (2 : ℤ) ^ 1 := pow_le_pow_right₀ (by norm_num) hApos
      _ = 2 := pow_one _
  rw [hDeq, abs_mul]
  have habs2 : |(2 : ℤ) ^ (N - (k : ℕ))| = (2 : ℤ) ^ (N - (k : ℕ)) := abs_of_pos (by positivity)
  rw [habs2]
  calc (2 : ℤ) ^ (N - (k : ℕ)) * |((if p k then 1 else -1) + 2 * t)|
      ≥ 2 * 1 := mul_le_mul h2A habs1 (by positivity) (by positivity)
    _ = 2 := mul_one _

/-- Distinct prefixes give distinct values (via integer separation). -/
lemma prefixVal0_injective (N : ℕ) : Function.Injective (prefixVal0 N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hn
  · intro p q _
    funext i
    exact i.elim0
  · intro p q hmq
    by_contra hne
    have hsep := prefixInt_sep hn hne
    have heqK : prefixInt N p = prefixInt N q := by
      have h1 := prefixVal0_eq N hn p
      have h2 := prefixVal0_eq N hn q
      rw [hmq] at h1
      have heqR : ((prefixInt N p : ℤ) : ℝ) / (2 : ℝ) ^ N
          = ((prefixInt N q : ℤ) : ℝ) / (2 : ℝ) ^ N :=
        h1.symm.trans h2
      have h2N : (2 : ℝ) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
      have hcast : ((prefixInt N p : ℤ) : ℝ) = ((prefixInt N q : ℤ) : ℝ) := by
        have hmul : ((prefixInt N p : ℤ) : ℝ) * (2 : ℝ) ^ N
            = ((prefixInt N q : ℤ) : ℝ) * (2 : ℝ) ^ N :=
          (div_eq_div_iff h2N h2N).mp heqR
        exact mul_right_cancel₀ h2N hmul
      exact Int.cast_inj.mp hcast
    rw [heqK, sub_self, abs_zero] at hsep
    omega

/-- Real spacing of distinct prefix values (from integer separation). -/
lemma prefixVal0_spacing {N : ℕ} (hn : 0 < N) {p q : Fin N → Bool} (hne : p ≠ q) :
    2 * ((2 : ℝ)⁻¹) ^ N ≤ |prefixVal0 N p - prefixVal0 N q| := by
  have hsepK : 2 ≤ |prefixInt N p - prefixInt N q| :=
    prefixInt_sep hn hne
  -- integer ≥2 transfers to reals, then divide by 2^N
  have hKr : (2 : ℝ) ≤ |((prefixInt N p : ℤ) : ℝ) - ((prefixInt N q : ℤ) : ℝ)| := by
    exact_mod_cast hsepK
  have h1 := prefixVal0_eq N hn p
  have h2 := prefixVal0_eq N hn q
  have hpos : (0 : ℝ) < (2 : ℝ) ^ N := pow_pos (by norm_num) N
  rw [h1, h2]
  have hdiv : |((prefixInt N p : ℤ) : ℝ) / (2 : ℝ) ^ N
      - ((prefixInt N q : ℤ) : ℝ) / (2 : ℝ) ^ N|
      = |((prefixInt N p : ℤ) : ℝ) - ((prefixInt N q : ℤ) : ℝ)| / (2 : ℝ) ^ N := by
    rw [div_sub_div_same, abs_div, abs_of_pos hpos]
  rw [hdiv]
  have h2eq : (2 : ℝ) * ((2 : ℝ)⁻¹) ^ N = 2 / (2 : ℝ) ^ N := by
    rw [inv_pow]
    field_simp
  rw [h2eq]
  exact div_le_div_of_nonneg_right hKr hpos.le

/-- Strictly inside the dyadic interval forces the prefix (via spacing, no first-difference). -/
lemma openInterval_subset_cylinder {N : ℕ} (p : Fin N → Bool) :
    binaryTail 0 ⁻¹' Set.Ioo (prefixVal0 N p - ((2 : ℝ)⁻¹) ^ N)
        (prefixVal0 N p + ((2 : ℝ)⁻¹) ^ N)
      ⊆ {ε : BitSpace | ∀ i : Fin N, ε (i : ℕ) = p i} := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hn
  · -- N = 0: cylinder is univ (vacuous prefix condition)
    intro ε _
    intro i
    exact i.elim0
  · intro ε hε
    have hmem : binaryTail 0 ε ∈ Set.Ioo (prefixVal0 N p - ((2 : ℝ)⁻¹) ^ N)
        (prefixVal0 N p + ((2 : ℝ)⁻¹) ^ N) := hε
    have hlt : |binaryTail 0 ε - prefixVal0 N p| < ((2 : ℝ)⁻¹) ^ N := by
      rw [Set.mem_Ioo] at hmem
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    by_contra hcon
    -- hcon : ¬ ∀ i, ...; get a differing index and the ε-prefix
    have hex : ∃ i : Fin N, ε (i : ℕ) ≠ p i := not_forall.mp hcon
    obtain ⟨i0, hi0⟩ := hex
    set q : Fin N → Bool := fun i => ε (i : ℕ) with hqdef
    have hqp_ne : q ≠ p := by
      intro heq
      have hcon : ε (i0 : ℕ) = p i0 := by
        have hqi : q i0 = p i0 := congrFun heq i0
        simpa [hqdef] using hqi
      exact hi0 hcon
    -- M_N(ε) equals the ε-prefix value; distinct prefixes are spaced
    have hM : partialSum0 N ε = prefixVal0 N q := partialSum0_eq_prefixVal (fun i => rfl)
    have hspace : 2 * ((2 : ℝ)⁻¹) ^ N ≤ |prefixVal0 N q - prefixVal0 N p| :=
      prefixVal0_spacing hn hqp_ne
    -- combine with tail bound to contradict strict membership
    have hsplit := binaryTail_zero_split N ε
    have htail := abs_binaryTail_le N ε
    have hdiff : |binaryTail 0 ε - prefixVal0 N p| ≥ ((2 : ℝ)⁻¹) ^ N := by
      have heqM : partialSum0 N ε = prefixVal0 N q := hM
      have heqF : binaryTail 0 ε - prefixVal0 N p
          = (prefixVal0 N q - prefixVal0 N p) + binaryTail N ε := by
        rw [hsplit, heqM]
        ring
      rw [heqF]
      have htri : |prefixVal0 N q - prefixVal0 N p| - |binaryTail N ε|
          ≤ |(prefixVal0 N q - prefixVal0 N p) + binaryTail N ε| := by
        have h : |prefixVal0 N q - prefixVal0 N p|
            ≤ |(prefixVal0 N q - prefixVal0 N p) + binaryTail N ε| + |binaryTail N ε| := by
          have heq : (prefixVal0 N q - prefixVal0 N p)
              = ((prefixVal0 N q - prefixVal0 N p) + binaryTail N ε) + (-binaryTail N ε) := by
            ring
          rw [heq]
          simpa using abs_add_le ((prefixVal0 N q - prefixVal0 N p) + binaryTail N ε)
            (-binaryTail N ε)
        linarith
      have htailN : |binaryTail N ε| ≤ ((2 : ℝ)⁻¹) ^ N := htail
      linarith [hspace, htailN, htri]
    linarith

/-- Disjoint open intervals around separated prefixes. -/
lemma prefix_intervals_disjoint {N : ℕ} (hn : 0 < N)
    (P : Finset (Fin N → Bool)) :
    Set.PairwiseDisjoint (↑P : Set (Fin N → Bool))
      (fun p => Set.Ioo (prefixVal0 N p - ((2 : ℝ)⁻¹)^N)
        (prefixVal0 N p + ((2 : ℝ)⁻¹)^N)) := by
  intro p _ q _ hpq
  change Disjoint (Set.Ioo (prefixVal0 N p - ((2 : ℝ)⁻¹)^N)
    (prefixVal0 N p + ((2 : ℝ)⁻¹)^N))
    (Set.Ioo (prefixVal0 N q - ((2 : ℝ)⁻¹)^N)
      (prefixVal0 N q + ((2 : ℝ)⁻¹)^N))
  rw [Set.disjoint_left]
  intro x hx hy
  have hsp := prefixVal0_spacing hn hpq
  have hlt : |prefixVal0 N p - prefixVal0 N q| < 2 * ((2 : ℝ)⁻¹)^N := by
    rw [abs_lt]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  linarith

/-- Packing dyadic cylinders bounds the probability of an arbitrary interval.
The error is twice the tail radius and vanishes as the prefix grows. -/
lemma binaryTail_interval_bound (a b : ℝ) (hab : a ≤ b) (N : ℕ) (hn : 0 < N) :
    bitLaw.real (binaryTail 0 ⁻¹' Set.Icc a b)
      ≤ (b - a) / 2 + 2 * ((2 : ℝ)⁻¹)^N := by
  classical
  let c : ℝ := ((2 : ℝ)⁻¹)^N
  have hc : 0 < c := pow_pos (by norm_num) N
  let P := Finset.univ.filter (fun p : Fin N → Bool =>
    a - c ≤ prefixVal0 N p ∧ prefixVal0 N p ≤ b + c)
  let C := fun p : Fin N → Bool => {ε : BitSpace | ∀ i : Fin N, ε (i : ℕ) = p i}
  let J := fun p : Fin N → Bool => Set.Ioo (prefixVal0 N p - c) (prefixVal0 N p + c)
  have hcover : binaryTail 0 ⁻¹' Set.Icc a b ⊆ ⋃ p ∈ P, C p := by
    intro ε hε
    let p : Fin N → Bool := fun i => ε (i : ℕ)
    have hs := binaryTail_zero_split N ε
    have hm : partialSum0 N ε = prefixVal0 N p := partialSum0_eq_prefixVal (fun _ => rfl)
    have ht := abs_le.mp (abs_binaryTail_le N ε)
    have hp : p ∈ P := by
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
      change a ≤ binaryTail 0 ε ∧ binaryTail 0 ε ≤ b at hε
      change -c ≤ binaryTail N ε ∧ binaryTail N ε ≤ c at ht
      constructor <;> linarith [hε.1, hε.2, ht.1, ht.2]
    exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, fun _ => rfl⟩⟩
  have hcyl : ∀ p ∈ P, bitLaw.real (C p) = c := by
    intro p _
    change (bitLaw (C p)).toReal = c
    rw [cylinder_firstN_measure]
    simp [c, ENNReal.toReal_pow, ENNReal.toReal_inv]
  have hprob : bitLaw.real (binaryTail 0 ⁻¹' Set.Icc a b) ≤ (P.card : ℝ) * c := by
    calc bitLaw.real _ ≤ bitLaw.real (⋃ p ∈ P, C p) :=
        measureReal_mono hcover (measure_ne_top _ _)
      _ ≤ ∑ p ∈ P, bitLaw.real (C p) := measureReal_biUnion_finset_le P C
      _ = (P.card : ℝ) * c := by simp [Finset.sum_congr rfl hcyl]
  have hjcover : (⋃ p ∈ P, J p) ⊆ Set.Ioo (a - 2 * c) (b + 2 * c) := by
    intro x hx
    obtain ⟨p, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hp, hx⟩ := Set.mem_iUnion.mp hx
    have hp' : a - c ≤ prefixVal0 N p ∧ prefixVal0 N p ≤ b + c := by
      simpa only [P, Finset.mem_filter, Finset.mem_univ, true_and] using hp
    change prefixVal0 N p - c < x ∧ x < prefixVal0 N p + c at hx
    constructor <;> linarith [hp'.1, hp'.2, hx.1, hx.2]
  have hjvol : volume.real (⋃ p ∈ P, J p) = (P.card : ℝ) * (2 * c) := by
    rw [measureReal_biUnion_finset (prefix_intervals_disjoint hn P)
      (fun _ _ => measurableSet_Ioo) (fun _ _ => by simp [Real.volume_Ioo])]
    have hv : ∀ p ∈ P, volume.real (J p) = 2 * c := by
      intro p _
      change volume.real (Set.Ioo (prefixVal0 N p - c) (prefixVal0 N p + c)) = 2 * c
      rw [Real.volume_real_Ioo_of_le (by linarith)]
      ring
    rw [Finset.sum_congr rfl hv]
    simp
  have hpack : (P.card : ℝ) * (2 * c) ≤ b - a + 4 * c := by
    calc (P.card : ℝ) * (2 * c) = volume.real (⋃ p ∈ P, J p) := hjvol.symm
      _ ≤ volume.real (Set.Ioo (a - 2 * c) (b + 2 * c)) :=
        measureReal_mono hjcover (by simp [Real.volume_Ioo])
      _ = b - a + 4 * c := by
        rw [Real.volume_real_Ioo_of_le (by linarith)]
        ring
  dsimp [c] at hprob hpack ⊢
  linarith

/-- Every interval has probability at most half its length. -/
lemma binaryTail_interval_le (a b : ℝ) (hab : a ≤ b) :
    bitLaw.real (binaryTail 0 ⁻¹' Set.Icc a b) ≤ (b - a) / 2 := by
  have ht : Tendsto (fun N : ℕ => (b - a) / 2 + 2 * ((2 : ℝ)⁻¹)^N)
      atTop (nhds ((b - a) / 2)) := by
    have hp : Tendsto (fun N : ℕ => ((2 : ℝ)⁻¹)^N) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using (hp.const_mul 2).const_add ((b - a) / 2)
  apply ge_of_tendsto ht
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact binaryTail_interval_bound a b hab N hN

/-- Exact values are null, including the ambiguous dyadic expansions. -/
lemma bitLaw_atomless (t : ℝ) : bitLaw (binaryTail 0 ⁻¹' {t}) = 0 := by
  have h := binaryTail_interval_le t t le_rfl
  rw [Set.Icc_self, sub_self, zero_div] at h
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
    (le_antisymm h measureReal_nonneg)

/-- The binary series has the distribution function of the uniform law. -/
lemma binaryTail_Iic_real (t : ℝ) :
    bitLaw.real (binaryTail 0 ⁻¹' Set.Iic t) =
      if t < -1 then 0 else if t < 1 then (t + 1) / 2 else 1 := by
  have hs (ε : BitSpace) : -1 ≤ binaryTail 0 ε ∧ binaryTail 0 ε ≤ 1 := by
    simpa using abs_le.mp (abs_binaryTail_le 0 ε)
  by_cases hleft : t < -1
  · have hempty : binaryTail 0 ⁻¹' Set.Iic t = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ε hε
      have : binaryTail 0 ε ≤ t := hε
      linarith [(hs ε).1]
    simp [hleft, hempty]
  · simp only [hleft, ite_false]
    by_cases hright : t < 1
    · simp only [hright, ite_true]
      have hpre : binaryTail 0 ⁻¹' Set.Iic t = binaryTail 0 ⁻¹' Set.Icc (-1) t := by
        ext ε
        exact ⟨fun h => ⟨(hs ε).1, h⟩, fun h => h.2⟩
      have hupper := binaryTail_interval_le (-1) t (not_lt.mp hleft)
      rw [← hpre] at hupper
      have hlower := binaryTail_interval_le t 1 hright.le
      have hcover : (binaryTail 0 ⁻¹' Set.Iic t) ∪
          (binaryTail 0 ⁻¹' Set.Icc t 1) = Set.univ := by
        apply Set.eq_univ_of_forall
        intro ε
        by_cases h : binaryTail 0 ε ≤ t
        · exact Or.inl h
        · exact Or.inr ⟨(not_le.mp h).le, (hs ε).2⟩
      have htotal := measureReal_union_le (μ := bitLaw)
        (binaryTail 0 ⁻¹' Set.Iic t) (binaryTail 0 ⁻¹' Set.Icc t 1)
      rw [hcover, probReal_univ] at htotal
      linarith
    · have huniv : binaryTail 0 ⁻¹' Set.Iic t = Set.univ := by
        apply Set.eq_univ_of_forall
        intro ε
        exact (hs ε).2.trans (not_lt.mp hright)
      simp [hright, huniv]

/-- Tail shift preserves the bit law (discarding the first `h` bits). -/
lemma shift_preserves_bitLaw (h : ℕ) :
    MeasurePreserving (fun ε : BitSpace => fun n : ℕ => ε (n + h)) bitLaw bitLaw := by
  have hmeas : Measurable (fun ε : BitSpace => fun n : ℕ => ε (n + h)) := by
    rw [measurable_pi_iff]
    intro n
    exact measurable_pi_apply _
  refine ⟨hmeas, ?_⟩
  unfold bitLaw
  have hinj : Function.Injective (fun n : ℕ => n + h) := fun a b hab => by
    simpa using hab
  have hmap := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ =>
    (PMF.uniformOfFintype Bool).toMeasure) hinj
  simpa using hmap

/-- Scaling: `binaryTail h = 2⁻ʰ • (binaryTail 0 ∘ shift)`. -/
lemma binaryTail_scale (h : ℕ) (ε : BitSpace) :
    binaryTail h ε = ((2 : ℝ)⁻¹) ^ h * binaryTail 0 (fun n : ℕ => ε (n + h)) := by
  unfold binaryTail
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [Nat.add_zero]
  simp only [div_eq_mul_inv, pow_add, mul_inv, inv_pow]
  ring

/-- Explicit CDF of a uniform interval (via volume). -/
lemma uniformInterval_Iic {a b t : ℝ} (hab : a < b) :
    uniformInterval a b (Set.Iic t)
      = if t < a then 0 else if t < b then ENNReal.ofReal ((t - a) / (b - a)) else 1 := by
  unfold uniformInterval
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hIcc : Set.Icc a b ∩ Set.Iic t
      = if t < a then ∅ else if t < b then Set.Icc a t else Set.Icc a b := by
    by_cases h1 : t < a
    · simp only [h1, ite_true]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic,
        Set.mem_empty_iff_false, iff_false]
      intro h
      exfalso
      linarith [h.1.1, h.2]
    · simp only [h1, ite_false]
      by_cases h2 : t < b
      · simp only [h2, ite_true]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
        constructor
        · exact fun h => ⟨h.1.1, h.2⟩
        · exact fun h => ⟨⟨h.1, le_trans h.2 (le_of_lt h2)⟩, h.2⟩
      · simp only [h2, ite_false]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
        constructor
        · exact fun h => h.1
        · exact fun h => ⟨h, le_trans h.2 (not_lt.mp h2)⟩
  rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Iic,
    Set.inter_comm _ _, hIcc]
  by_cases h1 : t < a
  · simp [h1]
  · simp only [h1, ite_false]
    by_cases h2 : t < b
    · simp only [h2, ite_true, smul_eq_mul, Real.volume_Icc]
      have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
      have hta : (0 : ℝ) ≤ t - a := sub_nonneg.mpr (not_lt.mp h1)
      rw [div_eq_mul_inv, ENNReal.ofReal_mul hta, ENNReal.ofReal_inv_of_pos hba]
      ring
    · simp only [h2, ite_false, smul_eq_mul, Real.volume_Icc]
      exact ENNReal.inv_mul_cancel (by simpa using hab) ENNReal.ofReal_ne_top

/-- The series of independent fair signs is uniform on `[-1,1]`
(paper `02-state.tex`, binary representation). -/
lemma map_binaryTail_zero :
    bitLaw.map (binaryTail 0) = uniformInterval (-1) 1 := by
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply (measurable_binaryTail 0) measurableSet_Iic,
    ← ofReal_measureReal (measure_ne_top _ _), binaryTail_Iic_real,
    uniformInterval_Iic (by norm_num : (-1 : ℝ) < 1)]
  by_cases hleft : t < -1
  · simp [hleft]
  · by_cases hright : t < 1 <;> simp [hleft, hright, one_add_one_eq_two]

/-- The binary series matches the real potential marginal of OAI's disorder law. -/
lemma binaryTail_matches_potential {d : ℕ} (x : OAI.Anderson.Site d) :
    bitLaw.map (binaryTail 0) = (OAI.Anderson.disorderLaw d).map
      (fun ω => OAI.Anderson.potential ω x) := by
  rw [map_binaryTail_zero, OAI.Anderson.potential_distribution]
  norm_num [uniformInterval]

/-- Pushforward scaling of uniform intervals (via CDFs on `Iic`). -/
lemma map_uniformInterval_mul {c a b : ℝ} (hc : 0 < c) (hab : a < b) :
    (uniformInterval a b).map (fun x => c * x) = uniformInterval (c * a) (c * b) := by
  have hcab : c * a < c * b := by
    have := mul_lt_mul_of_pos_left hab hc
    linarith
  have hfin : IsFiniteMeasure (uniformInterval a b) := by
    haveI := uniformInterval_probability hab
    infer_instance
  apply Measure.ext_of_Iic
  intro t
  have hmeas : Measurable (fun x : ℝ => c * x) := measurable_const_mul c
  rw [Measure.map_apply hmeas measurableSet_Iic]
  have hpre : (fun x : ℝ => c * x) ⁻¹' Set.Iic t = Set.Iic (t / c) := by
    ext x
    simp only [Set.mem_Iic, Set.mem_preimage]
    rw [le_div_iff₀ hc, mul_comm x c]
  rw [hpre, uniformInterval_Iic hab, uniformInterval_Iic hcab]
  by_cases h1 : t < c * a
  · have h1' : t / c < a := by
      rw [div_lt_iff₀ hc]
      linarith
    simp [h1, h1']
  · simp only [h1, ite_false]
    by_cases h2 : t < c * b
    · have h2' : t / c < b := by
        rw [div_lt_iff₀ hc]
        linarith
      have ha' : ¬ t / c < a := by
        intro hcon
        have hlt : t < a * c := (div_lt_iff₀ hc).mp hcon
        rw [mul_comm a c] at hlt
        exact h1 hlt
      simp only [ha', h2, h2', ite_true, ite_false]
      congr 1
      have hc' : c ≠ 0 := ne_of_gt hc
      have hba' : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
      field_simp
    · have h2' : ¬ t / c < b := by
        intro hcon
        have hlt : t < b * c := (div_lt_iff₀ hc).mp hcon
        rw [mul_comm b c] at hlt
        exact h2 hlt
      have ha'' : ¬ t / c < a := by
        intro hcon
        exact h2' (lt_trans hcon hab)
      simp [h2, h2', ha'']

/-- General-h series law (from h = 0 via shift preservation and scaling). -/
lemma map_binaryTail (h : ℕ) :
    bitLaw.map (binaryTail h)
      = uniformInterval (-((2 : ℝ)⁻¹ ^ h)) ((2 : ℝ)⁻¹ ^ h) := by
  set c : ℝ := ((2 : ℝ)⁻¹) ^ h with hcdef
  have hcpos : 0 < c := pow_pos (by norm_num) h
  have hfun : binaryTail h
      = fun ε : BitSpace => c * binaryTail 0 (fun n : ℕ => ε (n + h)) := by
    funext ε
    exact binaryTail_scale h ε
  have hshift := shift_preserves_bitLaw h
  have hmeas_shift : Measurable (fun ε : BitSpace => fun n : ℕ => ε (n + h)) :=
    hshift.measurable
  have hmeas_tail : Measurable (binaryTail (0 : ℕ)) := measurable_binaryTail 0
  have hmeas_mul : Measurable (fun x : ℝ => c * x) := measurable_const_mul c
  have hmeas_inner : Measurable
      (fun ε : BitSpace => binaryTail 0 (fun n : ℕ => ε (n + h))) :=
    hmeas_tail.comp hmeas_shift
  have e1 : (fun ε : BitSpace => c * binaryTail 0 (fun n : ℕ => ε (n + h)))
      = (fun x : ℝ => c * x) ∘ (fun ε : BitSpace => binaryTail 0 (fun n : ℕ => ε (n + h))) :=
    rfl
  have e2 : (fun ε : BitSpace => binaryTail 0 (fun n : ℕ => ε (n + h)))
      = binaryTail 0 ∘ (fun ε : BitSpace => fun n : ℕ => ε (n + h)) := rfl
  rw [hfun, e1, ← Measure.map_map hmeas_mul hmeas_inner,
    e2, ← Measure.map_map hmeas_tail hmeas_shift, hshift.map_eq, map_binaryTail_zero]
  have hscale := map_uniformInterval_mul (a := (-1 : ℝ)) (b := 1) hcpos (by norm_num)
  simpa [hcdef, mul_neg, mul_one] using hscale

/-- Prefix / tail independence (disjoint coordinate blocks). -/
lemma indepFun_prefix_tail (h : ℕ) :
    ProbabilityTheory.IndepFun
      (fun ε : BitSpace => fun i : Fin h => ε (i : ℕ)) (binaryTail h) bitLaw := by
  classical
  -- coordinate σ-algebras and their independence
  have hIndepFun := iIndepFun_bits
  have hiIndep : ProbabilityTheory.iIndep
      (fun i : ℕ => (inferInstance : MeasurableSpace Bool).comap (fun ε : BitSpace => ε i))
      bitLaw :=
    hIndepFun.iIndep
  set S_pre : Set ℕ := {i | i < h} with hSpre
  set S_tail : Set ℕ := {i | h ≤ i} with hStail
  have hdisj : Disjoint S_pre S_tail := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [S_pre, Set.mem_setOf_eq] at hx1
    simp only [S_tail, Set.mem_setOf_eq] at hx2
    omega
  have hIndep : ProbabilityTheory.Indep
      (MeasureTheory.cylinderEvents (X := fun _ : ℕ => Bool) S_pre)
      (MeasureTheory.cylinderEvents (X := fun _ : ℕ => Bool) S_tail) bitLaw :=
    ProbabilityTheory.indep_iSup_of_disjoint
      (fun i => (measurable_pi_apply i).comap_le) hiIndep hdisj
  -- prefix is measurable w.r.t. the prefix σ-algebra
  have hXmeas : @Measurable BitSpace (Fin h → Bool)
      (MeasureTheory.cylinderEvents (X := fun _ : ℕ => Bool) S_pre) _
      (fun ε : BitSpace => fun i : Fin h => ε (i : ℕ)) := by
    letI : MeasurableSpace BitSpace :=
      MeasureTheory.cylinderEvents (X := fun _ : ℕ => Bool) S_pre
    refine measurable_pi_iff.mpr fun i => ?_
    have hi : ((i : ℕ) : ℕ) ∈ S_pre := by
      simp [S_pre, i.isLt]
    exact MeasureTheory.measurable_cylinderEvent_apply hi
  -- tail is measurable w.r.t. the tail σ-algebra
  have hYmeas : @Measurable BitSpace ℝ
      (MeasureTheory.cylinderEvents (X := fun _ : ℕ => Bool) S_tail) _
      (binaryTail h) := by
    letI : MeasurableSpace BitSpace :=
      MeasureTheory.cylinderEvents (X := fun _ : ℕ => Bool) S_tail
    unfold binaryTail
    apply Measurable.tsum
    intro n
    have hn : n + h ∈ S_tail := by
      simp [S_tail, Nat.le_add_left]
    have h1 : Measurable (fun ε : BitSpace => ε (n + h)) :=
      MeasureTheory.measurable_cylinderEvent_apply hn
    have h2 : Measurable (fun b : Bool => (if b then (1 : ℝ) else -1)) :=
      Measurable.of_discrete
    exact (h2.comp h1).div_const _
  rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have hs' : @MeasurableSet BitSpace
      (MeasureTheory.cylinderEvents (X := fun _ : ℕ => Bool) S_pre)
      ((fun ε : BitSpace => fun i : Fin h => ε (i : ℕ)) ⁻¹' s) :=
    hXmeas hs
  have ht' : @MeasurableSet BitSpace
      (MeasureTheory.cylinderEvents (X := fun _ : ℕ => Bool) S_tail)
      ((binaryTail h) ⁻¹' t) :=
    hYmeas ht
  exact ((hIndep.indepSet_of_measurableSet hs' ht').measure_inter_eq_mul)

end

end AndersonAC.MuseProb

/-- WP04 `binary`: uniform binary tails and prefix independence (muse-prob). -/
theorem AndersonAC.Blueprint.Packages.binary :
    AndersonAC.Blueprint.BinaryInput := by
  intro h
  exact ⟨AndersonAC.MuseProb.measurable_binaryTail h,
    AndersonAC.MuseProb.map_binaryTail h,
    AndersonAC.MuseProb.indepFun_prefix_tail h⟩
