import AndersonAC.S2.SignResampling
import AndersonAC.S2.RetainedMeasurable

/-! Fair finite sign cylinders on events invariant under untouched-coordinate flips. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AndersonAC.SolS2
open AndersonAC.S2
section Queries
variable (ι : Type*) [Fintype ι] [DecidableEq ι] {M : ℕ → ℕ}

def finiteSignCylinder (s : Finset (SignIndex ι)) (a : s → Bool) : Set (RandomSources ι M) :=
  {ω | ∀ x : s, ω.1 x = a x}

theorem finiteSignCylinder_measurable (s : Finset (SignIndex ι)) (a : s → Bool) :
    MeasurableSet (finiteSignCylinder (M := M) ι s a) := by
  simp only [finiteSignCylinder, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro x
  have hf : Measurable (fun ω : RandomSources ι M => ω.1 x.val) :=
    (measurable_pi_apply x.val).comp measurable_fst
  exact hf (measurableSet_singleton (a x))

theorem finiteSignCylinder_probability_eq (s : Finset (SignIndex ι))
    (a b : s → Bool) (B : Set (RandomSources ι M)) (hB : MeasurableSet B)
    (hinv : ∀ mask : Set (SignIndex ι), mask ⊆ s → (signFlip ι mask) ⁻¹' B = B) :
    sourcesLaw ι M (B ∩ finiteSignCylinder ι s a) =
      sourcesLaw ι M (B ∩ finiteSignCylinder ι s b) := by
  classical
  let mask : Set (SignIndex ι) := {x | ∃ h : x ∈ s, a ⟨x, h⟩ ≠ b ⟨x, h⟩}
  have hsub : mask ⊆ s := by
    rintro x ⟨hx, hne⟩
    exact hx
  have hcyl : (signFlip (M := M) ι mask) ⁻¹' finiteSignCylinder ι s a = finiteSignCylinder ι s b := by
    ext ω
    simp only [Set.mem_preimage, finiteSignCylinder, Set.mem_ofPred_eq]
    apply forall_congr'
    intro x
    have hm : x.val ∈ mask ↔ a x ≠ b x := by
      constructor
      · rintro ⟨hx, hne⟩
        exact hne
      · intro hne
        exact ⟨x.property, hne⟩
    dsimp only [signFlip, flipSigns]
    simp only [hm]
    by_cases hab : a x = b x
    · simp [hab]
    · cases ha : a x <;> cases hb : b x <;> cases hw : ω.1 x.val <;> simp_all
  have heq := Measure.map_apply (μ := sourcesLaw ι M) (signFlip_measurable (M := M) ι mask)
    (hB.inter (finiteSignCylinder_measurable ι s a))
  rw [signFlip_law, Set.preimage_inter, hinv mask hsub, hcyl] at heq
  exact heq

theorem finiteSignCylinder_factor (s : Finset (SignIndex ι)) (a : s → Bool)
    (B : Set (RandomSources ι M)) (hB : MeasurableSet B)
    (hinv : ∀ mask : Set (SignIndex ι), mask ⊆ s → (signFlip ι mask) ⁻¹' B = B) :
    (sourcesLaw ι M (B ∩ finiteSignCylinder ι s a)).toReal =
      (2 : ℝ) ^ (-(s.card : ℤ)) * (sourcesLaw ι M B).toReal := by
  classical
  let C : (s → Bool) → Set (RandomSources ι M) := fun p => B ∩ finiteSignCylinder ι s p
  have hm : ∀ p : s → Bool, MeasurableSet (C p) :=
    fun p => hB.inter (finiteSignCylinder_measurable ι s p)
  have hd : Set.PairwiseDisjoint (Finset.univ : Finset (s → Bool)) C := by
    intro p hp r hr hpr
    apply Set.disjoint_left.mpr
    intro ω hωp hωr
    apply hpr
    funext x
    exact (hωp.2 x).symm.trans (hωr.2 x)
  have hcover : (⋃ p ∈ (Finset.univ : Finset (s → Bool)), C p) = B := by
    ext ω
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨p, hp, hω⟩
      exact hω.1
    · intro hω
      exact ⟨fun x => ω.1 x, Finset.mem_univ _, hω, fun x => rfl⟩
  have hsum : (sourcesLaw ι M B).toReal =
      ∑ p : s → Bool, (sourcesLaw ι M (C p)).toReal := by
    rw [← hcover, measure_biUnion_finset hd (fun p hp => hm p), ENNReal.toReal_sum]
    intro p hp
    exact measure_ne_top _ _
  have hequal : ∀ p : s → Bool, sourcesLaw ι M (C p) = sourcesLaw ι M (C a) := by
    intro p
    exact finiteSignCylinder_probability_eq ι s p a B hB hinv
  simp_rw [hequal] at hsum
  have hcard : Fintype.card (s → Bool) = 2 ^ s.card := by simp
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, Nat.cast_pow,
    Nat.cast_ofNat] at hsum
  rw [zpow_neg, zpow_natCast]
  change (sourcesLaw ι M (C a)).toReal = _
  rw [hsum]
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (2 : ℝ) ^ s.card ≠ 0), one_mul]

theorem signsUnqueried_measurable {Q : ℕ → RandomSources ι M → Query ι}
    (hQ : ObeysQueryRules ι Q) (q : ℕ) (s : Finset (SignIndex ι)) :
    MeasurableSet (signsUnqueried ι Q q s) := by
  have hglobal : ∀ j, Measurable (Q j) := fun j =>
    Measurable.of_comap_le ((hQ.1 j).comap_le.trans (retained_le ι hQ j))
  have hseen : ∀ x, MeasurableSet {ω | x ∈ queriedSigns ι Q q ω} := by
    intro x
    simp only [queriedSigns, Set.mem_iUnion, Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro j
    apply MeasurableSet.iUnion
    intro hj
    exact hglobal j (show MeasurableSet {c | x ∈ querySigns ι c} from trivial)
  simp only [signsUnqueried, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro x
  apply MeasurableSet.iInter
  intro hx
  exact (hseen x).compl

theorem orderCylinder_measurable (O : Finset ℕ) (b : (o : ℕ) → Order (M o)) :
    MeasurableSet (orderCylinder (M := M) ι O b) := by
  simp only [orderCylinder, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro o
  apply MeasurableSet.iInter
  intro ho
  change MeasurableSet {ω : RandomSources ι M | ω.2 o = b o}
  have hf : Measurable (fun ω : RandomSources ι M => ω.2 o) :=
    (measurable_pi_apply o).comp measurable_snd
  exact hf (show MeasurableSet {b o} from trivial)

theorem signFlip_fresh_iff {Q : ℕ → RandomSources ι M → Query ι}
    (hQ : ObeysQueryRules ι Q) (q : ℕ) (s : Finset (SignIndex ι))
    (mask : Set (SignIndex ι)) (hmask : mask ⊆ s) (ω : RandomSources ι M) :
    signFlip ι mask ω ∈ signsUnqueried ι Q q s ↔ ω ∈ signsUnqueried ι Q q s := by
  have hforward : ∀ ω : RandomSources ι M, ω ∈ signsUnqueried ι Q q s →
      signFlip ι mask ω ∈ signsUnqueried ι Q q s := by
    intro ω hω
    have hd : Disjoint mask (queriedSigns ι Q q ω) := Set.disjoint_left.mpr (by
      intro x hx hseen
      exact hω x (hmask hx) hseen)
    have heq := (signFlip_retained ι Q hQ q ω mask hd).2
    intro x hx hseen
    exact hω x hx (heq.symm ▸ hseen)
  constructor
  · intro hω
    have h := hforward (signFlip ι mask ω) hω
    simpa only [signFlip_involutive ι mask ω] using h
  · exact hforward ω

theorem unqueried_sign_cylinder {Q : ℕ → RandomSources ι M → Query ι}
    (hQ : ObeysQueryRules ι Q) (q : ℕ)
    (D : Set (RandomSources ι M)) (hD : MeasurableSet[retained ι Q q] D)
    (s : Finset (SignIndex ι)) (a : SignIndex ι → Bool)
    (O : Finset ℕ) (b : (o : ℕ) → Order (M o)) :
    (sourcesLaw ι M (D ∩ signsUnqueried ι Q q s ∩ signCylinder ι s a ∩ orderCylinder ι O b)).toReal =
      (2 : ℝ) ^ (-(s.card : ℤ)) *
        (sourcesLaw ι M (D ∩ signsUnqueried ι Q q s ∩ orderCylinder ι O b)).toReal := by
  let B := D ∩ signsUnqueried ι Q q s ∩ orderCylinder ι O b
  have hB : MeasurableSet B :=
    ((retained_le ι hQ q D hD).inter (signsUnqueried_measurable ι hQ q s)).inter
      (orderCylinder_measurable ι O b)
  have hinv : ∀ mask : Set (SignIndex ι), mask ⊆ s → (signFlip ι mask) ⁻¹' B = B := by
    intro mask hmask
    ext ω
    have hfr := signFlip_fresh_iff ι hQ q s mask hmask ω
    have hor : signFlip ι mask ω ∈ orderCylinder ι O b ↔ ω ∈ orderCylinder ι O b := Iff.rfl
    by_cases hf : ω ∈ signsUnqueried ι Q q s
    · have hd : Disjoint mask (queriedSigns ι Q q ω) := Set.disjoint_left.mpr (by
        intro x hx hseen
        exact hf x (hmask hx) hseen)
      have hi := (signFlip_retained ι Q hQ q ω mask hd).1
      have hdd : signFlip ι mask ω ∈ D ↔ ω ∈ D := (hi D hD).symm
      change ((signFlip ι mask ω ∈ D ∧ signFlip ι mask ω ∈ signsUnqueried ι Q q s) ∧
        signFlip ι mask ω ∈ orderCylinder ι O b) ↔
        ((ω ∈ D ∧ ω ∈ signsUnqueried ι Q q s) ∧ ω ∈ orderCylinder ι O b)
      rw [hdd, hfr, hor]
    · have hff : signFlip ι mask ω ∉ signsUnqueried ι Q q s := mt hfr.mp hf
      change ((signFlip ι mask ω ∈ D ∧ signFlip ι mask ω ∈ signsUnqueried ι Q q s) ∧
        signFlip ι mask ω ∈ orderCylinder ι O b) ↔
        ((ω ∈ D ∧ ω ∈ signsUnqueried ι Q q s) ∧ ω ∈ orderCylinder ι O b)
      simp only [hf, hff, and_false, false_and]
  have hcyl : finiteSignCylinder (M := M) ι s (fun x => a x.val) = signCylinder ι s a := by
    ext ω
    constructor
    · intro h x hx
      exact h ⟨x, hx⟩
    · intro h x
      exact h x.val x.property
  have hfactor := finiteSignCylinder_factor ι s (fun x => a x.val) B hB hinv
  rw [hcyl] at hfactor
  simpa only [B, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hfactor

end Queries
end AndersonAC.SolS2
