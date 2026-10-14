import AndersonAC.S2.OrderResampling
import AndersonAC.S2.SignFreshness
import AndersonAC.S2.OrderCompletionStatement

/-! Universe-general order completion for the original S2 endpoints.
Adapted from the checked S2Order helper at 144d8fe. The frozen helper contract
remains unchanged. This namespace keeps its counting helpers compatible with
the independent stopped-freshness helper's public names. -/

noncomputable section
open MeasureTheory AndersonAC.S2
open scoped Classical ENNReal

namespace AndersonAC.SolS2.OrderCompletionCore
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ → ℕ}

theorem remaining_card_aux (m r : ℕ) (hr : r ≤ m) :
    Fintype.card { j : Fin m // r ≤ j.val } = m - r := by
  classical
  have hequiv : { j : Fin m // r ≤ j.val } ≃ Fin (m - r) :=
    { toFun := fun j => ⟨j.val.val - r, by
        have hj1 : j.val.val < m := j.val.isLt
        have hj2 : r ≤ j.val.val := j.property
        omega⟩
      invFun := fun k => ⟨⟨r + k.val, by have hk := k.isLt; omega⟩, Nat.le_add_right r k.val⟩
      left_inv := by
        intro j
        obtain ⟨j, hj⟩ := j
        simp only
        apply Subtype.ext
        apply Fin.ext
        simp only
        omega
      right_inv := by intro k; simp }
  rw [Fintype.card_congr hequiv, Fintype.card_fin]

def StabN (m r : ℕ) : Type := { τ : Equiv.Perm (Fin m) // ∀ j : Fin m, ¬ r ≤ j.val → τ j = j }

instance StabN.fintype (m r : ℕ) : Fintype (StabN m r) := by
  classical
  unfold StabN
  infer_instance

theorem StabN.card_eq (m r : ℕ) (hr : r ≤ m) :
    Fintype.card (StabN m r) = (m - r).factorial := by
  classical
  have hequiv : StabN m r ≃ Equiv.Perm { j : Fin m // r ≤ j.val } :=
    (Equiv.Perm.subtypeEquivSubtypePerm (fun j : Fin m => r ≤ j.val)).symm
  rw [Fintype.card_congr hequiv, Fintype.card_perm, remaining_card_aux m r hr]

def StabProd (M : ℕ → ℕ) (O : Finset ℕ) (r : (o : ℕ) → ℕ) : Type :=
  (o : O) → StabN (M o.val) (r o.val)

instance StabProd.fintype (M : ℕ → ℕ) (O : Finset ℕ) (r : (o : ℕ) → ℕ) :
    Fintype (StabProd M O r) := by
  classical
  unfold StabProd
  infer_instance

theorem StabProd.card_eq (M : ℕ → ℕ) (O : Finset ℕ) (r : (o : ℕ) → ℕ)
    (hr : ∀ o ∈ O, r o ≤ M o) :
    Fintype.card (StabProd M O r) = ∏ o ∈ O, (M o - r o).factorial := by
  classical
  unfold StabProd
  rw [Fintype.card_pi]
  have hcoe : (∏ i : O, Fintype.card (StabN (M (↑i : ℕ)) (r (↑i : ℕ))))
      = (∏ o ∈ O, Fintype.card (StabN (M o) (r o))) :=
    Finset.prod_coe_sort O (fun o => Fintype.card (StabN (M o) (r o)))
  rw [hcoe]
  apply Finset.prod_congr rfl
  intro o ho
  exact StabN.card_eq (M o) (r o) (hr o ho)


theorem orderCount_succ_eq (Q : ℕ → RandomSources ι M → Query ι) (q : ℕ)
    (ω : RandomSources ι M) (o : ℕ) :
    orderCount ι Q (q + 1) ω o =
      orderCount ι Q q ω o + (if Q q ω = Query.nextOrder o then 1 else 0) := by
  classical
  unfold orderCount
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : Q q ω = Query.nextOrder o
  · simp only [h, ite_true]
    have hnot : q ∉ (Finset.range q).filter (fun j => Q j ω = Query.nextOrder o) := by
      simp only [Finset.mem_filter, Finset.mem_range, not_and]
      intro _; omega
    rw [Finset.card_insert_of_notMem hnot]
  · simp [h]


theorem orderCount_le_M (Q : ℕ → RandomSources ι M → Query ι)
    (hQ : ObeysQueryRules ι Q) (q : ℕ) (ω : RandomSources ι M) (o : ℕ) :
    orderCount ι Q q ω o ≤ M o := by
  induction q generalizing ω with
  | zero => unfold orderCount; simp
  | succ q ih =>
    rw [orderCount_succ_eq]
    by_cases h : Q q ω = Query.nextOrder o
    · simp only [h, ite_true]
      have hlt : orderCount ι Q q ω o < M o := hQ.2.2 q ω o h
      omega
    · simp only [h, ite_false, add_zero]
      exact ih ω


theorem Q_prod_meas (Q : ℕ → RandomSources ι M → Query ι)
    (hQ : ObeysQueryRules ι Q) (j : ℕ) : Measurable (Q j) :=
  ((hQ.1) j).mono (retained_le ι hQ j) le_rfl

theorem countProfile_prod_meas (Q : ℕ → RandomSources ι M → Query ι)
    (hQ : ObeysQueryRules ι Q) (q : ℕ) (O : Finset ℕ) (r : ℕ → ℕ) :
    MeasurableSet {ω : RandomSources ι M | ∀ o ∈ O, orderCount ι Q q ω o = r o} := by
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro o
  apply MeasurableSet.iInter
  intro _
  exact (orderCount_measurable ι Q q o (fun j _ => Q_prod_meas Q hQ j))
    (measurableSet_singleton _)

def extendStab {O : Finset ℕ} {r : ℕ → ℕ} (τ : StabProd M O r) :
    (o : ℕ) → Order (M o) := by
  classical
  exact fun o => if h : o ∈ O then (τ ⟨o, h⟩).val else 1

def inverseStab {O : Finset ℕ} {r : ℕ → ℕ} (τ : StabProd M O r) :
    StabProd M O r := fun o => ⟨(τ o).val⁻¹, by
      intro j hj
      apply (τ o).val.injective
      simpa using ((τ o).property j hj).symm⟩

theorem extendStab_inverse {O : Finset ℕ} {r : ℕ → ℕ} (τ : StabProd M O r) :
    extendStab (inverseStab τ) = fun o => (extendStab τ o)⁻¹ := by
  classical
  funext o
  by_cases ho : o ∈ O <;> simp [extendStab, inverseStab, ho]

def profilePart (Q : ℕ → RandomSources ι M → Query ι) (q : ℕ)
    (D : Set (RandomSources ι M)) (s : Finset (SignIndex ι))
    (O : Finset ℕ) (r : ℕ → ℕ) : Set (RandomSources ι M) :=
  {ω | ∀ o ∈ O, orderCount ι Q q ω o = r o} ∩ (D ∩ signsUnqueried ι Q q s)

theorem profilePart_measurable (Q : ℕ → RandomSources ι M → Query ι)
    (hQ : ObeysQueryRules ι Q) (q : ℕ) (D : Set (RandomSources ι M))
    (hD : MeasurableSet[retained ι Q q] D) (s : Finset (SignIndex ι))
    (O : Finset ℕ) (r : ℕ → ℕ) : MeasurableSet (profilePart Q q D s O r) :=
  (countProfile_prod_meas Q hQ q O r).inter
    ((retained_le ι hQ q D hD).inter (signsUnqueried_measurable ι hQ q s))

theorem profilePart_forward (Q : ℕ → RandomSources ι M → Query ι)
    (hQ : ObeysQueryRules ι Q) (q : ℕ) (D : Set (RandomSources ι M))
    (hD : MeasurableSet[retained ι Q q] D) (s : Finset (SignIndex ι))
    (O : Finset ℕ) (r : ℕ → ℕ) (τ : StabProd M O r)
    (ω : RandomSources ι M) (hω : ω ∈ profilePart Q q D s O r) :
    orderAction ι (extendStab τ) ω ∈ profilePart Q q D s O r := by
  classical
  have hfix : ∀ o (j : Fin (M o)), j.val < orderCount ι Q q ω o → extendStab τ o j = j := by
    intro o j hj
    by_cases ho : o ∈ O
    · simp only [extendStab, dite_eq_left ho]
      apply (τ ⟨o, ho⟩).property
      change ¬ r o ≤ j.val
      rw [hω.1 o ho] at hj
      omega
    · simp [extendStab, ho]
  have hi := orderAction_retained ι Q hQ q ω (extendStab τ) hfix
  refine ⟨fun o ho => (hi.2.2 o).symm.trans (hω.1 o ho),
    (hi.1 D hD).mp hω.2.1, ?_⟩
  intro x hx
  rw [← hi.2.1]
  exact hω.2.2 x hx

theorem profilePart_preimage (Q : ℕ → RandomSources ι M → Query ι)
    (hQ : ObeysQueryRules ι Q) (q : ℕ) (D : Set (RandomSources ι M))
    (hD : MeasurableSet[retained ι Q q] D) (s : Finset (SignIndex ι))
    (O : Finset ℕ) (r : ℕ → ℕ) (τ : StabProd M O r) :
    orderAction ι (extendStab τ) ⁻¹' profilePart Q q D s O r = profilePart Q q D s O r := by
  ext ω
  constructor
  · intro hω
    have h := profilePart_forward Q hQ q D hD s O r (inverseStab τ) _ hω
    rwa [extendStab_inverse, orderAction_inverse] at h
  · exact profilePart_forward Q hQ q D hD s O r τ ω

def prefixCompatible (O : Finset ℕ) (r : ℕ → ℕ) (b : (o : ℕ) → Order (M o))
    (ω : RandomSources ι M) : Prop :=
  ∀ o ∈ O, ∀ j : Fin (M o), j.val < r o → b o j = ω.2 o j

theorem orbit_compatible {O : Finset ℕ} {r : ℕ → ℕ} {b : (o : ℕ) → Order (M o)}
    {ω : RandomSources ι M} (τ : StabProd M O r)
    (h : orderAction ι (extendStab τ) ω ∈ orderCylinder ι O b) :
    prefixCompatible O r b ω := by
  classical
  intro o ho j hj
  have he := congrArg (fun π : Order (M o) => π j) (h o ho)
  have hfix : (τ ⟨o, ho⟩).val j = j :=
    (τ ⟨o, ho⟩).property j (show ¬ r o ≤ j.val by omega)
  simpa only [orderAction, permuteOrders, extendStab, dite_eq_left ho,
    Equiv.Perm.mul_apply, hfix] using he.symm

theorem orbit_count (O : Finset ℕ) (r : ℕ → ℕ) (b : (o : ℕ) → Order (M o))
    (ω : RandomSources ι M) :
    (∑ τ : StabProd M O r, if orderAction ι (extendStab τ) ω ∈ orderCylinder ι O b
      then (1 : ℝ) else 0) = if prefixCompatible O r b ω then 1 else 0 := by
  classical
  by_cases hp : prefixCompatible O r b ω
  · let τ₀ : StabProd M O r := fun o => ⟨(ω.2 o)⁻¹ * b o, by
      intro j hj
      simp only [Equiv.Perm.mul_apply]
      rw [hp o.val o.property j (by omega)]
      simp⟩
    have hwin : orderAction ι (extendStab τ₀) ω ∈ orderCylinder ι O b := by
      intro o ho
      change ω.2 o * extendStab τ₀ o = b o
      simp [extendStab, ho, τ₀]
    have huniq : ∀ τ : StabProd M O r,
        orderAction ι (extendStab τ) ω ∈ orderCylinder ι O b → τ = τ₀ := by
      intro τ hτ
      funext o
      apply Subtype.ext
      have he := hτ o.val o.property
      change ω.2 o * extendStab τ o = b o at he
      simp only [extendStab, dite_eq_left o.property] at he
      change (τ o).val = (ω.2 o)⁻¹ * b o
      rw [← he]
      group
    rw [ite_eq_left hp, Finset.sum_eq_single τ₀]
    · simp [hwin]
    · intro τ hτ hne
      exact ite_eq_right (fun h => hne (huniq τ h))
    · simp
  · rw [ite_eq_right hp]
    apply Finset.sum_eq_zero
    intro τ hτ
    exact ite_eq_right (fun h => hp (orbit_compatible τ h))

theorem completionWeight_profile (Q : ℕ → RandomSources ι M → Query ι) (q : ℕ)
    (O : Finset ℕ) (r : ℕ → ℕ) (hr : ∀ o ∈ O, r o ≤ M o)
    (b : (o : ℕ) → Order (M o)) (ω : RandomSources ι M)
    (hω : ∀ o ∈ O, orderCount ι Q q ω o = r o) :
    completionWeight ι Q q O b ω =
      (Fintype.card (StabProd M O r) : ℝ)⁻¹ *
        (∑ τ : StabProd M O r, if orderAction ι (extendStab τ) ω ∈ orderCylinder ι O b
          then (1 : ℝ) else 0) := by
  classical
  rw [orbit_count, StabProd.card_eq M O r hr]
  unfold completionWeight
  simp_rw [Nat.cast_prod]
  by_cases hp : prefixCompatible O r b ω
  · rw [ite_eq_left hp, mul_one, ← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro o ho
    rw [hω o ho, ite_eq_left (hp o ho)]
  · rw [ite_eq_right hp, mul_zero]
    unfold prefixCompatible at hp
    push Not at hp
    obtain ⟨o, ho, j, hj, hne⟩ := hp
    apply Finset.prod_eq_zero ho
    rw [hω o ho, ite_eq_right (by intro h; exact hne (h j hj))]


theorem finite_action_average {Ω G : Type*} [MeasurableSpace Ω] [Fintype G]
    [Nonempty G] (μ : Measure Ω) [IsFiniteMeasure μ]
    (φ : G → Ω → Ω) (hφ : ∀ g, Measurable (φ g))
    (hlaw : ∀ g, μ.map (φ g) = μ)
    (A C : Set Ω) (hA : MeasurableSet A) (hC : MeasurableSet C)
    (hinv : ∀ g, φ g ⁻¹' A = A) (w : Ω → ℝ)
    (hw : ∀ ω ∈ A, w ω = (Fintype.card G : ℝ)⁻¹ *
      ∑ g : G, if φ g ω ∈ C then (1 : ℝ) else 0) :
    Integrable (A.indicator w) μ ∧ (μ (A ∩ C)).toReal = ∫ ω in A, w ω ∂μ := by
  classical
  let f : G → Ω → ℝ := fun g => (φ g ⁻¹' (A ∩ C)).indicator (fun _ => 1)
  have hfi : ∀ g, Integrable (f g) μ := fun g =>
    (integrable_const (1 : ℝ)).indicator ((hA.inter hC).preimage (hφ g))
  have heq : A.indicator w = fun ω => (Fintype.card G : ℝ)⁻¹ * ∑ g : G, f g ω := by
    funext ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, hw ω hω]
      congr 1
      apply Finset.sum_congr rfl
      intro g hg
      have hfg : φ g ω ∈ A := by
        change ω ∈ φ g ⁻¹' A
        rw [hinv g]
        exact hω
      simp [f, Set.indicator, hfg]
    · rw [Set.indicator_of_notMem hω]
      have hz : ∀ g, f g ω = 0 := by
        intro g
        have hfg : φ g ω ∉ A := by
          change ω ∉ φ g ⁻¹' A
          rw [hinv g]
          exact hω
        simp [f, Set.indicator, hfg]
      simp [hz]
  have hmeas : ∀ g, μ (φ g ⁻¹' (A ∩ C)) = μ (A ∩ C) := by
    intro g
    have h := Measure.map_apply (μ := μ) (hφ g) (hA.inter hC)
    rw [hlaw g] at h
    exact h.symm
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact (integrable_finsetSum Finset.univ (fun g hg => hfi g)).const_mul _
  · rw [← integral_indicator hA, heq, integral_const_mul,
      integral_finsetSum Finset.univ (fun g hg => hfi g)]
    have hfint : ∀ g, (∫ ω, f g ω ∂μ) = (μ (A ∩ C)).toReal := by
      intro g
      dsimp only [f]
      rw [integral_indicator_const (1 : ℝ) ((hA.inter hC).preimage (hφ g)),
        smul_eq_mul, mul_one]
      change (μ (φ g ⁻¹' (A ∩ C))).toReal = _
      rw [hmeas g]
    simp_rw [hfint]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hc : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

instance StabN.nonempty (m r : ℕ) : Nonempty (StabN m r) :=
  ⟨⟨1, fun _ _ => rfl⟩⟩

instance StabProd.nonempty (M : ℕ → ℕ) (O : Finset ℕ) (r : ℕ → ℕ) :
    Nonempty (StabProd M O r) := ⟨fun _ => ⟨1, fun _ _ => rfl⟩⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ → ℕ}

theorem profile_average (Q : ℕ → RandomSources ι M → Query ι)
    (hQ : ObeysQueryRules ι Q) (q : ℕ) (D : Set (RandomSources ι M))
    (hD : MeasurableSet[retained ι Q q] D) (s : Finset (SignIndex ι))
    (O : Finset ℕ) (r : ℕ → ℕ) (hr : ∀ o ∈ O, r o ≤ M o)
    (b : (o : ℕ) → Order (M o)) :
    Integrable ((profilePart Q q D s O r).indicator (completionWeight ι Q q O b))
        (sourcesLaw ι M) ∧
      (sourcesLaw ι M (profilePart Q q D s O r ∩ orderCylinder ι O b)).toReal =
        ∫ ω in profilePart Q q D s O r, completionWeight ι Q q O b ω ∂sourcesLaw ι M := by
  exact finite_action_average (sourcesLaw ι M)
    (fun τ : StabProd M O r => orderAction ι (extendStab τ))
    (fun τ => orderAction_measurable ι _) (fun τ => orderAction_law ι _)
    _ _ (profilePart_measurable Q hQ q D hD s O r) (orderCylinder_measurable ι O b)
    (fun τ => profilePart_preimage Q hQ q D hD s O r τ) _
    (fun ω hω => completionWeight_profile Q q O r hr b ω hω.1)


theorem order_completion (Q : ℕ → RandomSources ι M → Query ι)
    (hQ : ObeysQueryRules ι Q) (q : ℕ) (D : Set (RandomSources ι M))
    (hD : MeasurableSet[retained ι Q q] D) (s : Finset (SignIndex ι))
    (O : Finset ℕ) (b : (o : ℕ) → Order (M o)) :
    (sourcesLaw ι M (D ∩ signsUnqueried ι Q q s ∩ orderCylinder ι O b)).toReal =
      ∫ ω in D ∩ signsUnqueried ι Q q s,
        completionWeight ι Q q O b ω ∂sourcesLaw ι M := by
  classical
  let P := (o : O) → Fin (M o.val + 1)
  let r : P → ℕ → ℕ := fun p o => if h : o ∈ O then (p ⟨o, h⟩).val else 0
  let A : P → Set (RandomSources ι M) := fun p => profilePart Q q D s O (r p)
  let B := D ∩ signsUnqueried ι Q q s
  let C := orderCylinder (M := M) ι O b
  let w := completionWeight ι Q q O b
  let pω : RandomSources ι M → P := fun ω o =>
    ⟨orderCount ι Q q ω o.val, Nat.lt_succ_of_le (orderCount_le_M Q hQ q ω o.val)⟩
  have hr : ∀ p : P, ∀ o ∈ O, r p o ≤ M o := by
    intro p o ho
    simp only [r, dite_eq_left ho]
    exact Nat.le_of_lt_succ (p ⟨o, ho⟩).isLt
  have hm : ∀ p : P, MeasurableSet (A p) :=
    fun p => profilePart_measurable Q hQ q D hD s O (r p)
  have hc : MeasurableSet C := orderCylinder_measurable ι O b
  have hp : ∀ (ω : RandomSources ι M) (p : P), ω ∈ A p ↔ ω ∈ B ∧ p = pω ω := by
    intro ω p
    constructor
    · intro h
      refine ⟨h.2, ?_⟩
      funext o
      apply Fin.ext
      have he := h.1 o.val o.property
      simpa only [r, dite_eq_left o.property, pω] using he.symm
    · rintro ⟨h, rfl⟩
      refine ⟨?_, h⟩
      intro o ho
      simp [r, ho, pω]
  have hd : Set.PairwiseDisjoint (Finset.univ : Finset P) A := by
    intro p hp' p' hp'' hne
    apply Set.disjoint_left.mpr
    intro ω hω hω'
    exact hne (((hp ω p).mp hω).2.trans (((hp ω p').mp hω').2.symm))
  have hcover : (⋃ p ∈ (Finset.univ : Finset P), A p) = B := by
    ext ω
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨p, hpu, hω⟩
      exact ((hp ω p).mp hω).1
    · intro hω
      exact ⟨pω ω, Finset.mem_univ _, (hp ω _).mpr ⟨hω, rfl⟩⟩
  have hcoverC : (⋃ p ∈ (Finset.univ : Finset P), A p ∩ C) = B ∩ C := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨p, hp', hω, hωC⟩
      exact ⟨((hp ω p).mp hω).1, hωC⟩
    · rintro ⟨hω, hωC⟩
      exact ⟨pω ω, Finset.mem_univ _, (hp ω _).mpr ⟨hω, rfl⟩, hωC⟩
  have hdC : Set.PairwiseDisjoint (Finset.univ : Finset P) (fun p => A p ∩ C) := by
    intro p hp' p' hp'' hne
    exact (hd hp' hp'' hne).mono Set.inter_subset_left Set.inter_subset_left
  have havg : ∀ p : P, Integrable ((A p).indicator w) (sourcesLaw ι M) ∧
      (sourcesLaw ι M (A p ∩ C)).toReal = ∫ ω in A p, w ω ∂sourcesLaw ι M :=
    fun p => profile_average Q hQ q D hD s O (r p) (hr p) b
  have hsum : (sourcesLaw ι M (B ∩ C)).toReal =
      ∑ p : P, (sourcesLaw ι M (A p ∩ C)).toReal := by
    rw [← hcoverC, measure_biUnion_finset hdC (fun p hp' => (hm p).inter hc),
      ENNReal.toReal_sum]
    intro p hp'
    exact measure_ne_top _ _
  change (sourcesLaw ι M (B ∩ C)).toReal = ∫ ω in B, w ω ∂sourcesLaw ι M
  rw [hsum, ← hcover]
  rw [integral_biUnion_finset Finset.univ (fun p hp' => hm p) hd]
  · apply Finset.sum_congr rfl
    intro p hp'
    exact (havg p).2
  · intro p hp'
    exact (integrable_indicator_iff (hm p)).mp (havg p).1


end AndersonAC.SolS2.OrderCompletionCore

namespace AndersonAC.SolS2
open AndersonAC.S2
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ → ℕ}

theorem order_completion (Q : ℕ → RandomSources ι M → Query ι)
    (hQ : ObeysQueryRules ι Q) (q : ℕ) (D : Set (RandomSources ι M))
    (hD : MeasurableSet[retained ι Q q] D) (s : Finset (SignIndex ι))
    (O : Finset ℕ) (b : (o : ℕ) → Order (M o)) :
    (sourcesLaw ι M (D ∩ signsUnqueried ι Q q s ∩ orderCylinder ι O b)).toReal =
      ∫ ω in D ∩ signsUnqueried ι Q q s,
        completionWeight ι Q q O b ω ∂sourcesLaw ι M :=
  OrderCompletionCore.order_completion Q hQ q D hD s O b

end AndersonAC.SolS2
