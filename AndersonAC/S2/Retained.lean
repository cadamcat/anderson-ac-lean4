import AndersonAC.S2.Definitions

/-! Retained-query replay. Agreement on everything observed through operation q
forces the same query transcript, even when an operation exposes a whole suffix.
This is the deterministic step needed before resampling untouched inputs. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace AndersonAC.S2

@[instance_reducible] def agreementSpace {Ω : Type*} (x y : Ω) : MeasurableSpace Ω where
  MeasurableSet' s := x ∈ s ↔ y ∈ s
  measurableSet_empty := Iff.rfl
  measurableSet_compl := fun s hs => not_congr hs
  measurableSet_iUnion := fun s hs => by
    simpa only [Set.mem_iUnion] using exists_congr hs

def SameInformation {Ω : Type*} (m : MeasurableSpace Ω) (x y : Ω) : Prop :=
  m ≤ agreementSpace x y

theorem sameInformation_comap {Ω X : Type*} [MeasurableSpace X]
    (f : Ω → X) {x y : Ω} (h : f x = f y) :
    SameInformation (MeasurableSpace.comap f inferInstance) x y := by
  intro D hD
  rcases hD with ⟨B, hB, rfl⟩
  change f x ∈ B ↔ f y ∈ B
  rw [h]

theorem sameInformation_measurable {Ω X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] {m : MeasurableSpace Ω} {x y : Ω}
    (h : SameInformation m x y) {f : Ω → X} (hf : @Measurable _ _ m inferInstance f) :
    f x = f y := by
  have hxy := h (f ⁻¹' {f x}) (hf (measurableSet_singleton (f x)))
  have hy : f y ∈ ({f x} : Set X) := hxy.mp (by rfl)
  exact (Set.mem_singleton_iff.mp hy).symm

theorem record_measurable_decision {Ω X : Type*} [MeasurableSpace X]
    (history : MeasurableSpace Ω) (f : Ω → X)
    (hf : @Measurable _ _ history inferInstance f) :
    history ⊔ MeasurableSpace.comap f inferInstance = history := by
  exact sup_eq_left.mpr hf.comap_le

section Queries
variable (ι : Type*) [Fintype ι] [DecidableEq ι] {M : ℕ → ℕ}

theorem retained_mono (Q : ℕ → RandomSources ι M → Query ι) :
    Monotone (retained ι Q) := by
  apply monotone_nat_of_le_succ
  intro q
  exact le_sup_left

theorem queriedSigns_mono (Q : ℕ → RandomSources ι M → Query ι)
    (ω : RandomSources ι M) : Monotone (fun q => queriedSigns ι Q q ω) := by
  intro q r hqr x hx
  simp only [queriedSigns, Set.mem_iUnion, Finset.mem_range] at hx ⊢
  obtain ⟨j, hj, hx⟩ := hx
  exact ⟨j, lt_of_lt_of_le hj hqr, hx⟩

theorem orderCount_mono (Q : ℕ → RandomSources ι M → Query ι)
    (ω : RandomSources ι M) (o : ℕ) : Monotone (fun q => orderCount ι Q q ω o) := by
  intro q r hqr
  apply Finset.card_le_card
  exact Finset.filter_subset_filter _ (Finset.range_mono hqr)

theorem transcript_sameInformation (Q : ℕ → RandomSources ι M → Query ι)
    (q : ℕ) {ω ω' : RandomSources ι M}
    (hQ : ∀ j < q, Q j ω = Q j ω')
    (hA : ∀ j < q, answer ι Q j ω = answer ι Q j ω') :
    SameInformation (retained ι Q q) ω ω' := by
  induction q with
  | zero => exact bot_le
  | succ q ih =>
    apply sup_le
    · exact ih (fun j hj => hQ j (by omega)) (fun j hj => hA j (by omega))
    · apply sameInformation_comap
      exact Prod.ext (hQ q (by omega)) (hA q (by omega))

/- This theorem has no probability hypothesis. Measurability makes the policy
constant on a retained transcript; no unobserved value can alter its next query. -/
theorem retained_query_replay (Q : ℕ → RandomSources ι M → Query ι)
    (hpolicy : ∀ q, @Measurable _ _ (retained ι Q q) inferInstance (Q q))
    (q : ℕ) (ω ω' : RandomSources ι M)
    (hsigns : ∀ x ∈ queriedSigns ι Q q ω, ω.1 x = ω'.1 x)
    (horders : ∀ o (j : Fin (M o)), j.val < orderCount ι Q q ω o → ω.2 o j = ω'.2 o j) :
    (∀ j < q, Q j ω = Q j ω') ∧
      (∀ j < q, answer ι Q j ω = answer ι Q j ω') := by
  classical
  induction q with
  | zero => exact ⟨by simp, by simp⟩
  | succ q ih =>
    have hold := ih
      (fun x hx => hsigns x (queriedSigns_mono ι Q ω (by omega) hx))
      (fun o j hj => horders o j (lt_of_lt_of_le hj (orderCount_mono ι Q ω o (by omega))))
    have hsame := transcript_sameInformation ι Q q hold.1 hold.2
    have hc : Q q ω = Q q ω' := sameInformation_measurable hsame (hpolicy q)
    have hcount : ∀ o, orderCount ι Q q ω o = orderCount ι Q q ω' o := by
      intro o
      unfold orderCount
      congr 1
      apply Finset.filter_congr
      intro j hj
      rw [hold.1 j (Finset.mem_range.mp hj)]
    have ha : answer ι Q q ω = answer ι Q q ω' := by
      apply Prod.ext
      · funext x
        change (if x ∈ querySigns ι (Q q ω) then some (ω.1 x) else none) =
          (if x ∈ querySigns ι (Q q ω') then some (ω'.1 x) else none)
        rw [← hc]
        split_ifs with hx
        · congr 1
          exact hsigns x (by simp only [queriedSigns, Set.mem_iUnion]; exact ⟨q, by simp, hx⟩)
        · rfl
      · unfold answer
        simp only [hc]
        cases he : Q q ω' with
        | nextOrder o =>
          simp only [hcount]
          split_ifs with hj
          · congr 2
            apply horders
            have hstep : orderCount ι Q (q + 1) ω o = orderCount ι Q q ω o + 1 := by
              unfold orderCount
              rw [Finset.range_add_one, Finset.filter_insert]
              simp only [hc, he, ite_true]
              apply Finset.card_insert_of_notMem
              simp
            change orderCount ι Q q ω' o < orderCount ι Q (q + 1) ω o
            have hc' := hcount o
            omega
          · rfl
        | trueDigit i k => rfl
        | auxiliary k => rfl
        | trueSuffix i h => rfl
        | decision => rfl
    constructor
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hold.1 j hj
      · exact hc
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hold.2 j hj
      · exact ha

end Queries
end AndersonAC.S2
