import AndersonAC.S2.SignResampling

/-! Independent random orders can be permuted on unexposed positions without
changing retained queries. The product law is preserved by every fixed action. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace AndersonAC.SolS2
open AndersonAC.S2
section Queries
variable (ι : Type*) [Fintype ι] [DecidableEq ι] {M : ℕ → ℕ}

def permuteOrders (τ : (o : ℕ) → Order (M o)) (π : (o : ℕ) → Order (M o)) :
    (o : ℕ) → Order (M o) := fun o => π o * τ o

def orderAction (τ : (o : ℕ) → Order (M o)) (ω : RandomSources ι M) : RandomSources ι M :=
  (ω.1, permuteOrders τ ω.2)

theorem permuteOrders_measurable (τ : (o : ℕ) → Order (M o)) : Measurable (permuteOrders τ) := by
  apply Measurable.of_eval
  intro o
  exact (measurable_from_top (f := fun π : Order (M o) => π * τ o)).comp (measurable_pi_apply o)

theorem orderAction_measurable (τ : (o : ℕ) → Order (M o)) : Measurable (orderAction ι τ) :=
  measurable_fst.prodMk ((permuteOrders_measurable τ).comp measurable_snd)

theorem permuteOrders_law (τ : (o : ℕ) → Order (M o)) :
    (ordersLaw M).map (permuteOrders τ) = ordersLaw M := by
  unfold ordersLaw permuteOrders
  rw [Measure.infinitePi_map_pi
    (fun o : ℕ => (PMF.uniformOfFintype (Order (M o))).toMeasure)
    (f := fun o π => π * τ o) (fun o => measurable_from_top)]
  congr 1
  funext o
  exact uniformFinite_map_equiv (Equiv.mulRight (τ o))

theorem orderAction_law (τ : (o : ℕ) → Order (M o)) :
    (sourcesLaw ι M).map (orderAction ι τ) = sourcesLaw ι M := by
  unfold sourcesLaw orderAction
  change ((signsLaw ι).prod (ordersLaw M)).map (Prod.map id (permuteOrders τ)) = _
  rw [← Measure.map_prod_map _ _ measurable_id (permuteOrders_measurable τ),
    Measure.map_id, permuteOrders_law]

theorem orderAction_inverse (τ : (o : ℕ) → Order (M o)) (ω : RandomSources ι M) :
    orderAction ι (fun o => (τ o)⁻¹) (orderAction ι τ ω) = ω := by
  apply Prod.ext
  · rfl
  · funext o
    exact mul_inv_cancel_right _ _

theorem orderAction_retained (Q : ℕ → RandomSources ι M → Query ι)
    (hQ : ObeysQueryRules ι Q) (q : ℕ) (ω : RandomSources ι M)
    (τ : (o : ℕ) → Order (M o))
    (hfix : ∀ o (j : Fin (M o)), j.val < orderCount ι Q q ω o → τ o j = j) :
    SameInformation (retained ι Q q) ω (orderAction ι τ ω) ∧
      queriedSigns ι Q q ω = queriedSigns ι Q q (orderAction ι τ ω) ∧
      ∀ o, orderCount ι Q q ω o = orderCount ι Q q (orderAction ι τ ω) o := by
  have hp := retained_query_replay ι Q hQ.1 q ω (orderAction ι τ ω)
    (fun x hx => rfl) (fun o j hj => by
      simp only [orderAction, permuteOrders, Equiv.Perm.mul_apply, hfix o j hj])
  refine ⟨transcript_sameInformation ι Q q hp.1 hp.2, ?_, ?_⟩
  · ext x
    simp only [queriedSigns, Set.mem_iUnion, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, hx⟩
      exact ⟨j, hj, by simpa only [← hp.1 j hj] using hx⟩
    · rintro ⟨j, hj, hx⟩
      exact ⟨j, hj, by simpa only [hp.1 j hj] using hx⟩
  · intro o
    unfold orderCount
    congr 1
    apply Finset.filter_congr
    intro j hj
    rw [hp.1 j (Finset.mem_range.mp hj)]

end Queries
end AndersonAC.SolS2
