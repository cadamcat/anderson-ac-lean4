import AndersonAC.S9Inf.HelperStatements

noncomputable section

open Filter OAI.Anderson
open scoped Topology ENNReal NNReal lp

namespace AndersonAC.SolS9Inf

private def finitePart {d : ℕ} (s : Finset (Site d)) (v : StateSpace d) :
    StateSpace d :=
  ⟨fun x => if x ∈ s then v x else 0,
    (lp.memℓp v).mono' (by
      intro x
      by_cases hx : x ∈ s <;> simp [hx])⟩

private def potentialTail {d : ℕ} (v : StateSpace d) (s : Finset (Site d)) : ℝ≥0 :=
  ∑' b : {x : Site d // x ∉ s}, ⟨‖v b.1‖ ^ 2, sq_nonneg _⟩

private lemma finitePart_error_apply {d : ℕ} (s : Finset (Site d))
    (v : StateSpace d) (x : Site d) :
    (v - finitePart s v) x = if x ∈ s then 0 else v x := by
  change v x - (if x ∈ s then v x else 0) = if x ∈ s then 0 else v x
  by_cases hx : x ∈ s <;> simp [hx]

set_option backward.isDefEq.respectTransparency false in
private lemma tsum_norm_sq_compl {d : ℕ} (v : StateSpace d) (s : Finset (Site d)) :
    (∑' b : {x : Site d // x ∉ s}, ‖v b.1‖ ^ 2) =
      ∑' x : Site d, ({x : Site d | x ∉ s}.indicator (fun x => ‖v x‖ ^ 2)) x := by
  exact tsum_subtype ({x : Site d | x ∉ s}) (fun x : Site d => ‖v x‖ ^ 2)

set_option backward.isDefEq.respectTransparency false in
private lemma finitePart_error_sq {d : ℕ} (v : StateSpace d) (s : Finset (Site d)) :
    ‖v - finitePart s v‖ ^ 2 = (potentialTail v s : ℝ) := by
  calc
    ‖v - finitePart s v‖ ^ 2 =
        ∑' x : Site d, ‖(v - finitePart s v) x‖ ^ 2 := by
      symm
      simpa using (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num)
        (v - finitePart s v)).tsum_eq
    _ = ∑' b : {x // x ∉ s}, ‖v b‖ ^ 2 := by
      symm
      rw [tsum_norm_sq_compl v s]
      apply tsum_congr
      intro x
      by_cases hx : x ∈ s <;>
        simp [Set.indicator, hx, finitePart_error_apply]
    _ = (potentialTail v s : ℝ) := by
      rw [potentialTail]
      calc
        _ = ∑' b : {x : Site d // x ∉ s},
            ((⟨‖v b.1‖ ^ 2, sq_nonneg _⟩ : ℝ≥0) : ℝ) := by
          apply tsum_congr
          intro b
          rfl
        _ = _ :=
          (NNReal.coe_tsum
            (L := SummationFilter.unconditional {x : Site d // x ∉ s})
            (f := fun b : {x : Site d // x ∉ s} =>
              ⟨‖v b.1‖ ^ 2, sq_nonneg _⟩)).symm

private lemma potentialOperator_finitePart_eq {d : ℕ} (s : Finset (Site d))
    (v : StateSpace d) (ω : Configuration d) :
    potentialOperator ω (finitePart s v) =
      ∑ x ∈ s, (potential ω x : ℂ) • lp.single 2 x (v x) := by
  ext y
  rw [potentialOperator_apply]
  simp only [finitePart, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul]
  by_cases hy : y ∈ s
  · rw [Finset.sum_eq_single y]
    all_goals simp_all [Pi.single, eq_comm]
  · have hsum : (∑ c ∈ s, (potential ω c : ℂ) *
        ((Pi.single c (v c) : Site d → ℂ) y)) = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      have hcy : y ≠ c := by
        intro h
        exact hy (h ▸ hc)
      simp [Pi.single, hcy]
    simp [hy, hsum]

private lemma continuous_potentialOperator_finitePart {d : ℕ}
    (s : Finset (Site d)) (v : StateSpace d) :
    Continuous (fun ω : Configuration d => potentialOperator ω (finitePart s v)) := by
  rw [show (fun ω : Configuration d => potentialOperator ω (finitePart s v)) =
      (fun ω => ∑ x ∈ s, (potential ω x : ℂ) • lp.single 2 x (v x)) from by
        funext ω
        exact potentialOperator_finitePart_eq s v ω]
  apply continuous_finsetSum
  intro x hx
  have hpotential : Continuous (fun ω : Configuration d => (potential ω x : ℂ)) := by
    change Continuous (fun ω : Configuration d => Complex.ofReal ((ω x : SingleSite) : ℝ))
    exact Complex.continuous_ofReal.comp
      (continuous_subtype_val.comp (continuous_apply x))
  exact ContinuousSMul.continuous_smul.comp
    (hpotential.prodMk continuous_const)

private lemma potential_finitePart_dist_le {d : ℕ} (s : Finset (Site d))
    (v : StateSpace d) (ω : Configuration d) :
    dist (potentialOperator ω v) (potentialOperator ω (finitePart s v)) ≤
      ‖v - finitePart s v‖ := by
  rw [dist_eq_norm]
  calc
    ‖potentialOperator ω v - potentialOperator ω (finitePart s v)‖ =
        ‖potentialOperator ω (v - finitePart s v)‖ := by rw [← map_sub]
    _ ≤ ‖potentialOperator ω‖ * ‖v - finitePart s v‖ :=
      (potentialOperator ω).le_opNorm _
    _ ≤ 1 * ‖v - finitePart s v‖ :=
      mul_le_mul_of_nonneg_right (norm_potentialOperator_le_one ω) (norm_nonneg _)
    _ = ‖v - finitePart s v‖ := one_mul _

theorem potentialStrongContinuity_proof : PotentialStrongContinuityStatement := by
  intro d v
  let tail : Finset (Site d) → ℝ≥0 := potentialTail v
  have htail : Tendsto tail atTop (𝓝 0) := by
    change Tendsto (potentialTail v) atTop (𝓝 0)
    exact NNReal.tendsto_tsum_compl_atTop_zero
      (fun x : Site d => ⟨‖v x‖ ^ 2, sq_nonneg _⟩)
  have htailReal : Tendsto (fun s => (tail s : ℝ)) atTop (𝓝 0) := by
    exact continuous_subtype_val.continuousAt.tendsto.comp htail
  have herror : Tendsto (fun s : Finset (Site d) => ‖v - finitePart s v‖)
      atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    let εsq : ℝ≥0 := ⟨ε ^ 2, sq_nonneg _⟩
    have hεsq : 0 < εsq := by
      dsimp [εsq]
      exact_mod_cast sq_pos_of_pos hε
    have hsmall : Set.Iio εsq ∈ 𝓝 (0 : ℝ≥0) := isOpen_Iio.mem_nhds hεsq
    filter_upwards [htail.eventually hsmall] with s hs
    have hs' : (tail s : ℝ) < ε ^ 2 := by
      exact_mod_cast hs
    simpa only [dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg (v - finitePart s v))] using
      (show ‖v - finitePart s v‖ < ε by nlinarith [finitePart_error_sq v s])
  have huniform : TendstoUniformly
      (fun s : Finset (Site d) => fun ω : Configuration d =>
        potentialOperator ω (finitePart s v))
      (fun ω : Configuration d => potentialOperator ω v) atTop := by
    rw [Filter.HasBasis.tendstoUniformly_iff_of_uniformity
      NormedAddCommGroup.uniformity_basis_dist]
    intro ε hε
    filter_upwards [herror.eventually (isOpen_Iio.mem_nhds hε)] with s hs ω
    simpa [dist_eq_norm] using (potential_finitePart_dist_le s v ω).trans_lt hs
  exact huniform.continuous (Frequently.of_forall fun s =>
    continuous_potentialOperator_finitePart s v)

#print axioms AndersonAC.SolS9Inf.potentialStrongContinuity_proof

end AndersonAC.SolS9Inf
