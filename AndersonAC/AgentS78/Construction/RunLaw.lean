import AndersonAC.S78.Statements

/-!
# the law of one finite-volume run

`RunLaw d m n₀ u E …` records, for one fixed finite volume `m`, starting index `n₀`,
coupling parameter `u` and energy `E`, exactly what §8 uses from the random multiscale
construction (08-history.tex:296–400):

* an enlarged probability space whose true potential has the product law `torusLaw d m`
  as its unconditional marginal (02-state.tex:68–72, 08-history.tex:396–400);
* the pending-site history (`PendingHistory`, 08-history.tex:37–131) with the joint
  chronological birth bound (history-joint);
* the deterministic list of late tile trials after the cutoff `J = ⌊m/2⌋`, each failing
  with probability at most `p_J` (history-late-failure);
* the success event: every failure of the run is a pending site at the cutoff or a late
  failure (the two abort rules, 02-state.tex:357–362), and on success the true variables
  lie in the bounded certificate event (completion proof, 08-history.tex:370–394).

`uniformCertificateInput_of_runLaw` proves `S78.UniformCertificateInput` from such runs
with uniform constants. It uses only the proved §8 bounds `pending_site_bound`,
`cutoff_probability_bound`, `late_failure_bound`, `uniform_abort_bound` and
`success_projects_to_true_law`.
-/

open scoped BigOperators ENNReal
open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- The law of one finite-volume run of the random multiscale construction. -/
structure RunLaw (d m n₀ : ℕ) (u E Cr cp cg Ch c Clate : ℝ) (Ω : Type) [MeasurableSpace Ω] where
  μ : Measure Ω
  prob : IsProbabilityMeasure μ
  trueConfig : Ω → OAI.Anderson.TorusConfiguration d m
  trueConfig_measurable : Measurable trueConfig
  law : μ.map trueConfig = OAI.Anderson.torusLaw d m
  history : PendingHistory d m n₀ Ω
  history_C : history.C = Ch
  pending_measurable : ∀ j x, MeasurableSet (history.pending j x)
  birth_measurable : ∀ a, MeasurableSet (history.birth a)
  birth_joint : ∀ S : Finset (BirthLabel (Torus d m)),
    μ (⋂ a ∈ S, history.birth a) ≤ ENNReal.ofReal (witnessWeight c S)
  late : Finset ℕ
  late_card : (late.card : ℝ) ≤ Clate * ((m : ℝ) + 1) * (4 : ℝ) ^ (20 * d * m)
  lateEvent : ℕ → Set Ω
  late_prob : ∀ n ∈ late, μ (lateEvent n) ≤ ENNReal.ofReal (birthBound c (m / 2))
  /-- a null set, e.g. a singular true principal block (02-state.tex:220–229). -/
  exceptional : Set Ω
  exceptional_null : μ exceptional = 0
  success : Set Ω
  failure_cover : successᶜ ⊆
    (⋃ x, history.pending (m / 2) x) ∪ (⋃ n ∈ late, lateEvent n) ∪ exceptional
  certificate : success ⊆ trueConfig ⁻¹' boundedCertificateEvent d n₀ m u E Cr cp cg

theorem historyExponent_pos (d : ℕ) (hd : 3 ≤ d) (c : ℝ) (hc : 0 < c) :
    0 < historyExponent d c := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hd)
  have hnu : 0 < nu d := by unfold nu delta; positivity
  have hα : 0 < historyAlpha d := by unfold historyAlpha; positivity
  unfold historyExponent
  exact lt_min (by positivity) (by positivity)

theorem birthBound_anti_exponent {a b : ℝ} (hab : a ≤ b) (j : ℕ) :
    birthBound b j ≤ birthBound a j := by
  unfold birthBound
  apply Real.exp_le_exp.mpr
  have : (4 : ℝ) ^ (a * (j : ℝ)) ≤ (4 : ℝ) ^ (b * (j : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg j))
  linarith

/-- The two abort probabilities are bounded by `abortBound` (history-uniform-abort). -/
theorem run_failure_le_abortBound (d m : ℕ) (q Clate : ℝ) (hq : 0 ≤ q) (hClate : 0 ≤ Clate)
    (P L : ℝ) (hP : P ≤ (4 : ℝ) ^ (20 * d * m) * birthBound q (m / 2))
    (hL : L ≤ (Clate * ((m : ℝ) + 1) * (4 : ℝ) ^ (20 * d * m)) * birthBound q (m / 2)) :
    P + L ≤ abortBound d m q Clate := by
  have hJ : (m : ℝ) / 2 - 1 ≤ ((m / 2 : ℕ) : ℝ) := by
    have h := Nat.lt_div_mul_add (a := m) (b := 2) (by norm_num)
    have h' : (m : ℝ) < ((m / 2 : ℕ) : ℝ) * 2 + 2 := by exact_mod_cast h
    linarith
  have hpow : (4 : ℝ) ^ (q * ((m : ℝ) / 2 - 1)) ≤ (4 : ℝ) ^ (q * ((m / 2 : ℕ) : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_left hJ hq)
  have hexp : (4 : ℝ) ^ (20 * d * m) * birthBound q (m / 2) ≤
      Real.exp (20 * (d : ℝ) * (m : ℝ) * Real.log 4 - (4 : ℝ) ^ (q * ((m : ℝ) / 2 - 1))) := by
    unfold birthBound
    have h4 : (4 : ℝ) ^ (20 * d * m) = Real.exp (20 * (d : ℝ) * (m : ℝ) * Real.log 4) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
      push_cast; ring_nf
    rw [h4, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hB : 0 ≤ (4 : ℝ) ^ (20 * d * m) * birthBound q (m / 2) := by
    unfold birthBound; positivity
  unfold abortBound
  have hm : 0 ≤ Clate * ((m : ℝ) + 1) := by positivity
  calc P + L ≤ (4 : ℝ) ^ (20 * d * m) * birthBound q (m / 2) +
        (Clate * ((m : ℝ) + 1)) * ((4 : ℝ) ^ (20 * d * m) * birthBound q (m / 2)) := by
          nlinarith
    _ = (1 + Clate * ((m : ℝ) + 1)) * ((4 : ℝ) ^ (20 * d * m) * birthBound q (m / 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by linarith)

/-- **Layer A glue.** Runs with uniform constants give `UniformCertificateInput`. -/
theorem uniformCertificateInput_of_runLaw (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (Cr cp cg Ch c Clate : ℝ) (hcp : 0 < cp) (hcg : 0 < cg) (hCh : 1 ≤ Ch) (hc : 0 < c)
    (hClate : 0 ≤ Clate) (N₀ : ℕ)
    (hrun : ∀ n₀ m : ℕ, N₀ ≤ n₀ → 4 * n₀ ≤ m → ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      ∀ E : ℝ, E ∈ OAI.Anderson.energyWindow d e₂ →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω), Nonempty (RunLaw d m n₀ u E Cr cp cg Ch c Clate Ω)) :
    UniformCertificateInput d e₂ := by
  obtain ⟨Np, hNp⟩ := pending_site_bound d hd c Ch hc hCh
  set q := min (historyExponent d c) c with hq_def
  have hq : 0 < q := lt_min (historyExponent_pos d hd c hc) hc
  obtain ⟨Na, hNa⟩ := uniform_abort_bound d q Clate hq hClate
  refine ⟨max (max Np Na) (max N₀ 1), Cr, cp, cg, hcp, hcg, ?_⟩
  intro n₀ m hn₀ hm u hu E hE
  have hNp' : Np ≤ n₀ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn₀
  have hNa' : Na ≤ n₀ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn₀
  have hN₀' : N₀ ≤ n₀ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn₀
  have h1 : 1 ≤ n₀ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn₀
  obtain ⟨Ω, _, ⟨R⟩⟩ := hrun n₀ m hN₀' hm u hu E hE
  have := R.prob
  set J := m / 2 with hJ
  have hJn : n₀ ≤ J := by omega
  have hJs : clearingScheduled J m := le_rfl
  -- pending sites at the cutoff
  have hsite : ∀ x, R.μ (R.history.pending J x) ≤ ENNReal.ofReal (birthBound q J) := by
    intro x
    refine le_trans (hNp m n₀ Ω R.μ R.history hNp' R.history_C R.pending_measurable
      R.birth_measurable R.birth_joint J x hJn hJs) ?_
    exact ENNReal.ofReal_le_ofReal (birthBound_anti_exponent (min_le_left _ _) J)
  have hpend := cutoff_probability_bound R.μ d m J (fun x => R.history.pending J x) q hsite
  have hlate := late_failure_bound R.μ R.late R.lateEvent (birthBound q J)
    (fun n hn => le_trans (R.late_prob n hn)
      (ENNReal.ofReal_le_ofReal (birthBound_anti_exponent (min_le_right _ _) J)))
  have hBq : 0 ≤ birthBound q J := by unfold birthBound; positivity
  have hfail : R.μ R.successᶜ ≤ ENNReal.ofReal (abortBound d m q Clate) := by
    calc R.μ R.successᶜ
        ≤ R.μ ((⋃ x, R.history.pending J x) ∪ (⋃ n ∈ R.late, R.lateEvent n) ∪
            R.exceptional) := measure_mono R.failure_cover
      _ ≤ R.μ ((⋃ x, R.history.pending J x) ∪ (⋃ n ∈ R.late, R.lateEvent n)) +
            R.μ R.exceptional := measure_union_le _ _
      _ = R.μ ((⋃ x, R.history.pending J x) ∪ (⋃ n ∈ R.late, R.lateEvent n)) := by
          rw [R.exceptional_null, add_zero]
      _ ≤ R.μ (⋃ x, R.history.pending J x) + R.μ (⋃ n ∈ R.late, R.lateEvent n) :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal ((4 : ℝ) ^ (20 * d * m) * birthBound q J) +
            ENNReal.ofReal ((R.late.card : ℝ) * birthBound q J) := add_le_add hpend hlate
      _ = ENNReal.ofReal ((4 : ℝ) ^ (20 * d * m) * birthBound q J +
            (R.late.card : ℝ) * birthBound q J) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal (abortBound d m q Clate) := by
          apply ENNReal.ofReal_le_ofReal
          exact run_failure_le_abortBound d m q Clate hq.le hClate _ _ le_rfl
            (mul_le_mul_of_nonneg_right R.late_card hBq)
  have habort := hNa n₀ m hNa' hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hexp : Real.exp (-(m : ℝ)) ≤ 1 / 2 := by
    have : Real.exp (-(m : ℝ)) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-1) ≤ 1 / 2 := by
      have := Real.add_one_le_exp (1 : ℝ)
      rw [Real.exp_neg]
      rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      linarith
    linarith
  have hfail' : R.μ R.successᶜ ≤ 1 / 2 := by
    refine le_trans hfail ?_
    rw [show (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp]
    exact ENNReal.ofReal_le_ofReal (le_trans habort hexp)
  have hproj := success_projects_to_true_law R.μ d m R.trueConfig R.trueConfig_measurable
    R.law R.success _ (bounded_certificate_event_measurable d n₀ m u E Cr cp cg) R.certificate
  have hsucc : (1 / 2 : ℝ≥0∞) ≤ R.μ R.success := by
    have htot : R.μ R.success + R.μ R.successᶜ ≥ 1 := by
      rw [← measure_univ (μ := R.μ)]
      calc R.μ Set.univ = R.μ (R.success ∪ R.successᶜ) := by rw [Set.union_compl_self]
        _ ≤ R.μ R.success + R.μ R.successᶜ := measure_union_le _ _
    by_contra hlt
    push_neg at hlt
    have : R.μ R.success + R.μ R.successᶜ < 1 / 2 + 1 / 2 :=
      ENNReal.add_lt_add_of_lt_of_le (by simp) hlt hfail'
    rw [ENNReal.add_halves] at this
    exact absurd htot (not_le.mpr this)
  exact le_trans hsucc hproj

end AndersonAC.AgentS78
