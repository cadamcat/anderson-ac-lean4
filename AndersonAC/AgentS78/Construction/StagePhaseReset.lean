import AndersonAC.AgentS78.Construction.StagePhaseStage
import AndersonAC.AgentS78.Construction.StagePhaseResetFix

/-!
# WP10 construction: the diagonal reset on the active block, at the record level

`resetMap` (ResetBlock.lean) inverts the full torus matrix and therefore does not produce a
damped endpoint once the active set is proper (`resetMap_not_damped`,
StagePhaseResetDefect.lean). `resetMapA` is Proposition 7.4 on the active block
(07-assembly.tex:806–877): the measurable Picard correction `resetCorrection` of the active
block `(M_A, r_A)`, `r' = r + ζ` (padded by zero), `g' = (M_A − t diag r'_A)⁻¹` padded by zero.

`stage_end_resetA`: the clearing-phase invariant, the stage-start bound `‖K_old‖ ≤ 1/3`
(StageBounds, from `stageBounds_of_hist`) and the inverse-row input of Lemma 4.? for the
committed endpoint (`ResetRowInput`, 07-assembly.tex:1017–1019) give the next stage boundary
for `resetMapA t_j x`.
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

/-- The active block of the committed endpoint. -/
def activeBlock (s : Endpoint (Torus d m)) : Matrix s.active s.active ℂ :=
  s.M.submatrix (fun a : s.active => a.val) (fun a : s.active => a.val)

/-- The reset correction of the active block (the measurable Picard limit). -/
def activeReset (t : ℝ) (x : RunRecord d m) : x.endpoint.active → ℂ :=
  resetCorrection t (activeBlock x.endpoint, fun a : x.endpoint.active => x.r a.val)

/-- **The diagonal reset on the active block.** -/
def resetMapA (t : ℝ) (x : RunRecord d m) : RunRecord d m :=
  { x with
    r := x.r + padV x.endpoint.active (activeReset t x)
    endpoint := resetEndpoint x.endpoint x.r (activeReset t x) t }

theorem resetMapA_preserves (t : ℝ) (x : RunRecord d m) :
    (resetMapA t x).stage = x.stage ∧ (resetMapA t x).sweep = x.sweep ∧
    (resetMapA t x).installed = x.installed ∧
    (resetMapA t x).prefixLength = x.prefixLength ∧ (resetMapA t x).terminal = x.terminal ∧
    (resetMapA t x).pending = x.pending ∧ (resetMapA t x).latest = x.latest ∧
    (resetMapA t x).components = x.components ∧ (resetMapA t x).aborted = x.aborted ∧
    (resetMapA t x).endpoint.active = x.endpoint.active :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Inverse-row input for the reset** (Lemma `inverse-row` applied to the committed
endpoint, 07-assembly.tex:1017–1019): `‖(1 − K)⁻¹‖_{∞→∞} ≤ C log(1/t)` on the active block,
for the damping `r` and scale `t`. -/
def ResetRowBound (C : ℝ) (s : Endpoint (Torus d m)) (r : Torus d m → ℂ) (t : ℝ) : Prop :=
  ∀ v : s.active → ℂ,
    ‖((1 - squareKernel ((Real.sqrt t : ℂ) • resetInverse (activeBlock s)
      (fun a : s.active => r a.val) t))⁻¹).mulVec v‖ ≤ C * Real.log (1 / t) * ‖v‖

theorem Kn_eq_activeBlock (s : Endpoint (Torus d m)) (r : Torus d m → ℂ) (t : ℝ)
    (hD : IsDampedEndpoint s r t) :
    Kn s t = matrixNorm (squareKernel ((Real.sqrt t : ℂ) •
      resetInverse (activeBlock s) (fun a : s.active => r a.val) t)) := by
  unfold Kn normalizedInverse
  rw [g_eq_padM_resetInverse s r t hD, padM_squareKernel, matrixNorm_eq_l2, matrixNorm_eq_l2,
    norm_padM]
  rfl

/-- **The stage operation with the active-block reset.** -/
theorem stage_end_resetA (hd : 3 ≤ d) (CA cA PA CR : ℝ) (hCA : 1 ≤ CA) (hcA : 0 < cA)
    (hPA : 0 ≤ PA) :
    ∃ Cmin : ℝ, 1 ≤ Cmin ∧ ∀ C : ℝ, Cmin ≤ C → ∃ t₀ : ℝ, 0 < t₀ ∧
    ∀ {m : ℕ} (n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (j : ℕ) (x : RunRecord d m)
      (D : ClearPhaseData n₀ u E ρ C CA cA PA j x),
      u ∈ Set.Ioc (1 / 4 : ℝ) 1 → n₀ < j → stageScale u (j - 1) m < t₀ →
      Kn D.old (stageScale u (j - 1) m) ≤ 1 / 3 →
      (Kn x.endpoint (stageScale u j m) ≤ 1 / 2 →
        (∀ i ∈ x.endpoint.active, ‖x.endpoint.g i i - x.r i‖ ≤ stageScale u j m ^ (0.36 * delta)) →
        ResetRowBound CR x.endpoint x.r (stageScale u j m)) →
      BoundaryHist n₀ u E ρ C j (resetMapA (stageScale u j m) x).endpoint
        (resetMapA (stageScale u j m) x).r := by
  obtain ⟨Cmin, hCmin, hcore⟩ := stage_end_core hd CA cA PA hCA hcA hPA
  obtain ⟨C', tA, hC', htA, hCAss⟩ := committed_assembly d hd CA cA PA hCA hcA hPA
  obtain ⟨tR, htR, hRbc⟩ := resetTransform_ball_contract cA (max (CA + 1) CR) hcA
    ((by linarith : (1 : ℝ) ≤ CA + 1).trans (le_max_left _ _))
  refine ⟨Cmin, hCmin, fun C hC => ?_⟩
  obtain ⟨t₀, ht₀, hmain⟩ := hcore C hC
  have hC1 : 1 ≤ C := hCmin.trans hC
  have hδ : (0 : ℝ) < delta := by norm_num [delta]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdν : (d : ℝ) * nu d = delta / 100000 := by
    unfold nu; field_simp
  have he1 : 0 < 0.06 * delta - (d : ℝ) * nu d := by rw [hdν]; norm_num [delta]
  obtain ⟨t1, ht1, hs1⟩ := AndersonAC.SolS78.reset_radius_small _ (1 / C') he1 (by positivity)
  obtain ⟨t2, ht2, hs2⟩ := AndersonAC.SolS78.reset_radius_small (0.10 * delta)
    (1 / (6 * (C + 2))) (by positivity) (by positivity)
  refine ⟨min (min t₀ (min tA 1)) (min tR (min t1 t2)), by positivity, ?_⟩
  intro m n₀ u E ρ j x D hu hj ht hKold hrowb
  have hjt : stageScale u (j - 1) m < t₀ := ht.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  set t := stageScale u (j - 1) m with htdef
  set t' := stageScale u j m with ht'def
  have htpos : 0 < t := stageScale_pos' hu _ _
  have ht'pos : 0 < t' := stageScale_pos' hu _ _
  have htt' : t' ≤ t := stageScale_anti hu m (Nat.sub_le j 1)
  have ht1' : t < 1 := ht.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  have ht'A : t' < tA := htt'.trans_lt (ht.trans_le ((min_le_left _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have ht'R : t' < tR := htt'.trans_lt (ht.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have ht'1 : t' < t1 := htt'.trans_lt (ht.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have ht2' : t < t2 := ht.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  have hs1' : C' * t' ^ (0.06 * delta - (d : ℝ) * nu d) ≤ 1 := by
    have := hs1 t' ht'pos ht'1
    rw [le_div_iff₀ hC'] at this; linarith
  have hs2' : (C + 2) * t ^ (0.10 * delta) ≤ 1 / 6 := by
    have := hs2 t htpos ht2'
    rw [le_div_iff₀ (by positivity)] at this; linarith
  obtain ⟨old, rOld, k, I, hist, sweep, hlast, hfrozen, hIC, hIc, hIP⟩ := D
  simp only at hKold
  subst hfrozen
  have hCa := hCAss m k t' (stageScale u n₀ m * t') x.r I hIC hIc hIP ht'A (Fin.last k)
  rw [hlast] at hCa
  obtain ⟨hKfin, hlag, -, -, -, -⟩ := hCa
  have hD : IsDampedEndpoint x.endpoint x.r t' := hlast ▸ I.physical (Fin.last k)
  set A := x.endpoint.active with hA
  set MA := activeBlock x.endpoint with hMA
  set rA : A → ℂ := fun a => x.r a.val with hrA
  have hfg := g_eq_padM_resetInverse x.endpoint x.r t' hD
  have hcount : Fintype.card (Torus d m) ≤ 2 * A.card := by
    have := I.activeCount (Fin.last k); rw [hlast] at this; exact this
  haveI hne : Nonempty A := by
    have hpos : 0 < Fintype.card (Torus d m) := Fintype.card_pos_iff.mpr ⟨0⟩
    have : 0 < A.card := by omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp this
    exact ⟨⟨a, ha⟩⟩
  have hMAs : ∀ a b, MA a b = MA b a ∧ (MA a b).im = 0 := fun a b => hD.1 a.val b.val
  have hdampI : ∀ i, cA ≤ (x.r i).im ∧ (x.r i).im ≤ CA ∧ ‖x.r i‖ ≤ CA := by
    intro i; have := I.damping i; rw [hIC, hIc] at this; exact this
  have hrA' : ∀ a, cA ≤ (rA a).im ∧ (rA a).im ≤ CA + 1 ∧ ‖rA a‖ ≤ CA + 1 := by
    intro a; obtain ⟨h1, h2, h3⟩ := hdampI a.val
    exact ⟨h1, by linarith, by linarith⟩
  have hgdiag : ∀ a : A, resetInverse MA rA t' a a = x.endpoint.g a.val a.val := by
    intro a; rw [hfg, padM_val]; rfl
  have hpow : t' ^ (0.42 * delta - (d : ℝ) * nu d) =
      t' ^ (0.06 * delta - (d : ℝ) * nu d) * t' ^ (0.36 * delta) := by
    rw [← Real.rpow_add ht'pos]; congr 1; ring
  have hlag' : ∀ a : A, ‖x.endpoint.g a.val a.val - x.r a.val‖ ≤ t' ^ (0.36 * delta) := by
    intro a
    refine (hlag a.val a.property).trans ?_
    rw [hpow, ← mul_assoc]
    have := Real.rpow_pos_of_pos ht'pos (0.36 * delta)
    nlinarith
  have hgA : ∀ a, (resetInverse MA rA t' a a).im ≤ CA + 1 := by
    intro a
    rw [hgdiag]
    have h1 := hlag' a
    have h2 : |(x.endpoint.g a.val a.val - x.r a.val).im| ≤
        ‖x.endpoint.g a.val a.val - x.r a.val‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im] at h2
    have h3 := (hdampI a.val).2.1
    have := le_abs_self ((x.endpoint.g a.val a.val).im - (x.r a.val).im)
    have h4 : t' ^ (0.36 * delta) ≤ 1 := Real.rpow_le_one ht'pos.le
      ((htt'.trans ht1'.le)) (by positivity)
    linarith
  have hKfin' : Kn x.endpoint t' < 1 / 2 := by
    have h1 : Kn x.endpoint t' ≤ Kn (I.state 0) t' + t' ^ (0.10 * delta) := by
      unfold Kn; exact hKfin
    have h2' : Kn (I.state 0) t' ≤ Kn old t + C * t ^ (0.10 * delta) := sweep.K
    have h3 : t' ^ (0.10 * delta) ≤ t ^ (0.10 * delta) :=
      Real.rpow_le_rpow ht'pos.le htt' (by positivity)
    have h4 : 0 < t ^ (0.10 * delta) := Real.rpow_pos_of_pos htpos _
    nlinarith
  have hKA : matrixNorm (squareKernel ((Real.sqrt t' : ℂ) • resetInverse MA rA t')) < 1 / 2 := by
    rw [← Kn_eq_activeBlock x.endpoint x.r t' hD]; exact hKfin'
  have hrowb' := hrowb hKfin'.le (fun i hi => hlag' ⟨i, hi⟩)
  have hlagA : ‖resetLag MA rA t'‖ ≤ t' ^ (0.36 * delta) := by
    refine (pi_norm_le_iff_of_nonneg (Real.rpow_nonneg ht'pos.le _)).mpr fun a => ?_
    simp only [resetLag]
    rw [hgdiag]
    exact hlag' a
  have hlog : 0 ≤ Real.log (1 / t') := by
    rw [one_div, Real.log_inv]
    exact neg_nonneg.mpr (Real.log_nonpos ht'pos.le (htt'.trans ht1'.le))
  have hmax := le_max_left (CA + 1) CR
  obtain ⟨hball, hcontr⟩ := hRbc A MA rA t' ht'pos ht'R hMAs
    (fun a => ⟨(hrA' a).1, (hrA' a).2.1.trans hmax, (hrA' a).2.2.trans hmax⟩)
    (fun a => (hgA a).trans hmax) hKA
    (fun v => (hrowb' v).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hlog) (norm_nonneg v))) hlagA
  obtain ⟨hζ, hfix⟩ := resetCorrection_solves MA rA t' ht'pos.le hKA hball hcontr
  exact hmain n₀ u E ρ j x ⟨old, x.r, k, I, hist, sweep, hlast, rfl, hIC, hIc, hIP⟩ hu hj hjt
    (activeReset t' x) hζ hfix

end AndersonAC.AgentS78
