import AndersonAC.AgentS78.Construction.TileStartFourier
import AndersonAC.AgentS78.Construction.TileStartComparison
import AndersonAC.AgentS78.Construction.TileStartPortFacts

/-!
# Algebraic duplicated stage start on the live ports

`StartClauses` is stated on the ambient all-ports state, which fails when a site is
inactive (`startClauses_active_univ`). This file states the algebraic clauses on the
live state that follow from Lemma `duplication` (04-sweep.tex:73–123) and the
stage-boundary bounds (05-local-sweeps.tex:320–337):
`a.state (portR θ r) : S45.State a.live` and proved (`tileStartAlgebraic_proof`) under the
stage bounds at `j − 1`, the damped identity of the endpoint and the cover facts
(`b = t_{n₀} t`, energy `Λ`, site `Prod.fst`). The decay clauses (`start_decay`,
`start_far_decay`, `prefix_decay`) are not part of this file: they need the locality of the
endpoint matrix (Combes–Thomas, 05-local-sweeps.tex:62–80).
-/

noncomputable section
set_option autoImplicit false

open scoped BigOperators Matrix.Norms.L2Operator

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

section Defs
variable (C : ℝ) (P : TilePlan d m) (j : ℕ)

/-- The duplicated stage-start state on the live ports. -/
def liveStartState (a : S45.LiveState (Port d m)) (r : Torus d m → ℂ) : S45.State a.live :=
  a.state (portR (sweepTheta P.u m j) r)

/-- **Algebraic duplicated stage-start clauses on the live ports** for the
`start_prestate`, `start_lag`, `start_comparison`, `start_rows`, `start_reserve_rows` clauses
of `StartClauses`; –123, 05:320–337). -/
structure StartAlgebraicLive (a : S45.LiveState (Port d m)) (r : Torus d m → ℂ) : Prop where
  start_prestate : ∃ Λplus Wstar : S45.Form a.live,
    S45.Prestate (sweepScale P.u m j) C Λplus Wstar (liveStartState P j a r) ∧
    ‖(liveStartState P j a r).K (sweepScale P.u m j)‖ ≤ 1 / 3 ∧
    (∀ y, S45.neutral y → 0 ≤ Λplus y) ∧
    (∀ y, S45.neutral y → (liveStartState P j a r).X (sweepScale P.u m j) y ≤
      (1 + S45.power (sweepScale P.u m j) S45.kappa) *
        (∑ i, y i ^ 2 / (liveStartState P j a r).p i ^ 2) +
        C * sweepScale P.u m j * Λplus y)
  start_lag : ∀ i, a.ambientLag (sweepScale P.u m j) (portR (sweepTheta P.u m j) r) i = 0
  start_comparison : S45.formComparable
    (S45.qform ((liveStartState P j a r).D (sweepScale P.u m j)))
    (S45.spatialEnergy (fun x : a.live => (P.cover j).cover.site x.1) (P.cover j).b
      (P.cover j).cover.energy) C
  start_rows : ∀ i, (liveStartState P j a r).fourthRow (sweepScale P.u m j) Finset.univ i ≤
    3 / 4 * S45.rowCap (sweepScale P.u m j)
  start_reserve_rows : ∀ i : a.live, i.1.2 = true →
    (liveStartState P j a r).fourthRow (sweepScale P.u m j)
        (Finset.univ.filter fun x : a.live => x.1.2 = true) i ≤
      sweepTheta P.u m j ^ 2 * S45.rowCap (sweepScale P.u m j)

end Defs

/-- Algebraic stage-start clauses on the live ports, assuming the endpoint's damped
identity and the stated cover energy and site map, uniformly for `C ≥ C'`. -/
def TileStartAlgebraicStatement (d : ℕ) : Prop :=
  ∀ cP CP cL CL C₀ : ℝ, 0 < cP → cP ≤ CP → 0 < cL → 0 < CL → 0 < C₀ →
  ∃ C' ≥ 1, ∃ t0 > 0, ∀ C ≥ C', ∀ (m n₀ : ℕ) (u : ℝ) (P : TilePlan d m) (j : ℕ)
    (z : RunRecord d m),
    P.n₀ = n₀ → P.u = u → u ∈ Set.Ioc (1 / 4 : ℝ) 1 → n₀ < j → j ≤ m + 1 →
    sweepScale u m j < t0 →
    StageBounds d m n₀ (j - 1) u cP CP cL CL C₀ z.endpoint z.r →
    IsDampedEndpoint z.endpoint z.r (sweepScale u m j) →
    (P.cover j).cover.energy = gradientEnergy (nnGraph d m) →
    (P.cover j).b = stageScale u n₀ m * sweepScale u m j →
    (P.cover j).cover.site = Prod.fst →
    StartAlgebraicLive C P j (sweepStartLiveState (sweepTheta P.u m j) z) z.r ∧
    (sweepStartMap (sweepTheta P.u m j) (sweepScale P.u m j) z).sweep.valid
      (sweepScale P.u m j) (portR (sweepTheta P.u m j) z.r)
      (stageD0 P j (sweepStartMap (sweepTheta P.u m j) (sweepScale P.u m j) z)) 0

/-! ## Scales -/

theorem sweepScale_eq_stage (u : ℝ) {m j : ℕ} (hj : j ≤ m + 1) :
    sweepScale u m j = stageScale u (j - 1) m := by
  unfold sweepScale
  split_ifs with hf
  · have : j = m + 1 := le_antisymm hj hf
    subst this; simp
  · rfl

theorem sweepTheta_bounds {u : ℝ} (hu : 0 < u) {m j : ℕ} (hj0 : 0 < j) (hj : j ≤ m + 1) :
    1 / 4 ≤ sweepTheta u m j ∧ sweepTheta u m j ≤ 1 / 2 := by
  unfold sweepTheta
  split_ifs with hf
  · norm_num
  · have hjm : j ≤ m := by unfold IsFinalSweep at hf; omega
    unfold stageScale
    set a : ℝ := u / (4 : ℝ) ^ j
    set c : ℝ := u / (4 : ℝ) ^ m
    have ha : 0 < a := by positivity
    have hc : 0 < c := by positivity
    have hca : c ≤ a := div_le_div_of_nonneg_left hu.le (by positivity)
      (pow_le_pow_right₀ (by norm_num) hjm)
    have hprev : u / (4 : ℝ) ^ (j - 1) = 4 * a := by
      have : (4 : ℝ) ^ j = 4 * (4 : ℝ) ^ (j - 1) := by
        rw [← pow_succ']; congr 1; omega
      simp only [a, this]; field_simp
    rw [hprev]
    constructor
    · rw [le_div_iff₀ (by positivity)]; linarith
    · rw [div_le_iff₀ (by positivity)]; linarith

theorem sweepScale_lower {u : ℝ} (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (m j : ℕ) (hj : j ≤ m + 1) :
    1 / (4 : ℝ) ^ (m + 1) ≤ sweepScale u m j := by
  rw [sweepScale_eq_stage u hj]
  unfold stageScale
  have h1 : 1 / (4 : ℝ) ^ (m + 1) ≤ u / (4 : ℝ) ^ m := by
    rw [pow_succ, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hu.1, show (0 : ℝ) < (4 : ℝ) ^ m by positivity]
  have : 0 ≤ u / (4 : ℝ) ^ (j - 1) := div_nonneg (by linarith [hu.1]) (by positivity)
  linarith

/-! ## The ambient `D` is the live `D` padded by zero -/

theorem ambient_qform_eq {P : Type*} [Fintype P] [DecidableEq P] (a : S45.LiveState P)
    (r : P → ℂ) (t : ℝ) (f : P → ℝ) :
    S45.qform ((a.ambient r).D t) f = S45.qform ((a.state r).D t) (fun x => f x.1) := by
  classical
  have hent : ∀ x y, ((a.ambient r).D t) x y =
      if hx : x ∈ a.live then if hy : y ∈ a.live then
        ((a.state r).D t) ⟨x, hx⟩ ⟨y, hy⟩ else 0 else 0 := by
    intro x y
    simp only [AgentS45.state_D_entry, S45.State.q, S45.State.p, S45.State.F,
      S45.entryAbsSquare, S45.State.h, Matrix.smul_apply, smul_eq_mul, S45.LiveState.ambient,
      S45.LiveState.state, S45.mask, S45.pad, S45.restrict, Matrix.submatrix_apply]
    by_cases hx : x ∈ a.live <;> by_cases hy : y ∈ a.live <;>
      simp [hx, hy, Subtype.ext_iff]
    rintro rfl; exact absurd hx hy
  unfold S45.qform
  simp only [Matrix.mulVec, dotProduct, hent]
  rw [← Finset.sum_subset (Finset.subset_univ a.live) (fun x _ hx => by simp [hx]),
    ← Finset.sum_coe_sort a.live]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  rw [← Finset.sum_subset (Finset.subset_univ a.live) (fun y _ hy => by simp [x.2, hy]),
    ← Finset.sum_coe_sort a.live]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [x.2, y.2]

/-! ## Reserve rows -/

theorem live_reserve_rows (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (z : RunRecord d m)
    (s : S45.State (Fin z.endpoint.active.card)) (t H : ℝ)
    (hrow : ∀ k, s.fourthRow t Finset.univ k ≤ H) (x : liveStart z) (hx : x.1.2 = true) :
    ((livePortMap θ z).liftState s).fourthRow t
        (Finset.univ.filter fun y : liveStart z => y.1.2 = true) x ≤ θ ^ 2 * H := by
  classical
  set v := livePortMap θ z
  set e := actEquiv z
  set R := Finset.univ.filter fun y : liveStart z => y.1.2 = true
  have hwx : v.weight x ^ 4 = θ := by rw [live_weight4 z hθ0 hθ1, if_pos hx]
  have hterm : ∀ y ∈ R, ‖(v.liftState s).h t x y‖ ^ 4 =
      θ * (θ * ‖s.h t (v.site x) (v.site y)‖ ^ 4) := by
    intro y hy
    have hy' : y.1.2 = true := (Finset.mem_filter.mp hy).2
    have hwy : v.weight y ^ 4 = θ := by rw [live_weight4 z hθ0 hθ1, if_pos hy']
    rw [AgentS45.lift_h_entry, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow]
    have h1 : |v.weight x| ^ 4 = v.weight x ^ 4 := by
      rw [show |v.weight x| ^ 4 = (|v.weight x| ^ 2) ^ 2 by ring, sq_abs]; ring
    have h2 : |v.weight y| ^ 4 = v.weight y ^ 4 := by
      rw [show |v.weight y| ^ 4 = (|v.weight y| ^ 2) ^ 2 by ring, sq_abs]; ring
    rw [h1, h2, hwx, hwy]; ring
  unfold S45.State.fourthRow
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.mul_sum]
  have hbij : ∑ y ∈ R, ‖s.h t (v.site x) (v.site y)‖ ^ 4 = s.fourthRow t Finset.univ (v.site x) := by
    unfold S45.State.fourthRow
    refine Finset.sum_nbij' (fun y => v.site y)
      (fun k => ⟨((e k).val, true), mem_liveStart_iff.mpr (e k).property⟩) ?_ ?_ ?_ ?_ ?_
    · intro y _; exact Finset.mem_univ _
    · intro k _; simp [R]
    · intro y hy
      have hy' : y.1.2 = true := (Finset.mem_filter.mp hy).2
      apply Subtype.ext
      apply Prod.ext
      · exact livePortMap_site_val θ z y
      · exact hy'.symm
    · intro k _
      rw [livePortMap_site_eq_iff]
    · intro y _; rfl
  rw [hbij]
  have h0 : 0 ≤ s.fourthRow t Finset.univ (v.site x) := Finset.sum_nonneg fun _ _ => by positivity
  have := hrow (v.site x)
  have hθ2 : θ * θ = θ ^ 2 := by ring
  rw [← mul_assoc, hθ2]
  exact mul_le_mul_of_nonneg_left this (sq_nonneg θ)

end AndersonAC.AgentS78
