import AndersonAC.AgentS78.Construction.TilePhaseContracts
import AndersonAC.AgentS78.Construction.TileCoverStatement
import AndersonAC.AgentS78.SweepPrestate
import AndersonAC.S45.DuplicationProof
import AndersonAC.S45.WardTransfer

/-!
# the duplicated stage start on the live ports (setup)

 . The start lift `sweepStartLiveState θ z` restricted to its live
ports (`liveStart z`, both ports of every active site) is the S45 lift of the physical active
state along an explicit `PortMap` (`livePortMap`), with port masses `1` (–80). This is
the form in which `S45.duplication` (–88) applies.
-/

noncomputable section
set_option autoImplicit false

open scoped BigOperators Matrix.Norms.L2Operator

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

/-- `(x^{1/4})^4 = x` for `x ≥ 0`. -/
theorem power_quarter_pow_four {x : ℝ} (hx : 0 ≤ x) : S45.power x (1 / 4) ^ 4 = x := by
  show (x ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = x
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- `(x^{1/4})^2 = √x` for `x ≥ 0`. -/
theorem power_quarter_sq {x : ℝ} (hx : 0 ≤ x) : S45.power x (1 / 4) ^ 2 = Real.sqrt x := by
  show (x ^ (1 / 4 : ℝ)) ^ (2 : ℕ) = Real.sqrt x
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, Real.sqrt_eq_rpow]
  norm_num

section Lift
variable (θ : ℝ) (z : RunRecord d m)

/-- Enumeration of the active sites. -/
def actEquiv (z : RunRecord d m) : Fin z.endpoint.active.card ≃ z.endpoint.active :=
  z.endpoint.active.equivFin.symm

theorem mem_liveStart_iff {z : RunRecord d m} {p : Port d m} :
    p ∈ liveStart z ↔ p.1 ∈ z.endpoint.active := by
  simp [liveStart]

/-- The port map from the live start ports to the enumerated active sites (–71). -/
def livePortMap : S45.PortMap (liveStart z) (Fin z.endpoint.active.card) where
  site p := (actEquiv z).symm ⟨p.1.1, mem_liveStart_iff.mp p.2⟩
  weight p := (S45.splitPorts (Torus d m) θ).weight p.1

/-- The physical S45 state on the enumerated active sites. -/
def physState : S45.State (Fin z.endpoint.active.card) := toS45 z.endpoint z.r (actEquiv z)

theorem livePortMap_site_val (p : liveStart z) :
    (actEquiv z ((livePortMap θ z).site p)).val = p.1.1 := by
  simp [livePortMap]

theorem live_eq : (sweepStartLiveState θ z).live = liveStart z := rfl

/-- The start lift on its live ports is the S45 port lift of the physical active state. -/
theorem startLive_eq :
    (sweepStartLiveState θ z).state (portR θ z.r) =
      (livePortMap θ z).liftState (physState z) := by
  unfold S45.LiveState.state S45.PortMap.liftState
  congr 1
  · funext p q
    simp only [livePortMap, physState, toS45, Equiv.apply_symm_apply]
    rfl
  · funext p
    simp only [livePortMap, physState, toS45, Equiv.apply_symm_apply]
    rfl

/-- The start lift with its live set written as `liveStart z` (definitionally equal). -/
def startLS : S45.LiveState (Port d m) := ⟨liveStart z, (sweepStartLiveState θ z).g⟩

theorem sweepStartLiveState_eq_startLS : sweepStartLiveState θ z = startLS θ z := rfl

theorem startLS_state_eq :
    S45.LiveState.state ⟨liveStart z, (sweepStartLiveState θ z).g⟩ (portR θ z.r) =
      (livePortMap θ z).liftState (physState z) :=
  startLive_eq θ z

theorem livePortMap_weight (p : liveStart z) :
    (livePortMap θ z).weight p = S45.power (if p.1.2 then θ else 1 - θ) (1 / 4) := rfl

theorem livePortMap_site_eq_iff (p : liveStart z) (i : Fin z.endpoint.active.card) :
    (livePortMap θ z).site p = i ↔ p.1.1 = (actEquiv z i).val := by
  constructor
  · rintro rfl; exact (livePortMap_site_val θ z p).symm
  · intro h
    apply (actEquiv z).injective
    apply Subtype.ext
    rw [livePortMap_site_val, h]

/-- Port masses are one (–69: `k_bit⁴ + k_res⁴ = w + θ = 1`). -/
theorem livePortMap_mass (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (i : Fin z.endpoint.active.card) :
    (livePortMap θ z).mass i = 1 := by
  classical
  set a := (actEquiv z i).val with ha
  have haA : a ∈ z.endpoint.active := (actEquiv z i).property
  let F : Port d m → ℝ := fun p =>
    if p.1 = a then S45.power (if p.2 then θ else 1 - θ) (1 / 4) ^ 4 else 0
  have h1 : (livePortMap θ z).mass i = ∑ p : liveStart z, F p.1 := by
    unfold S45.PortMap.mass
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [F, livePortMap_site_eq_iff, livePortMap_weight]
    rfl
  have h2 : ∑ p : liveStart z, F p.1 = ∑ p ∈ liveStart z, F p :=
    Finset.sum_coe_sort (liveStart z) F
  have h3 : ∑ p ∈ liveStart z, F p = ∑ p : Port d m, F p := by
    refine Finset.sum_subset (Finset.subset_univ _) fun p _ hp => ?_
    have : p.1 ≠ a := fun h => hp (mem_liveStart_iff.mpr (h ▸ haA))
    simp [F, this]
  have h4 : ∑ p : Port d m, F p = F (a, true) + F (a, false) := by
    change ∑ p : Torus d m × Bool, F p = _
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
    · exact Fintype.sum_bool _
    · intro b _ hb; simp [F, hb]
    · intro h; exact absurd (Finset.mem_univ a) h
  have e1 : F (a, true) = θ := by
    simp only [F, if_pos rfl]; exact power_quarter_pow_four hθ0
  have e2 : F (a, false) = 1 - θ := by
    simp only [F, if_pos rfl]; exact power_quarter_pow_four (by linarith : (0:ℝ) ≤ 1 - θ)
  rw [h1, h2, h3, h4, e1, e2]
  ring

theorem livePortMap_weight_pos (hθ0 : 0 < θ) (hθ1 : θ < 1) (p : liveStart z) :
    0 < (livePortMap θ z).weight p := by
  rw [livePortMap_weight]
  unfold S45.power
  split_ifs
  · exact Real.rpow_pos_of_pos hθ0 _
  · exact Real.rpow_pos_of_pos (by linarith) _

theorem livePortMap_weight_le_one (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (p : liveStart z) :
    (livePortMap θ z).weight p ≤ 1 := by
  rw [livePortMap_weight]
  unfold S45.power
  split_ifs
  · exact Real.rpow_le_one hθ0 hθ1 (by norm_num)
  · exact Real.rpow_le_one (by linarith) (by linarith) (by norm_num)

end Lift

end AndersonAC.AgentS78
