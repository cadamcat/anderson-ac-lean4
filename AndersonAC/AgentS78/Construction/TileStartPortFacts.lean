import AndersonAC.S45.DuplicationProof
import AndersonAC.S45.WardTransfer

/-!
# prestate facts of a mass-one port lift (Lemma `duplication`, –123)

 . For a port map with masses one and positive weights, the lift of a
self-consistent physical state with the constant kernel keeps the Ward identity, symmetry,
the vanishing lag, the constant kernel of `D`, the broad bounds and the fourth-row bounds.
-/

noncomputable section
set_option autoImplicit false

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace AndersonAC.AgentS78

open AndersonAC.S45

variable {P I : Type*} [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]
variable (v : PortMap P I) (s : State I) (t : ℝ)

theorem lift_ward_of_mass (hmass : ∀ i, v.mass i = 1) (hward : s.ward t) :
    (v.liftState s).ward t := by
  apply AgentS45.lift_mass_ward v s t
  have : (fun i => ((v.mass i * s.p i : ℝ) : ℂ)) = fun i => (s.p i : ℂ) := by
    funext i; simp [hmass i]
  rw [this]; exact hward

theorem lift_fix (hfix : ∀ i, s.g i i = s.r i) (x : P) :
    (v.liftState s).g x x = (v.liftState s).r x := by
  simp only [PortMap.liftState, hfix]; ring

theorem lift_lag_zero (hfix : ∀ i, s.g i i = s.r i) (x : P) :
    (v.liftState s).lag t x = 0 := by
  have h0 : (v.liftState s).rawLag = 0 := by
    funext y; simp [State.rawLag, lift_fix v s hfix y]
  simp [State.lag, h0]

theorem average_const (a : ℝ) (i : I) : v.average (fun _ => a) i = v.mass i * a := by
  unfold PortMap.average PortMap.mass
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> ring

theorem lift_constantKernel (hmass : ∀ i, v.mass i = 1) (hk : ∀ x, 0 < v.weight x)
    (hfix : ∀ i, s.g i i = s.r i) (hkernel : constantKernel (s.D t)) (hp : ∀ i, 0 < s.p i) :
    constantKernel ((v.liftState s).D t) := by
  have hq := (AgentS45.duplication_algebraic v s t hmass hfix).2.2.2.2
  have hterm : ∀ f : P → ℝ, ∀ x, 0 ≤ s.p (v.site x) ^ 2 * v.weight x ^ 4 *
      (f x - v.average f (v.site x)) ^ 2 := fun f x => by positivity
  refine ⟨AgentS45.lift_D_isSymm v s t hfix hkernel, fun f => ?_, fun f => ⟨fun h0 => ?_, ?_⟩⟩
  · rw [hq f]
    exact add_nonneg (hkernel.2.1 _) (Finset.sum_nonneg fun x _ => hterm f x)
  · rw [hq f] at h0
    have h1 := hkernel.2.1 (v.average f)
    have h2 : 0 ≤ ∑ x, s.p (v.site x) ^ 2 * v.weight x ^ 4 *
        (f x - v.average f (v.site x)) ^ 2 := Finset.sum_nonneg fun x _ => hterm f x
    obtain ⟨c, hc⟩ := (hkernel.2.2 (v.average f)).mp (by linarith)
    have h3 : ∑ x, s.p (v.site x) ^ 2 * v.weight x ^ 4 *
        (f x - v.average f (v.site x)) ^ 2 = 0 := by linarith
    rw [Finset.sum_eq_zero_iff_of_nonneg fun x _ => hterm f x] at h3
    refine ⟨c, fun x => ?_⟩
    have h4 := h3 x (Finset.mem_univ x)
    have hpos : 0 < s.p (v.site x) ^ 2 * v.weight x ^ 4 := by
      have := hp (v.site x); have := hk x; positivity
    have h5 : (f x - v.average f (v.site x)) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h4 with h | h
      · exact absurd h hpos.ne'
      · exact h
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h5
    rw [← hc (v.site x)]; linarith
  · rintro ⟨a, ha⟩
    have hf : f = fun _ => a := funext ha
    subst hf
    rw [hq]
    have havg : v.average (fun _ => a) = fun _ => a := by
      funext i; rw [average_const, hmass i, one_mul]
    rw [havg, (hkernel.2.2 _).mpr ⟨a, fun _ => rfl⟩]
    simp

theorem lift_broad (C : ℝ) (hC : 0 < C) (hw : ∀ x, 1 / 2 ≤ v.weight x ^ 2 ∧ v.weight x ^ 2 ≤ 1)
    (hb : ∀ i, ‖s.r i‖ ≤ C ∧ 1 / C ≤ s.p i ∧ s.p i ≤ C) (x : P) :
    ‖(v.liftState s).r x‖ ≤ C ∧ 1 / (2 * C) ≤ (v.liftState s).p x ∧
      (v.liftState s).p x ≤ C := by
  obtain ⟨hr, hp1, hp2⟩ := hb (v.site x)
  obtain ⟨hw1, hw2⟩ := hw x
  have hpx : (v.liftState s).p x = v.weight x ^ 2 * s.p (v.site x) :=
    AgentS45.lift_p_entry v s x
  refine ⟨?_, ?_, ?_⟩
  · have : (v.liftState s).r x = ((v.weight x ^ 2 : ℝ) : ℂ) * s.r (v.site x) := by
      simp [PortMap.liftState]
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (s.r (v.site x))]
  · rw [hpx]
    have : 1 / (2 * C) = 1 / 2 * (1 / C) := by field_simp
    rw [this]
    exact mul_le_mul hw1 hp1 (by positivity) (by nlinarith)
  · rw [hpx]; nlinarith [hp1, one_div_pos.mpr hC]

theorem lift_rows (hmass : ∀ i, v.mass i = 1) (a H : ℝ) (hw : ∀ x, v.weight x ^ 4 ≤ a)
    (hrow : ∀ i, s.fourthRow t Finset.univ i ≤ H) (hH : 0 ≤ H) (x : P) :
    (v.liftState s).fourthRow t Finset.univ x ≤ a * H := by
  rw [AgentS45.lift_fourthRow v s t hmass x]
  have h0 : 0 ≤ s.fourthRow t Finset.univ (v.site x) :=
    Finset.sum_nonneg fun _ _ => by positivity
  exact mul_le_mul (hw x) (hrow _) h0 ((by positivity : 0 ≤ v.weight x ^ 4).trans (hw x))

end AndersonAC.AgentS78
