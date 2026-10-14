import AndersonAC.AgentS78.Construction.TorusShell
import AndersonAC.AgentS78.Construction.TileCoverGeneric

/-!
# WP10 construction: the §5 tile covers — kernel energy on the torus

agent-s78cover (2026-10-14; takeover of luna-s78torus). `torusKernel_proof : ∀ d,
TorusKernelStatement d`: `Σ_{x,y} e^{-u dist(x,y)} (v_x - v_y)² ≤ C u^{-d-2} Λ(v)`, by
translation invariance and a shortest walk (`Σ_x (v_x - v_{x+z})² ≤ 2 dist(0,z)² Λ(v)`) and the
second shell moment.
-/

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

theorem adj_translate {p q : Torus d m} (h : (nnGraph d m).Adj p q) (x : Torus d m) :
    (nnGraph d m).Adj x (x + (q - p)) := by
  obtain ⟨hne, i, hi⟩ := (nn_adj_iff p q).1 h
  refine (nn_adj_iff _ _).2 ⟨fun h' => hne ?_, i, ?_⟩
  · have : q - p = 0 := by
      have := congrArg (fun z => z - x) h'
      simp only [sub_self, add_sub_cancel_left] at this
      exact this.symm
    exact (sub_eq_zero.mp this).symm
  · rcases hi with hi | hi
    · left; rw [hi]; abel
    · right; rw [hi]; abel

theorem sum_shift_sq_le (v : Torus d m → ℝ) (s : Torus d m)
    (hs : ∀ x, (nnGraph d m).Adj x (x + s)) :
    ∑ x, (v x - v (x + s)) ^ 2 ≤ 2 * torusEnergy d m v := by
  classical
  unfold torusEnergy gradientEnergy
  rw [← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul]
  refine Finset.sum_le_sum fun x _ => ?_
  have h := Finset.single_le_sum
    (f := fun y => if (nnGraph d m).Adj x y then (v x - v y) ^ 2 else 0)
    (fun y _ => by split_ifs <;> positivity) (Finset.mem_univ (x + s))
  simp only [if_pos (hs x)] at h
  convert h

theorem sum_walk_sq_le (v : Torus d m → ℝ) {a b : Torus d m} (w : (nnGraph d m).Walk a b) :
    ∑ x, (v (x + a) - v (x + b)) ^ 2 ≤ 2 * (w.length : ℝ) ^ 2 * torusEnergy d m v := by
  induction w with
  | nil => simp
  | @cons a c b h w ih =>
    have hΛ := torusEnergy_nonneg (d := d) (m := m) v
    have hA : ∑ x, (v (x + a) - v (x + c)) ^ 2 ≤ 2 * torusEnergy d m v := by
      have e : ∑ x, (v x - v (x + (c - a))) ^ 2 = ∑ x, (v (x + a) - v (x + c)) ^ 2 := by
        rw [← Equiv.sum_comp (Equiv.addRight a) (fun x => (v x - v (x + (c - a))) ^ 2)]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [Equiv.coe_addRight]
        rw [show x + a + (c - a) = x + c by abel]
      rw [← e]; exact sum_shift_sq_le v (c - a) (adj_translate h)
    rw [SimpleGraph.Walk.length_cons]
    set n : ℕ := w.length with hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · have hcb : c = b := SimpleGraph.Walk.eq_of_length_eq_zero (by rw [← hn, h0])
      subst hcb
      simp only [h0, zero_add, Nat.cast_one, one_pow, mul_one]
      exact hA
    · have hnr : (0 : ℝ) < n := by exact_mod_cast hpos
      have hpt : ∀ x, (n : ℝ) * (v (x + a) - v (x + b)) ^ 2 ≤
          n * (n + 1) * (v (x + a) - v (x + c)) ^ 2 + (n + 1) * (v (x + c) - v (x + b)) ^ 2 := by
        intro x
        nlinarith [sq_nonneg ((n : ℝ) * (v (x + a) - v (x + c)) - (v (x + c) - v (x + b)))]
      have hsum : (n : ℝ) * ∑ x, (v (x + a) - v (x + b)) ^ 2 ≤
          n * (n + 1) * ∑ x, (v (x + a) - v (x + c)) ^ 2 +
            (n + 1) * ∑ x, (v (x + c) - v (x + b)) ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun x _ => hpt x
      have h1 : n * (n + 1) * ∑ x, (v (x + a) - v (x + c)) ^ 2 ≤
          n * (n + 1) * (2 * torusEnergy d m v) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
      have h2 : ((n : ℝ) + 1) * ∑ x, (v (x + c) - v (x + b)) ^ 2 ≤
          (n + 1) * (2 * (n : ℝ) ^ 2 * torusEnergy d m v) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      have key : (n : ℝ) * ∑ x, (v (x + a) - v (x + b)) ^ 2 ≤
          n * (2 * ((n : ℝ) + 1) ^ 2 * torusEnergy d m v) := by nlinarith
      push_cast
      exact le_of_mul_le_mul_left key hnr

theorem torusKernel_proof : ∀ d, TorusKernelStatement d := by
  intro d
  obtain ⟨Cs, hCs, hshell⟩ := torusShell_proof d
  refine ⟨2 * Cs, by positivity, fun m u hu hu1 v => ?_⟩
  have hΛ := torusEnergy_nonneg (d := d) (m := m) v
  have hconn := torusConnected_proof d m
  -- translation invariance of the distance
  have htr : ∀ x z : Torus d m, physicalDistance d m x (x + z) = physicalDistance d m 0 z := by
    intro x z
    rw [torusMetric_proof, torusMetric_proof]
    unfold l1Dist
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp
  have hδ : ∀ z : Torus d m, ∑ x, (v x - v (x + z)) ^ 2 ≤
      2 * physicalDistance d m 0 z ^ 2 * torusEnergy d m v := by
    intro z
    obtain ⟨w, hw⟩ := hconn.exists_walk_length_eq_dist 0 z
    have h := sum_walk_sq_le v w
    simp only [add_zero] at h
    unfold physicalDistance
    rw [← hw]
    exact h
  calc (∑ x, ∑ y, Real.exp (-u * physicalDistance d m x y) * (v x - v y) ^ 2)
      = ∑ x, ∑ z, Real.exp (-u * physicalDistance d m x (x + z)) * (v x - v (x + z)) ^ 2 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        exact (Equiv.sum_comp (Equiv.addLeft x)
          (fun y => Real.exp (-u * physicalDistance d m x y) * (v x - v y) ^ 2)).symm
    _ = ∑ z, Real.exp (-u * physicalDistance d m 0 z) * ∑ x, (v x - v (x + z)) ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [htr]
    _ ≤ ∑ z, Real.exp (-u * physicalDistance d m 0 z) *
          (2 * physicalDistance d m 0 z ^ 2 * torusEnergy d m v) :=
        Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hδ z) (Real.exp_pos _).le
    _ = 2 * torusEnergy d m v * ∑ z, physicalDistance d m 0 z ^ 2 *
          Real.exp (-u * physicalDistance d m 0 z) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        ring
    _ ≤ 2 * torusEnergy d m v * (Cs * S45.power u (-(d : ℝ) - 2)) :=
        mul_le_mul_of_nonneg_left (hshell m u hu hu1 0).2 (by positivity)
    _ = 2 * Cs * S45.power u (-(d : ℝ) - 2) * torusEnergy d m v := by ring

end AndersonAC.AgentS78
