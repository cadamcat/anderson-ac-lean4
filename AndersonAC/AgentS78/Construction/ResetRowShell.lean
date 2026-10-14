import AndersonAC.AgentS78.S45Join
import AndersonAC.S78Moment.Moments

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- Exponential shell bounds on any active subset of the torus, inherited from the
uniform torus moment estimates. -/
theorem physicalShellBounds (d : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {m n : ℕ} (A : Finset (Torus d m)) (e : Fin n ≃ A),
      AndersonAC.S45.ShellBounds d C
        (fun i j => physicalDistance d m (e i).val (e j).val) := by
  classical
  obtain ⟨C0, hC0, hM0⟩ :=
    AndersonAC.SolS78.lattice_exponential_moments_proof d 0 1 (by norm_num)
  obtain ⟨C2, hC2, hM2⟩ :=
    AndersonAC.SolS78.lattice_exponential_moments_proof d 2 1 (by norm_num)
  let C := max 1 (max C0 C2)
  have hC1 : 1 ≤ C := by dsimp [C]; exact le_max_left _ _
  have hC0le : C0 ≤ C := by
    dsimp [C]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hC2le : C2 ≤ C := by
    dsimp [C]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hm0 : ∀ (m : ℕ) (u : ℝ), 0 < u → u ≤ 1 → ∀ x : Torus d m,
      (∑ y, Real.exp (-u * physicalDistance d m x y)) ≤
        C0 * AndersonAC.S45.power u (-(d : ℝ)) := by
    intro m u hu hu1 x
    have h := hM0 m u hu hu1 x
    simpa [AndersonAC.S45.power, mul_comm, mul_left_comm, mul_assoc] using h
  have hm2 : ∀ (m : ℕ) (u : ℝ), 0 < u → u ≤ 1 → ∀ x : Torus d m,
      (∑ y, physicalDistance d m x y ^ 2 *
        Real.exp (-u * physicalDistance d m x y)) ≤
        C2 * AndersonAC.S45.power u (-(d : ℝ) - 2) := by
    intro m u hu hu1 x
    have h := hM2 m u hu hu1 x
    simpa [AndersonAC.S45.power, mul_comm, mul_left_comm, mul_assoc] using h
  refine ⟨C, hC1, ?_⟩
  intro m n A e
  let dist : Fin n → Fin n → ℝ := fun i j =>
    physicalDistance d m (e i).val (e j).val
  have hnonneg : ∀ i j, 0 ≤ dist i j := by
    intro i j
    change 0 ≤ ((nnGraph d m).dist (e i).val (e j).val : ℝ)
    exact_mod_cast Nat.zero_le ((nnGraph d m).dist (e i).val (e j).val)
  have hsymmetric : ∀ i j, dist i j = dist j i := by
    intro i j
    simp [dist, physicalDistance, SimpleGraph.dist_comm]
  have htriangle : ∀ i j k, dist i k ≤ dist i j + dist j k := by
    intro i j k
    change ((nnGraph d m).dist (e i).val (e k).val : ℝ) ≤
      ((nnGraph d m).dist (e i).val (e j).val : ℝ) +
        ((nnGraph d m).dist (e j).val (e k).val : ℝ)
    exact_mod_cast
      (AndersonAC.SolS78.nnGraph_connected_proof (d := d) (m := m)).dist_triangle
        (u := (e i).val) (v := (e j).val) (w := (e k).val)
  have hself : ∀ i, dist i i = 0 := by
    intro i
    simp [dist, physicalDistance, SimpleGraph.dist_self]
  have hcount : ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ i,
      (∑ j, Real.exp (-u * dist i j)) ≤ C * AndersonAC.S45.power u (-(d : ℝ)) := by
    intro u hu hu1 i
    let x := (e i).val
    have hfull := hm0 m u hu hu1 x
    have hactive :
        (∑ y ∈ A, Real.exp (-u * physicalDistance d m x y)) ≤
          ∑ y : Torus d m, Real.exp (-u * physicalDistance d m x y) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (by
        intro y hyA hy
        exact Real.exp_nonneg _)
    have hsum :
        (∑ j : Fin n, Real.exp (-u * dist i j)) =
          ∑ y ∈ A, Real.exp (-u * physicalDistance d m x y) := by
      simpa [dist, x] using
        AndersonAC.AgentS78.sum_active_equiv A e
          (fun y => Real.exp (-u * physicalDistance d m x y))
    have hpow : 0 ≤ AndersonAC.S45.power u (-(d : ℝ)) :=
      Real.rpow_nonneg hu.le _
    calc
      (∑ j, Real.exp (-u * dist i j)) =
          ∑ y ∈ A, Real.exp (-u * physicalDistance d m x y) := hsum
      _ ≤ ∑ y : Torus d m, Real.exp (-u * physicalDistance d m x y) := hactive
      _ ≤ C0 * AndersonAC.S45.power u (-(d : ℝ)) := hfull
      _ ≤ C * AndersonAC.S45.power u (-(d : ℝ)) :=
        mul_le_mul_of_nonneg_right hC0le hpow
  have hsecond : ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ i,
      (∑ j, dist i j ^ 2 * Real.exp (-u * dist i j)) ≤
        C * AndersonAC.S45.power u (-(d : ℝ) - 2) := by
    intro u hu hu1 i
    let x := (e i).val
    have hfull := hm2 m u hu hu1 x
    have hactive :
        (∑ y ∈ A, physicalDistance d m x y ^ 2 *
          Real.exp (-u * physicalDistance d m x y)) ≤
          ∑ y : Torus d m, physicalDistance d m x y ^ 2 *
            Real.exp (-u * physicalDistance d m x y) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (by
        intro y hyA hy
        exact mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))
    have hsum :
        (∑ j : Fin n, dist i j ^ 2 * Real.exp (-u * dist i j)) =
          ∑ y ∈ A, physicalDistance d m x y ^ 2 *
            Real.exp (-u * physicalDistance d m x y) := by
      simpa [dist, x] using
        AndersonAC.AgentS78.sum_active_equiv A e
          (fun y => physicalDistance d m x y ^ 2 *
            Real.exp (-u * physicalDistance d m x y))
    have hpow : 0 ≤ AndersonAC.S45.power u (-(d : ℝ) - 2) :=
      Real.rpow_nonneg hu.le _
    calc
      (∑ j, dist i j ^ 2 * Real.exp (-u * dist i j)) =
          ∑ y ∈ A, physicalDistance d m x y ^ 2 *
            Real.exp (-u * physicalDistance d m x y) := hsum
      _ ≤ ∑ y : Torus d m, physicalDistance d m x y ^ 2 *
            Real.exp (-u * physicalDistance d m x y) := hactive
      _ ≤ C2 * AndersonAC.S45.power u (-(d : ℝ) - 2) := hfull
      _ ≤ C * AndersonAC.S45.power u (-(d : ℝ) - 2) :=
        mul_le_mul_of_nonneg_right hC2le hpow
  exact ⟨hnonneg, hsymmetric, htriangle, hself, hcount, hsecond⟩

/-- Increasing the shell constant preserves the shell estimates. -/
theorem shellBounds_mono_fin {d n : ℕ} {C B : ℝ} {dist : Fin n → Fin n → ℝ}
    (hCB : C ≤ B) (h : AndersonAC.S45.ShellBounds d C dist) :
    AndersonAC.S45.ShellBounds d B dist := by
  refine ⟨h.nonneg, h.symmetric, h.triangle, h.self, ?_, ?_⟩
  · intro u hu hu1 i
    calc
      (∑ j, Real.exp (-u * dist i j)) ≤ C * AndersonAC.S45.power u (-(d : ℝ)) :=
        h.count u hu hu1 i
      _ ≤ B * AndersonAC.S45.power u (-(d : ℝ)) :=
        mul_le_mul_of_nonneg_right hCB (Real.rpow_nonneg hu.le _)
  · intro u hu hu1 i
    calc
      (∑ j, dist i j ^ 2 * Real.exp (-u * dist i j)) ≤
          C * AndersonAC.S45.power u (-(d : ℝ) - 2) := h.second u hu hu1 i
      _ ≤ B * AndersonAC.S45.power u (-(d : ℝ) - 2) :=
        mul_le_mul_of_nonneg_right hCB (Real.rpow_nonneg hu.le _)

end AndersonAC.AgentS78
