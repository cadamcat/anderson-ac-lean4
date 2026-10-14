import AndersonAC.S78.Definitions
import AndersonAC.S78Moment.Geometry

/-!
L = sideLength m transport of the graph gradient energy: on the physical torus
with side length > 2, the S78 graph energy of `nnGraph d m` equals the sum of
squared forward differences along the d basis directions (the §3 form).
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

private abbrev eb {d m : ℕ} (j : Fin d) : Torus d m := OAI.Anderson.torusBasisVector j

private theorem zmod_one_ne_zero {m : ℕ} (hm : 0 < m) :
    (1 : ZMod (OAI.Anderson.sideLength m)) ≠ 0 := by
  intro h
  have h' : ((1 : ℕ) : ZMod (OAI.Anderson.sideLength m)) = 0 := by exact_mod_cast h
  have hd := (ZMod.natCast_eq_zero_iff 1 _).mp h'
  have := Nat.le_of_dvd one_pos hd
  have := AndersonAC.SolS78.sideLength_gt_two hm
  omega

private theorem zmod_two_ne_zero {m : ℕ} (hm : 0 < m) :
    (1 : ZMod (OAI.Anderson.sideLength m)) + 1 ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod (OAI.Anderson.sideLength m)) = 0 := by
    rw [← h]; push_cast; ring
  have hd := (ZMod.natCast_eq_zero_iff 2 _).mp h'
  have := Nat.le_of_dvd two_pos hd
  have := AndersonAC.SolS78.sideLength_gt_two hm
  omega

private theorem eb_apply {d m : ℕ} (j k : Fin d) :
    (eb (m := m) j : Torus d m) k = if k = j then 1 else 0 := by
  simp [eb, OAI.Anderson.torusBasisVector, Pi.single_apply]

private theorem eb_ne_zero {d m : ℕ} (hm : 0 < m) (j : Fin d) : (eb (m := m) j : Torus d m) ≠ 0 := by
  intro h
  have := congrFun h j
  rw [eb_apply] at this
  simp only [if_true, Pi.zero_apply] at this
  exact zmod_one_ne_zero hm this

private theorem eb_inj {d m : ℕ} (hm : 0 < m) {j k : Fin d}
    (h : (eb (m := m) j : Torus d m) = eb k) : j = k := by
  by_contra hne
  have := congrFun h j
  rw [eb_apply, eb_apply] at this
  simp only [if_true, if_neg hne] at this
  exact zmod_one_ne_zero hm this

private theorem eb_add_ne_zero {d m : ℕ} (hm : 0 < m) (j k : Fin d) :
    (eb (m := m) j : Torus d m) + eb k ≠ 0 := by
  intro h
  have := congrFun h j
  rw [Pi.add_apply, eb_apply, eb_apply] at this
  simp only [if_true, Pi.zero_apply] at this
  by_cases hkj : j = k
  · rw [if_pos hkj] at this; exact zmod_two_ne_zero hm this
  · rw [if_neg hkj, add_zero] at this; exact zmod_one_ne_zero hm this

/-- Neighbour map: `inl j ↦ x + e_j`, `inr j ↦ x - e_j`. -/
private def nbr {d m : ℕ} (x : Torus d m) : Fin d ⊕ Fin d → Torus d m
  | Sum.inl j => x + eb j
  | Sum.inr j => x - eb j

private theorem nbr_injective {d m : ℕ} (hm : 0 < m) (x : Torus d m) :
    Function.Injective (nbr x) := by
  rintro (j | j) (k | k) h <;> simp only [nbr] at h
  · rw [eb_inj hm (add_left_cancel h)]
  · exfalso; apply eb_add_ne_zero hm j k
    have := congrArg (fun z => z - x + eb k) h
    rw [show x + eb j - x + eb k = eb j + eb k by abel,
      show x - eb k - x + eb k = (0 : Torus d m) by abel] at this
    exact this
  · exfalso; apply eb_add_ne_zero hm j k
    have := congrArg (fun z => x - z + eb k) h
    rw [show x - (x - eb j) + eb k = eb j + eb k by abel,
      show x - (x + eb k) + eb k = (0 : Torus d m) by abel] at this
    exact this
  · have := congrArg (fun z => x - z) h; simp only [sub_sub_cancel] at this
    rw [eb_inj hm this]

private theorem neighbours_eq {d m : ℕ} (hm : 0 < m) (x : Torus d m) [DecidablePred ((nnGraph d m).Adj x)] :
    Finset.univ.filter ((nnGraph d m).Adj x) = Finset.univ.image (nbr x) := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  rw [AndersonAC.SolS78.nnGraph_adj_iff_proof]
  constructor
  · rintro ⟨_, i, h | h | h | h⟩
    · exact ⟨Sum.inl i, h.symm⟩
    · exact ⟨Sum.inr i, h.symm⟩
    · exact ⟨Sum.inr i, by simp only [nbr]; rw [h]; abel⟩
    · exact ⟨Sum.inl i, by simp only [nbr]; rw [h]; abel⟩
  · rintro ⟨s, rfl⟩
    rcases s with j | j
    · refine ⟨?_, j, Or.inl rfl⟩
      intro h; apply eb_ne_zero hm j
      have := congrArg (fun z => z - x) h; simp only [nbr] at this
      rw [sub_self, add_sub_cancel_left] at this; exact this.symm
    · refine ⟨?_, j, Or.inr (Or.inl rfl)⟩
      intro h; apply eb_ne_zero hm j
      have := congrArg (fun z => x - z) h; simp only [nbr] at this
      rw [sub_self, sub_sub_cancel] at this; exact this.symm

/-- The S78 graph gradient energy is the forward-difference energy (L = sideLength m > 2). -/
theorem gradientEnergy_eq_steps {d m : ℕ} (hm : 0 < m) (f : Torus d m → ℝ) :
    gradientEnergy (nnGraph d m) f =
      ∑ x : Torus d m, ∑ j : Fin d, (f (x + OAI.Anderson.torusBasisVector j) - f x) ^ 2 := by
  classical
  have hrow : ∀ x : Torus d m,
      (∑ y, if (nnGraph d m).Adj x y then (f x - f y) ^ 2 else 0) =
        (∑ j : Fin d, (f x - f (x + eb j)) ^ 2) + ∑ j : Fin d, (f x - f (x - eb j)) ^ 2 := by
    intro x
    rw [← Finset.sum_filter, neighbours_eq hm x, Finset.sum_image (fun a _ b _ h => nbr_injective hm x h),
      Fintype.sum_sum_type]
    rfl
  have hback : ∀ j : Fin d, (∑ x : Torus d m, (f x - f (x - eb j)) ^ 2) =
      ∑ x : Torus d m, (f (x + eb j) - f x) ^ 2 := by
    intro j
    exact Fintype.sum_equiv (Equiv.subRight (eb (m := m) j : Torus d m)) _ _
      (fun x => by simp only [Equiv.subRight_apply, sub_add_cancel])
  unfold gradientEnergy
  have e : (∑ i, ∑ j, if (nnGraph d m).Adj i j then (f i - f j) ^ 2 else 0) =
      2 * ∑ x : Torus d m, ∑ j : Fin d, (f (x + eb j) - f x) ^ 2 := by
    have hsecond : (∑ x : Torus d m, ∑ j : Fin d, (f x - f (x - eb j)) ^ 2) =
        ∑ x : Torus d m, ∑ j : Fin d, (f (x + eb j) - f x) ^ 2 := by
      rw [Finset.sum_comm, Finset.sum_congr rfl fun j _ => hback j, Finset.sum_comm]
    rw [Finset.sum_congr rfl fun x _ => hrow x, Finset.sum_add_distrib, hsecond, two_mul]
    congr 1
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  ring

end AndersonAC.AgentS78
