import AndersonAC.AgentS78.Construction.PhysicalIdentity
import AndersonAC.AgentS78Geo.TerminalMetric
import AndersonAC.S78Moment.Geometry

/-!
# The `hops` clause of `geo` from the physical identity

06-clearing.tex:207–212: "Every nonzero off-diagonal entry of M is either a direct lattice hop
or comes from the terminal Schur correction. The latter correction is block supported on active
neighbors of a connected terminal component". If the record satisfies `PhysicalIdentity E x`
(its `M` is the active Schur complement of `H − E` with installed potentials,
02-state.tex:231–247) and every inactive site lies in a set `Tset`, then on active pairs
`M a b` is the lattice hop unless `d_Tset(a,b) = 0`. The terminal block's inverse is supported
on pairs at zero collapsed distance because it commutes with the class projection
`{v | d_Tset(s, v) = 0}`.
-/

open scoped BigOperators Matrix
set_option autoImplicit false
noncomputable section

namespace AndersonAC.AgentS78Geo

open AndersonAC.S78 AndersonAC.AgentS78

variable {d m : ℕ}

/-- The hopping (off-diagonal) part of the lattice Hamiltonian. -/
def hopMatrix (d m : ℕ) : Matrix (Torus d m) (Torus d m) ℝ := fun a b =>
  if a = b then 0 else
    -∑ j : Fin d, ((if b = a + OAI.Anderson.torusBasisVector j then (1 : ℝ) else 0) +
      (if b = a - OAI.Anderson.torusBasisVector j then (1 : ℝ) else 0))

theorem installedShifted_offdiag (E : ℝ) (x : RunRecord d m) {a b : Torus d m} (hab : a ≠ b) :
    installedShifted E x a b = ((hopMatrix d m a b : ℝ) : ℂ) := by
  simp only [installedShifted, hopMatrix, OAI.Anderson.periodicHamiltonian, Matrix.add_apply,
    Matrix.sub_apply, Matrix.diagonal_apply_ne _ hab, Matrix.smul_apply, Matrix.one_apply_ne hab,
    if_neg hab]
  push_cast
  rw [smul_zero, add_zero, add_zero, sub_zero, neg_inj]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem basis_coord {i j : Fin d} :
    (OAI.Anderson.torusBasisVector j : Torus d m) i = if i = j then 1 else 0 := by
  simp [OAI.Anderson.torusBasisVector, Pi.single_apply]

theorem two_ne_zero_zmod (hm : 0 < m) : (2 : ZMod (OAI.Anderson.sideLength m)) ≠ 0 := by
  have hN : 2 < OAI.Anderson.sideLength m := AndersonAC.SolS78.sideLength_gt_two hm
  intro h
  have := congrArg ZMod.val h
  rw [ZMod.val_zero, show (2 : ZMod (OAI.Anderson.sideLength m)) =
    ((2 : ℕ) : ZMod (OAI.Anderson.sideLength m)) by norm_num, ZMod.val_natCast_of_lt hN] at this
  omega

theorem one_ne_zero_zmod (hm : 0 < m) : (1 : ZMod (OAI.Anderson.sideLength m)) ≠ 0 := by
  have hN : 2 < OAI.Anderson.sideLength m := AndersonAC.SolS78.sideLength_gt_two hm
  haveI : Fact (1 < OAI.Anderson.sideLength m) := ⟨by omega⟩
  exact one_ne_zero

/-- At most one lattice direction joins two sites. -/
theorem hop_unique (hm : 0 < m) {a b : Torus d m} {j k : Fin d} {s₁ s₂ : Bool}
    (h₁ : b = if s₁ then a + OAI.Anderson.torusBasisVector j else a - OAI.Anderson.torusBasisVector j)
    (h₂ : b = if s₂ then a + OAI.Anderson.torusBasisVector k else a - OAI.Anderson.torusBasisVector k) :
    j = k ∧ s₁ = s₂ := by
  have h1 := one_ne_zero_zmod (m := m) hm
  have h2 := two_ne_zero_zmod (m := m) hm
  have hc := fun i => congrFun (h₁.symm.trans h₂) i
  have hj := hc j
  by_cases hjk : j = k
  · subst hjk
    refine ⟨rfl, ?_⟩
    cases s₁ <;> cases s₂ <;> simp_all [basis_coord]
    · apply h2; linear_combination -hj
    · apply h2; linear_combination hj
  · exfalso
    cases s₁ <;> cases s₂ <;> simp [basis_coord, hjk] at hj <;> first | exact h1 hj | exact h1 (neg_eq_zero.mp hj) | exact h1 hj.symm | exact h1 (neg_eq_zero.mp hj.symm)

theorem hopMatrix_abs_le (hm : 0 < m) (a b : Torus d m) : |hopMatrix d m a b| ≤ 1 := by
  unfold hopMatrix
  split_ifs with hab
  · simp
  · by_cases hex : ∃ j₀, b = a + OAI.Anderson.torusBasisVector j₀ ∨
        b = a - OAI.Anderson.torusBasisVector j₀
    · obtain ⟨j₀, hj₀⟩ := hex
      obtain ⟨s₀, hs₀⟩ : ∃ s₀ : Bool, b = if s₀ then a + OAI.Anderson.torusBasisVector j₀
          else a - OAI.Anderson.torusBasisVector j₀ := by
        rcases hj₀ with h | h
        · exact ⟨true, by simpa using h⟩
        · exact ⟨false, by simpa using h⟩
      rw [Finset.sum_eq_single j₀]
      · rw [abs_neg]
        cases s₀
        · have hne : b ≠ a + OAI.Anderson.torusBasisVector j₀ := by
            intro h
            have := hop_unique hm (s₁ := false) (s₂ := true) hs₀ (by simpa using h)
            simp at this
          simp at hs₀
          subst hs₀
          simp [hne]
        · have hne : b ≠ a - OAI.Anderson.torusBasisVector j₀ := by
            intro h
            have := hop_unique hm (s₁ := true) (s₂ := false) hs₀ (by simpa using h)
            simp at this
          simp at hs₀
          subst hs₀
          simp [hne]
      · intro k _ hk
        have h1 : b ≠ a + OAI.Anderson.torusBasisVector k := by
          intro h
          exact hk (hop_unique hm (s₂ := true) hs₀ (by simpa using h)).1.symm
        have h2 : b ≠ a - OAI.Anderson.torusBasisVector k := by
          intro h
          exact hk (hop_unique hm (s₂ := false) hs₀ (by simpa using h)).1.symm
        simp [h1, h2]
      · intro h; exact absurd (Finset.mem_univ j₀) h
    · push_neg at hex
      have : ∀ j : Fin d, ((if b = a + OAI.Anderson.torusBasisVector j then (1 : ℝ) else 0) +
          (if b = a - OAI.Anderson.torusBasisVector j then (1 : ℝ) else 0)) = 0 := by
        intro j; simp [(hex j).1, (hex j).2]
      simp [this]

theorem hopMatrix_adj {a b : Torus d m} (h : hopMatrix d m a b ≠ 0) : (nnGraph d m).Adj a b := by
  unfold hopMatrix at h
  split_ifs at h with hab
  · exact absurd rfl h
  · by_contra hadj
    apply h
    have hz : ∀ j : Fin d, ((if b = a + OAI.Anderson.torusBasisVector j then (1 : ℝ) else 0) +
        (if b = a - OAI.Anderson.torusBasisVector j then (1 : ℝ) else 0)) = 0 := by
      intro j
      have h1 : b ≠ a + OAI.Anderson.torusBasisVector j := fun hb =>
        hadj ((AndersonAC.SolS78.nnGraph_adj_iff_proof a b).mpr ⟨hab, j, Or.inl hb⟩)
      have h2 : b ≠ a - OAI.Anderson.torusBasisVector j := fun hb =>
        hadj ((AndersonAC.SolS78.nnGraph_adj_iff_proof a b).mpr ⟨hab, j, Or.inr (Or.inl hb)⟩)
      simp [h1, h2]
    simp [hz]

theorem hopMatrix_symm : (hopMatrix d m).IsSymm := by
  apply Matrix.IsSymm.ext
  intro a b
  unfold hopMatrix
  by_cases hab : a = b
  · subst hab; rfl
  · rw [if_neg (Ne.symm hab), if_neg hab]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 : (a = b + OAI.Anderson.torusBasisVector j) ↔
        (b = a - OAI.Anderson.torusBasisVector j) := by
      constructor <;> intro h <;> rw [h] <;> abel
    have e2 : (a = b - OAI.Anderson.torusBasisVector j) ↔
        (b = a + OAI.Anderson.torusBasisVector j) := by
      constructor <;> intro h <;> rw [h] <;> abel
    simp only [e1, e2]
    ring

/-- Inverse of a matrix whose entries join only `R`-related indices, for an equivalence-like
class predicate: entries of the inverse join only related indices. -/
theorem inv_supported_on_class {κ : Type} [Fintype κ] [DecidableEq κ] (D : Matrix κ κ ℂ)
    (R : κ → κ → Prop) (hrefl : ∀ s, R s s)
    (hD : ∀ s u v, D u v ≠ 0 → (R s u ↔ R s v)) (s s' : κ) (h : D⁻¹ s s' ≠ 0) : R s s' := by
  classical
  let P : Matrix κ κ ℂ := Matrix.diagonal (fun v => if R s v then 1 else 0)
  have hPD : P * D = D * P := by
    ext u v
    simp only [P, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases huv : D u v = 0
    · simp [huv]
    · have := hD s u v huv
      by_cases hu : R s u
      · simp [hu, this.mp hu]
      · have hv : ¬R s v := fun hv => hu (this.mpr hv)
        simp [hu, hv]
  have hPDinv : P * D⁻¹ = D⁻¹ * P := by
    by_cases hunit : IsUnit D.det
    · calc P * D⁻¹ = D⁻¹ * D * P * D⁻¹ := by rw [Matrix.nonsing_inv_mul D hunit, Matrix.one_mul]
        _ = D⁻¹ * (P * D) * D⁻¹ := by rw [hPD]; simp only [Matrix.mul_assoc]
        _ = D⁻¹ * P := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv D hunit, Matrix.mul_one]
    · rw [Matrix.nonsing_inv_apply_not_isUnit D hunit]; simp
  have he := congrFun (congrFun hPDinv s) s'
  simp only [P, Matrix.diagonal_mul, Matrix.mul_diagonal, if_pos (hrefl s), one_mul] at he
  by_contra hR
  rw [if_neg hR, mul_zero] at he
  exact h he

/-- **The `hops` clause from the physical identity.** -/
theorem hops_of_physicalIdentity (hm : 0 < m) (E : ℝ) (x : RunRecord d m)
    (hphys : PhysicalIdentity E x) (Tset : Finset (Torus d m))
    (hT : ∀ y, y ∉ x.endpoint.active → y ∈ Tset) :
    ∃ J : Matrix (Torus d m) (Torus d m) ℝ, J.IsSymm ∧ (∀ a b, |J a b| ≤ 1) ∧
      (∀ a b, J a b ≠ 0 → (nnGraph d m).Adj a b) ∧
      ∀ a ∈ x.endpoint.active, ∀ b ∈ x.endpoint.active,
        x.endpoint.M a b ≠ ((J a b : ℝ) : ℂ) → terminalDistance (nnGraph d m) Tset a b = 0 := by
  classical
  have hG : (nnGraph d m).Connected := AndersonAC.SolS78.nnGraph_connected_proof
  set A := x.endpoint.active
  -- off-diagonal entries of `Hm` are hops
  have hHadj : ∀ u v, u ≠ v → (installedShifted E x) u v ≠ 0 → (nnGraph d m).Adj u v := by
    intro u v huv h
    apply hopMatrix_adj
    intro h0
    apply h
    rw [installedShifted_offdiag E x huv, h0]; simp
  refine ⟨hopMatrix d m, hopMatrix_symm, hopMatrix_abs_le hm, fun a b h => hopMatrix_adj h, ?_⟩
  intro a ha b hb hne
  by_cases hab : a = b
  · subst hab; exact terminalDistance_self _ _ _
  · -- entry of the physical identity
    have hpi := congrFun (congrFun hphys ⟨a, ha⟩) ⟨b, hb⟩
    simp only [Matrix.submatrix_apply, AndersonAC.SolS78.activeSchur, Matrix.sub_apply] at hpi
    rw [installedShifted_offdiag E x hab] at hpi
    -- the Schur correction is nonzero
    set D := (installedShifted E x).submatrix (fun i : {i // i ∉ A} => i.val) (fun i : {i // i ∉ A} => i.val)
    have hcorr : ((installedShifted E x).submatrix (fun i : A => i.val) (fun i : {i // i ∉ A} => i.val) * D⁻¹ *
        (installedShifted E x).submatrix (fun i : {i // i ∉ A} => i.val) (fun i : A => i.val)) ⟨a, ha⟩ ⟨b, hb⟩ ≠ 0 := by
      intro h0
      apply hne
      rw [hpi, h0, sub_zero]
    rw [Matrix.mul_apply] at hcorr
    obtain ⟨s', _, hs'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcorr
    have hW : (installedShifted E x) s'.val b ≠ 0 := right_ne_zero_of_mul hs'
    have hVD := left_ne_zero_of_mul hs'
    rw [Matrix.mul_apply] at hVD
    obtain ⟨s, _, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hVD
    have hV : (installedShifted E x) a s.val ≠ 0 := left_ne_zero_of_mul hs
    have hDinv : D⁻¹ s s' ≠ 0 := right_ne_zero_of_mul hs
    have hsT : s.val ∈ Tset := hT _ s.2
    have hs'T : s'.val ∈ Tset := hT _ s'.2
    have has : a ≠ s.val := fun h => s.2 (h ▸ ha)
    have hs'b : s'.val ≠ b := fun h => s'.2 (h ▸ hb)
    have d1 : terminalDistance (nnGraph d m) Tset a s.val = 0 :=
      terminalDistance_adj_terminal _ _ (hHadj _ _ has hV) (Or.inr hsT)
    have d3 : terminalDistance (nnGraph d m) Tset s'.val b = 0 :=
      terminalDistance_adj_terminal _ _ (hHadj _ _ hs'b hW) (Or.inl hs'T)
    -- the terminal inverse joins only sites at zero collapsed distance
    have d2 : terminalDistance (nnGraph d m) Tset s.val s'.val = 0 := by
      refine inv_supported_on_class D
        (fun u v => terminalDistance (nnGraph d m) Tset u.val v.val = 0)
        (fun u => terminalDistance_self _ _ _) ?_ s s' hDinv
      intro w u v huv
      have huv0 : terminalDistance (nnGraph d m) Tset u.val v.val = 0 := by
        by_cases h : u = v
        · subst h; exact terminalDistance_self _ _ _
        · have hne' : u.val ≠ v.val := fun h' => h (Subtype.ext h')
          exact terminalDistance_adj_terminal _ _ (hHadj _ _ hne' huv) (Or.inl (hT _ u.2))
      have hvu0 : terminalDistance (nnGraph d m) Tset v.val u.val = 0 := by
        rw [terminalDistance_symm hG]; exact huv0
      have hnn := terminalDistance_nonneg (nnGraph d m) Tset
      constructor
      · intro h
        have := terminalDistance_triangle hG Tset w.val u.val v.val
        linarith [hnn w.val v.val]
      · intro h
        have := terminalDistance_triangle hG Tset w.val v.val u.val
        linarith [hnn w.val u.val]
    have hnn := terminalDistance_nonneg (nnGraph d m) Tset a b
    have t1 := terminalDistance_triangle hG Tset a s.val b
    have t2 := terminalDistance_triangle hG Tset s.val s'.val b
    linarith

end AndersonAC.AgentS78Geo
