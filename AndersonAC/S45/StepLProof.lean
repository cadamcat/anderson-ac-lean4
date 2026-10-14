import AndersonAC.S45.HelperStatements2

noncomputable section
open Matrix
open scoped BigOperators

namespace AndersonAC.AgentS45

private theorem matrix_mask_apply {P α : Type*} [Fintype P] [DecidableEq P] [Zero α]
    (S : Finset P) (A : Matrix P P α) (i j : P) :
    AndersonAC.S45.mask S A i j = if i ∈ S then if j ∈ S then A i j else 0 else 0 := by
  simp [AndersonAC.S45.mask, AndersonAC.S45.pad, AndersonAC.S45.restrict]

private theorem matrix_mask_isSymm {P α : Type*} [Fintype P] [DecidableEq P] [Zero α]
    (S : Finset P) (A : Matrix P P α)
    (hA : (AndersonAC.S45.restrict A S).IsSymm) :
    (AndersonAC.S45.mask S A).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · have hs := hA.apply ⟨i, hi⟩ ⟨j, hj⟩
    simpa [matrix_mask_apply, AndersonAC.S45.restrict, hi, hj] using hs
  · simp [matrix_mask_apply, hi, hj]
  · simp [matrix_mask_apply, hi, hj]
  · simp [matrix_mask_apply, hi, hj]

private theorem laplacian_isSymm {P : Type*} [Fintype P] [DecidableEq P]
    (c : AndersonAC.S45.RMat P) (hc : c.IsSymm) :
    (AndersonAC.S45.laplacian c).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := fun h => hij h.symm
    simp [AndersonAC.S45.laplacian, hij, hji, hc.apply i j]

private theorem sum_offdiag_eq_erase {α : Type*} {P : Type*} [Fintype P] [DecidableEq P]
    [AddCommMonoid α] (f : P → α) (i : P) :
    (∑ j, if j = i then 0 else f j) = ∑ j ∈ Finset.univ.erase i, f j := by
  calc
    (∑ j, if j = i then 0 else f j) =
        ∑ j, if j ∈ Finset.univ.erase i then f j else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hji : j = i <;> simp [Finset.mem_erase, hji]
    _ = ∑ j ∈ Finset.univ.erase i, f j := by
          exact Finset.sum_ite_mem_eq (Finset.univ.erase i) f

private theorem laplacian_mulVec_one {P : Type*} [Fintype P] [DecidableEq P]
    (c : AndersonAC.S45.RMat P) :
    AndersonAC.S45.laplacian c *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  ext i
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [Pi.zero_apply, mul_one]
  have hdiag : AndersonAC.S45.laplacian c i i =
      ∑ j ∈ Finset.univ.erase i, c i j := by
    simpa [AndersonAC.S45.laplacian, Matrix.diagonal] using
      (sum_offdiag_eq_erase (fun j => c i j) i)
  have hoff : (∑ j ∈ Finset.univ.erase i, AndersonAC.S45.laplacian c i j) =
      - ∑ j ∈ Finset.univ.erase i, c i j := by
    calc
      (∑ j ∈ Finset.univ.erase i, AndersonAC.S45.laplacian c i j) =
          ∑ j ∈ Finset.univ.erase i, -c i j := by
            apply Finset.sum_congr rfl
            intro j hj
            have hji : j ≠ i := Finset.ne_of_mem_erase hj
            have hij : i ≠ j := fun e => hji e.symm
            simp [AndersonAC.S45.laplacian, hij]
      _ = - ∑ j ∈ Finset.univ.erase i, c i j := by
            rw [Finset.sum_neg_distrib]
  rw [← Finset.add_sum_erase (s := Finset.univ)
    (f := fun j => AndersonAC.S45.laplacian c i j) (Finset.mem_univ i)]
  rw [hdiag, hoff]
  ring

private theorem pad_isSymm {P : Type*} [Fintype P] [DecidableEq P]
    (S : Finset P) (A : Matrix S S ℝ) (hA : A.IsSymm) :
    (AndersonAC.S45.pad S A).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simpa [AndersonAC.S45.pad, hi, hj] using hA.apply ⟨i, hi⟩ ⟨j, hj⟩
  · simp [AndersonAC.S45.pad, hi, hj]
  · simp [AndersonAC.S45.pad, hi, hj]
  · simp [AndersonAC.S45.pad, hi, hj]

private theorem pad_mulVec_one {P : Type*} [Fintype P] [DecidableEq P]
    (S : Finset P) (A : Matrix S S ℝ)
    (hA : A *ᵥ (fun _ => (1 : ℝ)) = 0) :
    AndersonAC.S45.pad S A *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  classical
  ext i
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [Pi.zero_apply, mul_one]
  by_cases hi : i ∈ S
  · have hrow : (∑ j : S, A ⟨i, hi⟩ j) = 0 := by
      have hr := congrFun hA ⟨i, hi⟩
      simpa [Matrix.mulVec_apply_eq_sum] using hr
    have hsum : (∑ j, if hj : j ∈ S then A ⟨i, hi⟩ ⟨j, hj⟩ else 0) =
        ∑ j : S, A ⟨i, hi⟩ j := by
      let f : P → ℝ := fun j => if hj : j ∈ S then A ⟨i, hi⟩ ⟨j, hj⟩ else 0
      calc
        (∑ j, if hj : j ∈ S then A ⟨i, hi⟩ ⟨j, hj⟩ else 0) =
            ∑ j ∈ S, f j := by
              calc
                (∑ j, if hj : j ∈ S then A ⟨i, hi⟩ ⟨j, hj⟩ else 0) =
                    ∑ j, if hj : j ∈ S then f j else 0 := by
                      apply Finset.sum_congr rfl
                      intro j _
                      by_cases hj : j ∈ S <;> simp [f, hj]
                _ = ∑ j ∈ S, f j := Finset.sum_ite_mem_eq S f
        _ = ∑ j : S, A ⟨i, hi⟩ j := by
              simpa [f] using (Finset.sum_coe_sort S f).symm
    simpa [AndersonAC.S45.pad, hi] using hsum.trans hrow
  · simp [AndersonAC.S45.pad, hi]

private theorem matrix_mask_mulVec_one_of_support {P : Type*} [Fintype P]
    [DecidableEq P] (S : Finset P) (A : Matrix P P ℝ)
    (hA : A *ᵥ (fun _ => (1 : ℝ)) = 0)
    (hzero : ∀ i ∈ S, ∀ j ∉ S, A i j = 0) :
    AndersonAC.S45.mask S A *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  classical
  ext i
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [Pi.zero_apply, mul_one]
  by_cases hi : i ∈ S
  · have hfull : (∑ j, A i j) = 0 := by
      have hr := congrFun hA i
      simpa [Matrix.mulVec_apply_eq_sum] using hr
    have hsum : (∑ j, if j ∈ S then A i j else 0) = ∑ j, A i j := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ S
      · simp [hj]
      · simp [hj, hzero i hi j hj]
    simp [matrix_mask_apply, hi]
    rw [← Finset.sum_ite_mem_eq S (fun j => A i j), hsum, hfull]
  · simp [matrix_mask_apply, hi]

private theorem ambient_g_isSymm {P : Type*} [Fintype P] [DecidableEq P]
    (a : AndersonAC.S45.LiveState P) (r : P → ℂ)
    (hg : ((a.state r).g).IsSymm) : ((a.ambient r).g).IsSymm := by
  have hr : (AndersonAC.S45.restrict a.g a.live).IsSymm := by
    simpa [AndersonAC.S45.LiveState.state] using hg
  simpa [AndersonAC.S45.LiveState.ambient] using
    matrix_mask_isSymm a.live a.g hr

private theorem ambient_h_zero_right {P : Type*} [Fintype P] [DecidableEq P]
    (a : AndersonAC.S45.LiveState P) (r : P → ℂ) (t : ℝ) (i : P) {j : P}
    (hj : j ∉ a.live) : (a.ambient r).h t i j = 0 := by
  simp [AndersonAC.S45.LiveState.ambient, AndersonAC.S45.State.h, hj,
    AndersonAC.S45.mask, AndersonAC.S45.pad, AndersonAC.S45.restrict]

private theorem Ledge_isSymm_of_g_isSymm {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : AndersonAC.S45.State P) (x : P) (ξ : ℝ)
    (hg : s.g.IsSymm) : (AndersonAC.S45.Ledge t s x ξ).IsSymm := by
  have hh : (s.h t).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp [AndersonAC.S45.State.h, Matrix.IsSymm.apply hg i j]
  have hF : (s.F t).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp [AndersonAC.S45.State.F, AndersonAC.S45.entryAbsSquare,
      Matrix.IsSymm.apply hh i j]
  apply Matrix.IsSymm.ext
  intro i j
  simp only [AndersonAC.S45.Ledge]
  rw [Matrix.IsSymm.apply hh i.1 j.1, Matrix.IsSymm.apply hh x j.1,
    Matrix.IsSymm.apply hh i.1 x, Matrix.IsSymm.apply hF x j.1,
    Matrix.IsSymm.apply hF i.1 x]
  have hprod :
      AndersonAC.S45.gamma t s x ξ * star (s.h t i.1 j.1) * s.h t x j.1 * s.h t i.1 x =
      AndersonAC.S45.gamma t s x ξ * star (s.h t i.1 j.1) * s.h t i.1 x * s.h t x j.1 := by
    ring
  rw [hprod]
  ring

private theorem Ledge_zero_right {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : AndersonAC.S45.State P) (x : P) (ξ : ℝ)
    (i : AndersonAC.S45.survivors x)
    (j : AndersonAC.S45.survivors x)
    (hcol : ∀ i : P, s.h t i j.1 = 0) :
    AndersonAC.S45.Ledge t s x ξ i j = 0 := by
  simp [AndersonAC.S45.Ledge, AndersonAC.S45.State.F,
    AndersonAC.S45.entryAbsSquare, hcol]

theorem stepLLaplacian_proof : AndersonAC.AgentS45.StepLLaplacian := by
  intro P hP hDec q t r hwell hsym k hk
  classical
  rcases hp : q.pivot k with _ | x
  · simp [AndersonAC.S45.Sequence.stepL, hp]
  · have hrel : AndersonAC.S45.StepRel t r (q.state k) (q.state (k + 1)) x
        (q.scalar k) := by
      simpa [hp] using hwell.2 k hk
    have hnext : (q.state (k + 1)).live = (q.state k).live.erase x := hrel.survivors
    let a : AndersonAC.S45.LiveState P := q.state k
    let s : AndersonAC.S45.State P := a.ambient r
    have hgs : s.g.IsSymm := by
      exact ambient_g_isSymm a r (hsym k (Nat.le_of_lt hk))
    have hledgeSymm : (AndersonAC.S45.Ledge t s x (q.scalar k)).IsSymm :=
      Ledge_isSymm_of_g_isSymm t s x (q.scalar k) hgs
    have hlapSymm :
        (AndersonAC.S45.laplacian (AndersonAC.S45.Ledge t s x (q.scalar k))).IsSymm :=
      laplacian_isSymm _ hledgeSymm
    have hincSymm :
        (AndersonAC.S45.Linc t s x (q.scalar k)).IsSymm := by
      exact pad_isSymm (AndersonAC.S45.survivors x)
        (AndersonAC.S45.laplacian (AndersonAC.S45.Ledge t s x (q.scalar k))) hlapSymm
    have hstepSymm : (q.stepL t r k).IsSymm := by
      simp only [AndersonAC.S45.Sequence.stepL, hp]
      apply matrix_mask_isSymm
      simpa [AndersonAC.S45.restrict] using hincSymm.submatrix Subtype.val
    have hlapRow :
        AndersonAC.S45.laplacian (AndersonAC.S45.Ledge t s x (q.scalar k)) *ᵥ
          (fun _ => (1 : ℝ)) = 0 :=
      laplacian_mulVec_one _
    have hincRow : (AndersonAC.S45.Linc t s x (q.scalar k)) *ᵥ
        (fun _ => (1 : ℝ)) = 0 := by
      exact pad_mulVec_one (AndersonAC.S45.survivors x)
        (AndersonAC.S45.laplacian (AndersonAC.S45.Ledge t s x (q.scalar k))) hlapRow
    have hsupport : ∀ i ∈ (q.state (k + 1)).live, ∀ j ∉ (q.state (k + 1)).live,
        AndersonAC.S45.Linc t s x (q.scalar k) i j = 0 := by
      intro i hi j hj
      have hiErase : i ∈ (q.state k).live.erase x := by
        rw [← hnext]
        exact hi
      rcases Finset.mem_erase.mp hiErase with ⟨hix, hiLive⟩
      have hiSurv : i ∈ AndersonAC.S45.survivors x := by
        simp [AndersonAC.S45.survivors, hix]
      by_cases hjx : j = x
      · subst j
        simp [AndersonAC.S45.Linc, AndersonAC.S45.pad,
          AndersonAC.S45.survivors, hix]
      · have hjSurv : j ∈ AndersonAC.S45.survivors x := by
          simp [AndersonAC.S45.survivors, hjx]
        have hjLive : j ∉ (q.state k).live := by
          intro hjLive
          apply hj
          rw [hnext]
          exact Finset.mem_erase.mpr ⟨hjx, hjLive⟩
        have hledgeZero :
            AndersonAC.S45.Ledge t s x (q.scalar k)
              ⟨i, hiSurv⟩ ⟨j, hjSurv⟩ = 0 := by
          apply Ledge_zero_right t s x (q.scalar k) ⟨i, hiSurv⟩ ⟨j, hjSurv⟩
          intro z
          exact ambient_h_zero_right a r t z hjLive
        have hsubij :
            (⟨i, hiSurv⟩ : AndersonAC.S45.survivors x) ≠ ⟨j, hjSurv⟩ := by
          intro heq
          apply hj
          rw [hnext]
          have : i = j := congrArg Subtype.val heq
          subst j
          exact Finset.mem_erase.mpr ⟨hix, hiLive⟩
        simp [AndersonAC.S45.Linc, AndersonAC.S45.pad, hiSurv, hjSurv,
          AndersonAC.S45.laplacian, hsubij, hledgeZero]
    have hstepRow : (q.stepL t r k) *ᵥ (fun _ => (1 : ℝ)) = 0 := by
      simp only [AndersonAC.S45.Sequence.stepL, hp]
      exact matrix_mask_mulVec_one_of_support (q.state (k + 1)).live
        (AndersonAC.S45.Linc t s x (q.scalar k)) hincRow hsupport
    exact ⟨hstepSymm, hstepRow⟩

end AndersonAC.AgentS45
