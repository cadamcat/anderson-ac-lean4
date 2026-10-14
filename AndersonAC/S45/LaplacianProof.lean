import AndersonAC.S45.Definitions
import AndersonAC.S45.GammaProof
import AndersonAC.S45.PrestateProof

open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators

noncomputable section

namespace AndersonAC.AgentS45

open AndersonAC.S45

lemma laplacian_symmetric {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : RMat ι) (hc : c.IsSymm) : (laplacian c).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  by_cases hij : i = j
  · subst j
    rfl
  · simp [laplacian, hij, Ne.symm hij, hc.apply]

private lemma laplacian_row_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : RMat ι) (i : ι) : ∑ j, laplacian c i j = 0 := by
  classical
  let a := ∑ k, if k = i then 0 else c i k
  have hdiag : (∑ j, if i = j then a else 0) = a := by simp [a]
  have hoff : (∑ j, if i = j then 0 else c i j) = a := by
    simp [a, eq_comm]
  have hsplit : (∑ j, if i = j then a else -c i j) =
      (∑ j, if i = j then a else 0) - (∑ j, if i = j then 0 else c i j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i = j <;> simp [hij]
  change (∑ j, if i = j then a else -c i j) = 0
  rw [hsplit, hdiag, hoff]
  ring

lemma laplacian_mulVec_eq_sum_diff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : RMat ι) (f : ι → ℝ) (i : ι) :
    (laplacian c *ᵥ f) i = ∑ j, (if i = j then 0 else c i j * (f i - f j)) := by
  classical
  have hrow := laplacian_row_sum c i
  have hrewrite :
      ∑ j, laplacian c i j * (f j - f i) = ∑ j, laplacian c i j * f j := by
    calc
      ∑ j, laplacian c i j * (f j - f i) =
          ∑ j, (laplacian c i j * f j - laplacian c i j * f i) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = (∑ j, laplacian c i j * f j) - ∑ j, laplacian c i j * f i :=
        by rw [Finset.sum_sub_distrib]
      _ = (∑ j, laplacian c i j * f j) -
          (∑ j, laplacian c i j) * f i := by rw [← Finset.sum_mul]
      _ = ∑ j, laplacian c i j * f j := by rw [hrow]; ring
  calc
    (laplacian c *ᵥ f) i = ∑ j, laplacian c i j * f j := by
      simp [Matrix.mulVec_apply_eq_sum]
    _ = ∑ j, laplacian c i j * (f j - f i) := hrewrite.symm
    _ = ∑ j, (if i = j then 0 else c i j * (f i - f j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hij : i = j
      · subst j
        simp
      · simp [laplacian, hij]
        ring

lemma qform_laplacian_eq_half_sum_diff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : RMat ι) (hc : c.IsSymm) (f : ι → ℝ) :
    qform (laplacian c) f =
      (1 / 2) * ∑ i, ∑ j, c i j * (f i - f j) ^ 2 := by
  classical
  have hrowForm : qform (laplacian c) f =
      ∑ i, ∑ j, f i * c i j * (f i - f j) := by
    unfold qform
    apply Finset.sum_congr rfl
    intro i hi
    rw [laplacian_mulVec_eq_sum_diff, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
      ring
  have hswap : (∑ i, ∑ j, f j * c i j * (f i - f j)) =
      -(∑ i, ∑ j, f i * c i j * (f i - f j)) := by
    calc
      (∑ i, ∑ j, f j * c i j * (f i - f j)) =
          ∑ j, ∑ i, f j * c i j * (f i - f j) := by rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, f i * c j i * (f j - f i) := by
        rfl
      _ = ∑ i, ∑ j, -(f i * c i j * (f i - f j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hc.apply j i]
        ring
      _ = -(∑ i, ∑ j, f i * c i j * (f i - f j)) := by simp
  have henergy :
      ∑ i, ∑ j, c i j * (f i - f j) ^ 2 =
        2 * ∑ i, ∑ j, f i * c i j * (f i - f j) := by
    calc
      ∑ i, ∑ j, c i j * (f i - f j) ^ 2 =
          ∑ i, ∑ j,
            (f i * c i j * (f i - f j) - f j * c i j * (f i - f j)) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              ring
      _ = (∑ i, ∑ j, f i * c i j * (f i - f j)) -
          ∑ i, ∑ j, f j * c i j * (f i - f j) := by
            simp only [Finset.sum_sub_distrib]
      _ = (∑ i, ∑ j, f i * c i j * (f i - f j)) -
          -(∑ i, ∑ j, f i * c i j * (f i - f j)) := by rw [hswap]
      _ = 2 * ∑ i, ∑ j, f i * c i j * (f i - f j) := by ring
  rw [hrowForm]
  have hhalf :
      ∑ i, ∑ j, f i * c i j * (f i - f j) =
        (1 / 2) * ∑ i, ∑ j, c i j * (f i - f j) ^ 2 := by
    nlinarith [henergy]
  exact hhalf

lemma neutral_of_symmetric_rowSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : RMat ι) (hA : A.IsSymm) (hrow : ∀ i, ∑ j, A i j = 0) (f : ι → ℝ) :
    neutral (A *ᵥ f) := by
  classical
  unfold neutral
  simp only [Matrix.mulVec, dotProduct]
  calc
    (∑ i, ∑ j, A i j * f j) =
        ∑ j, (∑ i, A i j) * f j := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_mul]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hcol : ∑ i, A i j = 0 := by
        calc
          (∑ i, A i j) = ∑ i, A j i := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hA.apply j i
          _ = 0 := hrow j
      simp [hcol]

lemma neutral_laplacian_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : RMat ι) (hc : c.IsSymm) (f : ι → ℝ) :
    neutral (laplacian c *ᵥ f) := by
  exact neutral_of_symmetric_rowSum (laplacian c) (laplacian_symmetric c hc)
    (laplacian_row_sum c) f

lemma pad_symmetric {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (A : RMat S) (hA : A.IsSymm) : (pad S A).IsSymm := by
  classical
  apply Matrix.IsSymm.ext
  intro i j
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    simp [pad, hi, hj, hA.apply]

lemma sum_dite_mem_eq_subtype {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) [instS : Fintype S] (f : ∀ i, i ∈ S → ℝ) :
    (∑ i, if h : i ∈ S then f i h else 0) = ∑ i : S, f i i.property := by
  classical
  let g : ι → ℝ := fun i => if h : i ∈ S then f i h else 0
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun i : ι => i ∈ S) g
  have hinside : (∑ i : S, g i.val) = ∑ i : S, f i i.property := by
    apply Fintype.sum_congr
    intro i
    simp [g]
  have houtside : (∑ i : {i : ι // i ∉ S}, g i.val) = 0 := by
    apply Fintype.sum_eq_zero
    intro i
    simp [g, i.property]
  have hbridge := @Fintype.sum_equiv {i : ι // i ∈ S} S ℝ
    (Subtype.fintype (fun i : ι => i ∈ S)) instS inferInstance
    (Equiv.refl S) (fun i => g i.val) (fun i => g i.val) (by intro i; rfl)
  have hsplit' := hsplit
  simp only [houtside, add_zero] at hsplit'
  change (∑ i, g i) = _
  exact hsplit'.symm.trans (hbridge.trans hinside)

lemma pad_row_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (A : RMat S) [Fintype S]
    (hrow : ∀ i : S, ∑ j, A i j = 0) :
    ∀ i, ∑ j, pad S A i j = 0 := by
  classical
  intro i
  by_cases hi : i ∈ S
  · simp only [pad, dif_pos hi]
    rw [sum_dite_mem_eq_subtype S (fun j hj => A ⟨i, hi⟩ ⟨j, hj⟩)]
    exact hrow ⟨i, hi⟩
  · simp [pad, hi]

lemma Ledge_symmetric {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (x : P) (ξ : ℝ) (hsym : s.g.IsSymm) :
    (Ledge t s x ξ).IsSymm := by
  classical
  have hh : (s.h t).IsSymm := by
    unfold State.h
    exact hsym.smul _
  apply Matrix.IsSymm.ext
  intro i j
  have hji : s.h t j.val i.val = s.h t i.val j.val := hh.apply i.val j.val
  have hjx : s.h t j.val x = s.h t x j.val := hh.apply x j.val
  have hxi : s.h t x i.val = s.h t i.val x := hh.apply i.val x
  have hFj : s.F t j.val x = s.F t x j.val := by
    simp [State.F, entryAbsSquare, hjx]
  have hFi : s.F t x i.val = s.F t i.val x := by
    simp [State.F, entryAbsSquare, hxi]
  have hprod : gamma t s x ξ * star (s.h t i.val j.val) *
      s.h t x j.val * s.h t i.val x =
      gamma t s x ξ * star (s.h t i.val j.val) *
        s.h t i.val x * s.h t x j.val := by ring
  have hlinear := congrArg Complex.re hprod
  unfold Ledge
  rw [hji, hjx, hxi, hFj, hFi, hlinear]
  ring

lemma Linc_symmetric {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (x : P) (ξ : ℝ) (hsym : s.g.IsSymm) :
    (Linc t s x ξ).IsSymm := by
  exact pad_symmetric (survivors x) (laplacian (Ledge t s x ξ))
    (laplacian_symmetric (Ledge t s x ξ) (Ledge_symmetric t s x ξ hsym))

private lemma Linc_row_sum {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (x : P) (ξ : ℝ) :
    ∀ i, ∑ j, Linc t s x ξ i j = 0 := by
  exact pad_row_sum (survivors x) (laplacian (Ledge t s x ξ))
    (fun i => laplacian_row_sum (Ledge t s x ξ) i)

lemma Linc_neutral {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (x : P) (ξ : ℝ) (hsym : s.g.IsSymm) (f : P → ℝ) :
    neutral (Linc t s x ξ *ᵥ f) := by
  exact neutral_of_symmetric_rowSum (Linc t s x ξ)
    (Linc_symmetric t s x ξ hsym) (Linc_row_sum t s x ξ) f

lemma Linc_mulVec_eq_survivor_mulVec {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (x : P) (ξ : ℝ) (i : P) (f : P → ℝ)
    (hi : i ∈ survivors x) :
    (Linc t s x ξ *ᵥ f) i =
      (laplacian (Ledge t s x ξ) *ᵥ (fun j : survivors x => f j.val)) ⟨i, hi⟩ := by
  classical
  unfold Linc pad
  change (∑ j, (if hI : i ∈ survivors x then
      if hj : j ∈ survivors x then
        laplacian (Ledge t s x ξ) ⟨i, hI⟩ ⟨j, hj⟩ else 0 else 0) * f j) = _
  simp only [dif_pos hi, zero_mul, dite_mul]
  rw [sum_dite_mem_eq_subtype (survivors x)
    (fun j hj => laplacian (Ledge t s x ξ) ⟨i, hi⟩ ⟨j, hj⟩ * f j)]
  simp [Matrix.mulVec_apply_eq_sum]

lemma Linc_mulVec_entry_eq_edges {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (x : P) (ξ : ℝ) (i : P) (f : P → ℝ)
    (hi : i ∈ survivors x) :
    (Linc t s x ξ *ᵥ f) i =
      ∑ j : survivors x,
        if (⟨i, hi⟩ : survivors x) = j then 0 else
          Ledge t s x ξ ⟨i, hi⟩ j * (f i - f j.val) := by
  rw [Linc_mulVec_eq_survivor_mulVec t s x ξ i f hi]
  simpa using
    (laplacian_mulVec_eq_sum_diff (Ledge t s x ξ)
      (fun j : survivors x => f j.val) ⟨i, hi⟩)

lemma Linc_mulVec_eq_zero_of_not_mem {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (x : P) (ξ : ℝ) (i : P) (f : P → ℝ)
    (hi : i ∉ survivors x) : (Linc t s x ξ *ᵥ f) i = 0 := by
  have hrow : ∀ j, Linc t s x ξ i j = 0 := by
    intro j
    simp [Linc, pad, hi]
  simp [Matrix.mulVec_apply_eq_sum, hrow]

lemma complex_weighted_conj (z : ℂ) (p : ℝ) :
    z * ((p : ℂ) * star z) = ((p * ‖z‖ ^ 2 : ℝ) : ℂ) := by
  calc
    z * ((p : ℂ) * star z) = (p : ℂ) * (z * star z) := by ring
    _ = ((p * ‖z‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.star_def, RCLike.mul_conj]
      push_cast
      rfl

lemma complex_weighted_conj_left (z : ℂ) (p : ℝ) :
    z * (p : ℂ) * star z = ((p * ‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_assoc, complex_weighted_conj]

lemma complex_weighted_conj_left_end (z : ℂ) (p : ℝ) :
    z * (p : ℂ) * (starRingEnd ℂ) z = ((p * ‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [starRingEnd_apply]
  exact complex_weighted_conj_left z p

lemma ward_row_sum_F {P : Type*} [Fintype P] [DecidableEq P]
    (s : State P) (t : ℝ) (hw : s.ward t) (i : P) :
    ∑ j, s.p j * s.F t i j = s.q i := by
  classical
  change s.h t * diagonal (fun j => (s.p j : ℂ)) * (s.h t)ᴴ = matrixIm s.g at hw
  have hentry := congrArg (fun A : CMat P => A i i) hw
  have hExpanded :
      (∑ j, s.h t i j * (s.p j : ℂ) * (starRingEnd ℂ) (s.h t i j)) =
        ((s.g i i).im : ℂ) := by
    simpa [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
      matrixIm] using hentry
  have hcast : ((∑ j, s.p j * s.F t i j : ℝ) : ℂ) = (s.q i : ℂ) := by
    simpa [State.F, entryAbsSquare, State.q, complex_weighted_conj_left_end] using hExpanded
  apply Complex.ofReal_injective
  exact hcast

lemma F_row_sum_le_Cq {P : Type*} [Fintype P] [DecidableEq P]
    (t C : ℝ) (Λplus Wstar : Form P) (s : State P)
    (hC : 1 ≤ C) (hp : Prestate t C Λplus Wstar s) :
    ∀ i, ∑ j, s.F t i j ≤ C * s.q i := by
  classical
  have hCpos : 0 < C := by linarith
  have hcinv : C * (1 / C) = 1 := by field_simp [ne_of_gt hCpos]
  intro i
  have hFnon : ∀ j, 0 ≤ s.F t i j := by
    intro j
    simp [State.F, entryAbsSquare]
  calc
    (∑ j, s.F t i j) = ∑ j, C * ((1 / C) * s.F t i j) := by
      apply Finset.sum_congr rfl
      intro j hj
      calc
        s.F t i j = (C * (1 / C)) * s.F t i j := by rw [hcinv]; simp
        _ = C * ((1 / C) * s.F t i j) := by ring
    _ ≤ ∑ j, C * (s.p j * s.F t i j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hp.broad j).2.1 (hFnon j)) hCpos.le
    _ = C * (∑ j, s.p j * s.F t i j) := by rw [← Finset.mul_sum]
    _ = C * s.q i := by rw [ward_row_sum_F s t hp.ward i]

lemma F_symmetric_of_prestate {P : Type*} [Fintype P] [DecidableEq P]
    (t C : ℝ) (Λplus Wstar : Form P) (s : State P)
    (hp : Prestate t C Λplus Wstar s) : (s.F t).IsSymm := by
  have hh : (s.h t).IsSymm := by
    unfold State.h
    exact hp.symmetric.smul _
  apply Matrix.IsSymm.ext
  intro i j
  simp [State.F, entryAbsSquare, hh.apply i j]

lemma D_eq_laplacian_pF {P : Type*} [Fintype P] [DecidableEq P]
    (t C : ℝ) (Λplus Wstar : Form P) (s : State P)
    (hp : Prestate t C Λplus Wstar s) :
    s.D t = laplacian (fun i j => s.p i * s.p j * s.F t i j) := by
  classical
  have hDentry : ∀ i j, s.D t i j =
      (if i = j then s.p i * s.q i else 0) - s.p i * s.F t i j * s.p j := by
    intro i j
    simp [State.D, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.mul_apply]
  have hfull : ∀ i, (∑ j, s.p i * s.p j * s.F t i j) = s.p i * s.q i := by
    intro i
    calc
      (∑ j, s.p i * s.p j * s.F t i j) =
          s.p i * (∑ j, s.p j * s.F t i j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = s.p i * s.q i := by rw [ward_row_sum_F s t hp.ward i]
  have hdiag : ∀ i,
      (∑ j, if j = i then 0 else s.p i * s.p j * s.F t i j) =
        s.p i * s.q i - s.p i * s.F t i i * s.p i := by
    intro i
    have hsplit : (∑ j, s.p i * s.p j * s.F t i j) =
        (∑ j, if j = i then 0 else s.p i * s.p j * s.F t i j) +
          s.p i * s.p i * s.F t i i := by
      calc
        (∑ j, s.p i * s.p j * s.F t i j) =
            ∑ j, ((if j = i then 0 else s.p i * s.p j * s.F t i j) +
              (if j = i then s.p i * s.p j * s.F t i j else 0)) := by
                apply Finset.sum_congr rfl
                intro j hj
                by_cases hji : j = i <;> simp [hji]
        _ = (∑ j, if j = i then 0 else s.p i * s.p j * s.F t i j) +
            ∑ j, if j = i then s.p i * s.p j * s.F t i j else 0 :=
              Finset.sum_add_distrib
        _ = (∑ j, if j = i then 0 else s.p i * s.p j * s.F t i j) +
            s.p i * s.p i * s.F t i i := by simp
    rw [hfull i] at hsplit
    nlinarith [hsplit]
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [hDentry i i, laplacian, hdiag i]
  · rw [hDentry]
    simp [laplacian, hij]
    ring

lemma qform_D_eq_half_weighted_energy {P : Type*} [Fintype P] [DecidableEq P]
    (t C : ℝ) (Λplus Wstar : Form P) (s : State P)
    (hp : Prestate t C Λplus Wstar s) (f : P → ℝ) :
    qform (s.D t) f =
      (1 / 2) * ∑ i, ∑ j,
        s.p i * s.p j * s.F t i j * (f i - f j) ^ 2 := by
  rw [D_eq_laplacian_pF t C Λplus Wstar s hp]
  apply qform_laplacian_eq_half_sum_diff
  have hFsym := F_symmetric_of_prestate t C Λplus Wstar s hp
  apply Matrix.IsSymm.ext
  intro i j
  rw [hFsym.apply i j]
  ring

lemma F_energy_le_D_of_prestate {P : Type*} [Fintype P] [DecidableEq P]
    (t C : ℝ) (Λplus Wstar : Form P) (s : State P)
    (hC : 1 ≤ C) (hp : Prestate t C Λplus Wstar s) (f : P → ℝ) :
    (∑ i, ∑ j, s.F t i j * (f i - f j) ^ 2) ≤
      2 * C ^ 2 * qform (s.D t) f := by
  classical
  have hCpos : 0 < C := by linarith
  have hterm : ∀ i j, 0 ≤ s.F t i j * (f i - f j) ^ 2 := by
    intro i j
    exact mul_nonneg (by simp [State.F, entryAbsSquare]) (sq_nonneg _)
  have hprod : ∀ i j, 1 / C ^ 2 ≤ s.p i * s.p j := by
    intro i j
    have hpLoweri := (hp.broad i).2.1
    have hpLowerj := (hp.broad j).2.1
    have hmul := mul_le_mul hpLoweri hpLowerj (by positivity) (by
      have hpos : 0 < 1 / C := by positivity
      linarith)
    calc
      1 / C ^ 2 = (1 / C) * (1 / C) := by field_simp [ne_of_gt hCpos]
      _ ≤ s.p i * s.p j := hmul
  have hpoint : ∀ i j,
      s.F t i j * (f i - f j) ^ 2 ≤
        C ^ 2 * (s.p i * s.p j * s.F t i j * (f i - f j) ^ 2) := by
    intro i j
    have hmul := mul_le_mul_of_nonneg_right (hprod i j) (hterm i j)
    have hmul' := mul_le_mul_of_nonneg_left hmul (sq_nonneg C)
    have hid : C ^ 2 * ((1 / C ^ 2) *
        (s.F t i j * (f i - f j) ^ 2)) = s.F t i j * (f i - f j) ^ 2 := by
      field_simp [ne_of_gt hCpos]
    calc
      s.F t i j * (f i - f j) ^ 2 =
          C ^ 2 * ((1 / C ^ 2) * (s.F t i j * (f i - f j) ^ 2)) := hid.symm
      _ ≤ C ^ 2 * (s.p i * s.p j * (s.F t i j * (f i - f j) ^ 2)) := hmul'
      _ = C ^ 2 * (s.p i * s.p j * s.F t i j * (f i - f j) ^ 2) := by ring
  have hsum : (∑ i, ∑ j, s.F t i j * (f i - f j) ^ 2) ≤
      C ^ 2 * (∑ i, ∑ j,
        s.p i * s.p j * s.F t i j * (f i - f j) ^ 2) := by
    calc
      (∑ i, ∑ j, s.F t i j * (f i - f j) ^ 2) ≤
          ∑ i, ∑ j, C ^ 2 *
            (s.p i * s.p j * s.F t i j * (f i - f j) ^ 2) := by
              apply Finset.sum_le_sum
              intro i hi
              apply Finset.sum_le_sum
              intro j hj
              exact hpoint i j
      _ = C ^ 2 * (∑ i, ∑ j,
            s.p i * s.p j * s.F t i j * (f i - f j) ^ 2) := by
              simp only [← Finset.mul_sum]
  have hweighted :
      (∑ i, ∑ j, s.p i * s.p j * s.F t i j * (f i - f j) ^ 2) =
        2 * qform (s.D t) f := by
    rw [qform_D_eq_half_weighted_energy t C Λplus Wstar s hp f]
    ring
  calc
    (∑ i, ∑ j, s.F t i j * (f i - f j) ^ 2) ≤
        C ^ 2 * (∑ i, ∑ j,
          s.p i * s.p j * s.F t i j * (f i - f j) ^ 2) := hsum
    _ = 2 * C ^ 2 * qform (s.D t) f := by rw [hweighted]; ring

lemma quadratic_edge_stack_le_D {P : Type*} [Fintype P] [DecidableEq P]
    (t C R : ℝ) (Λplus Wstar : Form P) (s : State P) (S : Finset P)
    (hC : 1 ≤ C) (hR : 0 ≤ R)
    (hrow : ∀ i, (∑ j, s.F t i j) ≤ R)
    (hp : Prestate t C Λplus Wstar s) (f : P → ℝ) :
    (∑ x ∈ S, ∑ i, ∑ j,
      s.p i * s.p j * s.F t i x * s.F t x j * (f i - f j) ^ 2) ≤
      8 * C ^ 4 * R * qform (s.D t) f := by
  classical
  let ES : ℝ := ∑ x ∈ S, ∑ i, s.F t i x * (f i - f x) ^ 2
  let A : ℝ := ∑ x ∈ S, ∑ i, ∑ j,
    s.F t i x * s.F t x j * (f i - f x) ^ 2
  let B : ℝ := ∑ x ∈ S, ∑ i, ∑ j,
    s.F t i x * s.F t x j * (f x - f j) ^ 2
  have hCpos : 0 < C := by linarith
  have hFsym := F_symmetric_of_prestate t C Λplus Wstar s hp
  have hFnon : ∀ i j, 0 ≤ s.F t i j := by
    intro i j
    simp [State.F, entryAbsSquare]
  have hFcol : ∀ x, (∑ i, s.F t i x) ≤ R := by
    intro x
    calc
      (∑ i, s.F t i x) = ∑ i, s.F t x i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hFsym.apply x i
      _ ≤ R := hrow x
  have hESnon : 0 ≤ ES := by
    dsimp [ES]
    apply Finset.sum_nonneg
    intro x hx
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hFnon i x) (sq_nonneg _)
  have hESle : ES ≤ ∑ i, ∑ j, s.F t i j * (f i - f j) ^ 2 := by
    dsimp [ES]
    calc
      (∑ x ∈ S, ∑ i, s.F t i x * (f i - f x) ^ 2) ≤
          ∑ x, ∑ i, s.F t i x * (f i - f x) ^ 2 := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
            intro x hxS hx
            apply Finset.sum_nonneg
            intro i hi
            exact mul_nonneg (hFnon i x) (sq_nonneg _)
      _ = ∑ i, ∑ j, s.F t i j * (f i - f j) ^ 2 := by rw [Finset.sum_comm]
  have hA : A ≤ R * ES := by
    dsimp [A, ES]
    calc
      (∑ x ∈ S, ∑ i, ∑ j,
          s.F t i x * s.F t x j * (f i - f x) ^ 2) =
          ∑ x ∈ S, ∑ i,
            (s.F t i x * (f i - f x) ^ 2) * (∑ j, s.F t x j) := by
              apply Finset.sum_congr rfl
              intro x hx
              apply Finset.sum_congr rfl
              intro i hi
              calc
                (∑ j, s.F t i x * s.F t x j * (f i - f x) ^ 2) =
                    ∑ j, (s.F t i x * (f i - f x) ^ 2) * s.F t x j := by
                      apply Finset.sum_congr rfl
                      intro j hj
                      ring
                _ = (s.F t i x * (f i - f x) ^ 2) * (∑ j, s.F t x j) := by
                      rw [← Finset.mul_sum]
      _ ≤ ∑ x ∈ S, ∑ i, (s.F t i x * (f i - f x) ^ 2) * R := by
            apply Finset.sum_le_sum
            intro x hx
            apply Finset.sum_le_sum
            intro i hi
            exact mul_le_mul_of_nonneg_left (hrow x)
              (mul_nonneg (hFnon i x) (sq_nonneg _))
      _ = R * (∑ x ∈ S, ∑ i, s.F t i x * (f i - f x) ^ 2) := by
            calc
              (∑ x ∈ S, ∑ i, (s.F t i x * (f i - f x) ^ 2) * R) =
                  (∑ x ∈ S, ∑ i, s.F t i x * (f i - f x) ^ 2) * R := by
                    calc
                      (∑ x ∈ S, ∑ i, (s.F t i x * (f i - f x) ^ 2) * R) =
                          ∑ x ∈ S, (∑ i, s.F t i x * (f i - f x) ^ 2) * R := by
                            apply Finset.sum_congr rfl
                            intro x hx
                            rw [Finset.sum_mul]
                      _ = (∑ x ∈ S, ∑ i, s.F t i x * (f i - f x) ^ 2) * R := by
                            rw [Finset.sum_mul]
              _ = R * (∑ x ∈ S, ∑ i, s.F t i x * (f i - f x) ^ 2) := by ring
  have hB : B ≤ R * ES := by
    dsimp [B, ES]
    calc
      (∑ x ∈ S, ∑ i, ∑ j,
          s.F t i x * s.F t x j * (f x - f j) ^ 2) =
          ∑ x ∈ S, ∑ j,
            (s.F t x j * (f x - f j) ^ 2) * (∑ i, s.F t i x) := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro j hj
              calc
                (∑ i, s.F t i x * s.F t x j * (f x - f j) ^ 2) =
                    ∑ i, (s.F t x j * (f x - f j) ^ 2) * s.F t i x := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      ring
                _ = (s.F t x j * (f x - f j) ^ 2) * (∑ i, s.F t i x) := by
                      rw [← Finset.mul_sum]
      _ ≤ ∑ x ∈ S, ∑ j, (s.F t x j * (f x - f j) ^ 2) * R := by
            apply Finset.sum_le_sum
            intro x hx
            apply Finset.sum_le_sum
            intro j hj
            exact mul_le_mul_of_nonneg_left (hFcol x)
              (mul_nonneg (hFnon x j) (sq_nonneg _))
      _ = R * (∑ x ∈ S, ∑ j, s.F t j x * (f j - f x) ^ 2) := by
            calc
              (∑ x ∈ S, ∑ j, (s.F t x j * (f x - f j) ^ 2) * R) =
                  (∑ x ∈ S, ∑ j, s.F t x j * (f x - f j) ^ 2) * R := by
                    calc
                      (∑ x ∈ S, ∑ j, (s.F t x j * (f x - f j) ^ 2) * R) =
                          ∑ x ∈ S, (∑ j, s.F t x j * (f x - f j) ^ 2) * R := by
                            apply Finset.sum_congr rfl
                            intro x hx
                            rw [Finset.sum_mul]
                      _ = (∑ x ∈ S, ∑ j, s.F t x j * (f x - f j) ^ 2) * R := by
                            rw [Finset.sum_mul]
              _ = R * (∑ x ∈ S, ∑ j, s.F t j x * (f j - f x) ^ 2) := by
                    rw [mul_comm]
                    congr 1
                    apply Finset.sum_congr rfl
                    intro x hx
                    apply Finset.sum_congr rfl
                    intro j hj
                    rw [hFsym.apply x j]
                    ring
      _ = R * (∑ x ∈ S, ∑ i, s.F t i x * (f i - f x) ^ 2) := by rfl
  have hTsplit :
      (∑ x ∈ S, ∑ i, ∑ j,
        s.F t i x * s.F t x j * (f i - f j) ^ 2) ≤ 2 * A + 2 * B := by
    calc
      (∑ x ∈ S, ∑ i, ∑ j,
        s.F t i x * s.F t x j * (f i - f j) ^ 2) ≤
          ∑ x ∈ S, ∑ i, ∑ j,
            (2 * (s.F t i x * s.F t x j * (f i - f x) ^ 2) +
              2 * (s.F t i x * s.F t x j * (f x - f j) ^ 2)) := by
                apply Finset.sum_le_sum
                intro x hx
                apply Finset.sum_le_sum
                intro i hi
                apply Finset.sum_le_sum
                intro j hj
                have hsplit := sq_nonneg ((f i - f x) - (f x - f j))
                have hcoef : 0 ≤ s.F t i x * s.F t x j :=
                  mul_nonneg (hFnon i x) (hFnon x j)
                have hsq := mul_le_mul_of_nonneg_left
                  (show (f i - f j) ^ 2 ≤
                    2 * (f i - f x) ^ 2 + 2 * (f x - f j) ^ 2 by nlinarith [hsplit]) hcoef
                nlinarith [hsq]
      _ = 2 * A + 2 * B := by
        simp [A, B, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hpNon : ∀ i, 0 ≤ s.p i := by
    intro i
    have hinv : 0 < 1 / C := by positivity
    linarith [(hp.broad i).2.1]
  have hpProd : ∀ i j, s.p i * s.p j ≤ C ^ 2 := by
    intro i j
    calc
      s.p i * s.p j ≤ C * s.p j :=
        mul_le_mul_of_nonneg_right (hp.broad i).2.2 (hpNon j)
      _ ≤ C * C := mul_le_mul_of_nonneg_left (hp.broad j).2.2 hCpos.le
      _ = C ^ 2 := by ring
  have hTweighted :
      (∑ x ∈ S, ∑ i, ∑ j,
        s.p i * s.p j * s.F t i x * s.F t x j * (f i - f j) ^ 2) ≤
        C ^ 2 * (∑ x ∈ S, ∑ i, ∑ j,
          s.F t i x * s.F t x j * (f i - f j) ^ 2) := by
    calc
      (∑ x ∈ S, ∑ i, ∑ j,
        s.p i * s.p j * s.F t i x * s.F t x j * (f i - f j) ^ 2) ≤
          ∑ x ∈ S, ∑ i, ∑ j,
            C ^ 2 * (s.F t i x * s.F t x j * (f i - f j) ^ 2) := by
              apply Finset.sum_le_sum
              intro x hx
              apply Finset.sum_le_sum
              intro i hi
              apply Finset.sum_le_sum
              intro j hj
              have hnon : 0 ≤ s.F t i x * s.F t x j * (f i - f j) ^ 2 :=
                mul_nonneg (mul_nonneg (hFnon i x) (hFnon x j)) (sq_nonneg _)
              have hmul := mul_le_mul_of_nonneg_right (hpProd i j) hnon
              nlinarith [hmul]
      _ = C ^ 2 * (∑ x ∈ S, ∑ i, ∑ j,
          s.F t i x * s.F t x j * (f i - f j) ^ 2) := by
            simp [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hESenergy := F_energy_le_D_of_prestate t C Λplus Wstar s hC hp f
  have hRnon : 0 ≤ 8 * C ^ 4 * R := by positivity
  calc
    (∑ x ∈ S, ∑ i, ∑ j,
      s.p i * s.p j * s.F t i x * s.F t x j * (f i - f j) ^ 2) ≤
        C ^ 2 * (2 * A + 2 * B) := by
          calc
            _ ≤ C ^ 2 *
                (∑ x ∈ S, ∑ i, ∑ j,
                  s.F t i x * s.F t x j * (f i - f j) ^ 2) := hTweighted
            _ ≤ C ^ 2 * (2 * A + 2 * B) := by
              apply mul_le_mul_of_nonneg_left hTsplit (sq_nonneg C)
    _ ≤ C ^ 2 * (4 * R * ES) := by
          apply mul_le_mul_of_nonneg_left ?_ (sq_nonneg C)
          nlinarith [hA, hB]
    _ = (4 * C ^ 2 * R) * ES := by ring
    _ ≤ (4 * C ^ 2 * R) * (2 * C ^ 2 * qform (s.D t) f) := by
          apply mul_le_mul_of_nonneg_left ?_
            (by positivity : 0 ≤ 4 * C ^ 2 * R)
          exact hESle.trans hESenergy
    _ = 8 * C ^ 4 * R * qform (s.D t) f := by ring

lemma rho_edge_form_bound_of_prestate {P : Type*} [Fintype P] [DecidableEq P]
    (t C R K : ℝ) (Λplus Wstar : Form P) (s : State P) (S : Finset P)
    (hC : 1 ≤ C) (hR : 0 ≤ R) (hK : 0 ≤ K)
    (hrow : ∀ i, (∑ j, s.F t i j) ≤ R)
    (hp : Prestate t C Λplus Wstar s) (f : P → ℝ) (ρ : P → ℝ)
    (hρ : ∀ x ∈ S, |ρ x| ≤ K * power t beta) :
    |(1 / 2) * (∑ x ∈ S, ∑ i, ∑ j,
      s.p i * s.p j * s.F t i x * s.F t x j * ρ x * (f i - f j) ^ 2)| ≤
      4 * C ^ 4 * R * K * power t beta * qform (s.D t) f := by
  classical
  let edge (x i j : P) : ℝ :=
    s.p i * s.p j * s.F t i x * s.F t x j * (f i - f j) ^ 2
  let a : ℝ := K * power t beta
  have ha : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg hK (Real.rpow_nonneg hp.scale.1.le _)
  have hpNon : ∀ i, 0 ≤ s.p i := by
    intro i
    have hinv : 0 < 1 / C := by positivity
    linarith [(hp.broad i).2.1]
  have hedgeNon : ∀ x i j, 0 ≤ edge x i j := by
    intro x i j
    dsimp [edge]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hpNon i) (hpNon j))
      (by simp [State.F, entryAbsSquare])) (by simp [State.F, entryAbsSquare])) (sq_nonneg _)
  have hAbsSum :
      |∑ x ∈ S, ∑ i, ∑ j, edge x i j * ρ x| ≤
        ∑ x ∈ S, ∑ i, ∑ j, |edge x i j * ρ x| := by
    calc
      |∑ x ∈ S, ∑ i, ∑ j, edge x i j * ρ x| ≤
          ∑ x ∈ S, |∑ i, ∑ j, edge x i j * ρ x| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ S, ∑ i, |∑ j, edge x i j * ρ x| := by
            apply Finset.sum_le_sum
            intro x hx
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ S, ∑ i, ∑ j, |edge x i j * ρ x| := by
            apply Finset.sum_le_sum
            intro x hx
            apply Finset.sum_le_sum
            intro i hi
            exact Finset.abs_sum_le_sum_abs _ _
  have hAbsTerm : ∀ x ∈ S, ∀ i j, |edge x i j * ρ x| ≤ a * edge x i j := by
    intro x hx i j
    calc
      |edge x i j * ρ x| = edge x i j * |ρ x| := by
        rw [abs_mul, abs_of_nonneg (hedgeNon x i j)]
      _ ≤ edge x i j * a :=
        mul_le_mul_of_nonneg_left (by simpa [a] using hρ x hx) (hedgeNon x i j)
      _ = a * edge x i j := by ring
  have hsumBound :
      (∑ x ∈ S, ∑ i, ∑ j, |edge x i j * ρ x|) ≤
        a * (∑ x ∈ S, ∑ i, ∑ j, edge x i j) := by
    calc
      (∑ x ∈ S, ∑ i, ∑ j, |edge x i j * ρ x|) ≤
          ∑ x ∈ S, ∑ i, ∑ j, a * edge x i j := by
            apply Finset.sum_le_sum
            intro x hx
            apply Finset.sum_le_sum
            intro i hi
            apply Finset.sum_le_sum
            intro j hj
            exact hAbsTerm x hx i j
      _ = a * (∑ x ∈ S, ∑ i, ∑ j, edge x i j) := by
            simp only [← Finset.mul_sum]
  have hstack := quadratic_edge_stack_le_D t C R Λplus Wstar s S hC hR hrow hp f
  have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hsumRewrite :
      (∑ x ∈ S, ∑ i, ∑ j, edge x i j * ρ x) =
        ∑ x ∈ S, ∑ i, ∑ j,
          s.p i * s.p j * s.F t i x * s.F t x j * ρ x * (f i - f j) ^ 2 := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [edge]
    ring
  rw [← hsumRewrite]
  calc
    |(1 / 2) * (∑ x ∈ S, ∑ i, ∑ j, edge x i j * ρ x)| =
        (1 / 2) * |∑ x ∈ S, ∑ i, ∑ j, edge x i j * ρ x| := by
          rw [abs_mul, abs_of_nonneg hhalf]
    _ ≤ (1 / 2) * (∑ x ∈ S, ∑ i, ∑ j, |edge x i j * ρ x|) :=
          mul_le_mul_of_nonneg_left hAbsSum hhalf
    _ ≤ (1 / 2) * (a * (∑ x ∈ S, ∑ i, ∑ j, edge x i j)) :=
          mul_le_mul_of_nonneg_left hsumBound hhalf
    _ ≤ (1 / 2) * (a * (8 * C ^ 4 * R * qform (s.D t) f)) := by
          apply mul_le_mul_of_nonneg_left ?_ hhalf
          exact mul_le_mul_of_nonneg_left hstack ha
    _ = 4 * C ^ 4 * R * K * power t beta * qform (s.D t) f := by
          dsimp [a, edge]
          ring

lemma rawLag_eq_of_prestate {P : Type*} [Fintype P] [DecidableEq P]
    (t C : ℝ) (Λplus Wstar : Form P) (s : State P)
    (hp : Prestate t C Λplus Wstar s) :
    (1 - s.K t) *ᵥ s.lag t = s.rawLag := by
  have hdet : IsUnit (1 - s.K t).det :=
    (Matrix.isUnit_iff_isUnit_det (1 - s.K t)).mp hp.invertible
  have hmul : (1 - s.K t) * (1 - s.K t)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv (1 - s.K t) hdet
  simp only [State.lag, State.P]
  rw [Matrix.mulVec_mulVec]
  rw [hmul]
  simp

lemma rawLag_small_of_prestate {P : Type*} [Fintype P] [DecidableEq P]
    (t C : ℝ) (Λplus Wstar : Form P) (s : State P)
    (hC : 1 ≤ C) (hsmall : C * power t beta ≤ 1 / 2)
    (hp : Prestate t C Λplus Wstar s) :
    ∀ i, ‖s.rawLag i‖ ≤ 2 * power t beta * (1 + C ^ 2) := by
  classical
  have hCpos : 0 < C := by linarith
  have a_nonneg : 0 ≤ power t beta := (Real.rpow_pos_of_pos hp.scale.1 beta).le
  have hcinv : C * (1 / C) = 1 := by field_simp [ne_of_gt hCpos]
  have hraw := rawLag_eq_of_prestate t C Λplus Wstar s hp
  intro i
  have hcoord : s.rawLag i = s.lag t i - ∑ j, s.K t i j * s.lag t j := by
    have hsub : s.lag t - s.K t *ᵥ s.lag t = s.rawLag := by
      simpa [Matrix.sub_mulVec] using hraw
    have hi := congrFun hsub i
    simpa [Matrix.mulVec_apply_eq_sum] using hi.symm
  have hpLower : ∀ j, 1 / C ≤ s.p j := fun j => (hp.broad j).2.1
  have hpUpper : s.p i ≤ C := (hp.broad i).2.2
  have hqp : s.q i - s.p i = (s.rawLag i).im := by
    simp [State.q, State.p, State.rawLag, Complex.sub_im]
  have hqUpper : s.q i ≤ C + ‖s.rawLag i‖ := by
    have him := Complex.im_le_norm (s.rawLag i)
    linarith
  have hFnon : ∀ j, 0 ≤ s.F t i j := by
    intro j
    simp [State.F, entryAbsSquare]
  have hKnorm : ∀ j, ‖s.K t i j‖ = s.F t i j := by
    intro j
    simp [State.K, State.F, entryAbsSquare, entrywiseSquare,
      AndersonAC.Blueprint.entrywiseSquare, norm_pow]
  have hrow : (∑ j, s.F t i j) ≤ C * s.q i := by
    calc
      (∑ j, s.F t i j) = ∑ j, C * ((1 / C) * s.F t i j) := by
        apply Finset.sum_congr rfl
        intro j hj
        calc
          s.F t i j = (C * (1 / C)) * s.F t i j := by rw [hcinv]; simp
          _ = C * ((1 / C) * s.F t i j) := by ring
      _ ≤ ∑ j, C * (s.p j * s.F t i j) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hpLower j) (hFnon j)) hCpos.le
      _ = C * (∑ j, s.p j * s.F t i j) := by rw [← Finset.mul_sum]
      _ = C * s.q i := by rw [ward_row_sum_F s t hp.ward i]
  have hrowBound : (∑ j, s.F t i j) ≤ C * (C + ‖s.rawLag i‖) := by
    calc
      (∑ j, s.F t i j) ≤ C * s.q i := hrow
      _ ≤ C * (C + ‖s.rawLag i‖) :=
        mul_le_mul_of_nonneg_left hqUpper hCpos.le
  have hrawIneq : ‖s.rawLag i‖ ≤
      power t beta * (1 + C * (C + ‖s.rawLag i‖)) := by
    have hterm : ∀ j, ‖s.K t i j * s.lag t j‖ ≤ s.F t i j * power t beta := by
      intro j
      rw [norm_mul, hKnorm j]
      exact mul_le_mul_of_nonneg_left (hp.lag_cap j) (hFnon j)
    calc
      ‖s.rawLag i‖ = ‖s.lag t i - ∑ j, s.K t i j * s.lag t j‖ := by rw [hcoord]
      _ ≤
          ‖s.lag t i‖ + ‖∑ j, s.K t i j * s.lag t j‖ := norm_sub_le _ _
      _ ≤ power t beta + ∑ j, ‖s.K t i j * s.lag t j‖ :=
        add_le_add (hp.lag_cap i) (norm_sum_le _ _)
      _ ≤ power t beta + ∑ j, s.F t i j * power t beta := by
        apply add_le_add_right
        apply Finset.sum_le_sum
        intro j hj
        exact hterm j
      _ = power t beta * (1 + ∑ j, s.F t i j) := by
        rw [← Finset.sum_mul]
        ring
      _ ≤ power t beta * (1 + C * (C + ‖s.rawLag i‖)) := by
        apply mul_le_mul_of_nonneg_left ?_ a_nonneg
        linarith
  have hxnon : 0 ≤ ‖s.rawLag i‖ := norm_nonneg _
  have hcross : power t beta * C * ‖s.rawLag i‖ ≤ ‖s.rawLag i‖ / 2 := by
    calc
      power t beta * C * ‖s.rawLag i‖ = (C * power t beta) * ‖s.rawLag i‖ := by ring
      _ ≤ (1 / 2) * ‖s.rawLag i‖ := mul_le_mul_of_nonneg_right hsmall hxnon
      _ = ‖s.rawLag i‖ / 2 := by ring
  nlinarith [hrawIneq, hcross]

lemma F_row_sum_small_of_prestate {P : Type*} [Fintype P] [DecidableEq P]
    (t C : ℝ) (Λplus Wstar : Form P) (s : State P)
    (hC : 1 ≤ C) (hsmall : C * power t beta ≤ 1 / 2)
    (hp : Prestate t C Λplus Wstar s) :
    ∀ i, ∑ j, s.F t i j ≤ C * (C + 2 * power t beta * (1 + C ^ 2)) := by
  have hraw := rawLag_small_of_prestate t C Λplus Wstar s hC hsmall hp
  have hrow := F_row_sum_le_Cq t C Λplus Wstar s hC hp
  have hCpos : 0 < C := by linarith
  intro i
  have hqUpper : s.q i ≤ C + ‖s.rawLag i‖ := by
    have hqp : s.q i - s.p i = (s.rawLag i).im := by
      simp [State.q, State.p, State.rawLag, Complex.sub_im]
    have him := Complex.im_le_norm (s.rawLag i)
    linarith [(hp.broad i).2.2]
  calc
    (∑ j, s.F t i j) ≤ C * s.q i := hrow i
    _ ≤ C * (C + ‖s.rawLag i‖) := mul_le_mul_of_nonneg_left hqUpper hCpos.le
    _ ≤ C * (C + 2 * power t beta * (1 + C ^ 2)) := by
      apply mul_le_mul_of_nonneg_left ?_ hCpos.le
      linarith [hraw i]

lemma hdiag_small_of_prestate {P : Type*} [Fintype P] [DecidableEq P]
    (t C : ℝ) (Λplus Wstar : Form P) (s : State P)
    (hC : 1 ≤ C) (hsmall : C * power t beta ≤ 1 / 2)
    (hp : Prestate t C Λplus Wstar s) :
    ∀ i, ‖s.h t i i‖ ≤ (C + 2 * (1 + C ^ 2)) * Real.sqrt t := by
  have hraw := rawLag_small_of_prestate t C Λplus Wstar s hC hsmall hp
  have hβ : 0 ≤ AndersonAC.S45.beta := by norm_num [AndersonAC.S45.beta, delta]
  have ha_le_one : power t AndersonAC.S45.beta ≤ 1 :=
    Real.rpow_le_one hp.scale.1.le hp.scale.2.le hβ
  have hsqrt : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  intro i
  have hg : ‖s.g i i‖ ≤ C + 2 * (1 + C ^ 2) := by
    have hsplit : s.g i i = s.r i + s.rawLag i := by
      simp [State.rawLag]
    rw [hsplit]
    calc
      ‖s.r i + s.rawLag i‖ ≤ ‖s.r i‖ + ‖s.rawLag i‖ := norm_add_le _ _
      _ ≤ C + 2 * power t beta * (1 + C ^ 2) :=
        add_le_add (hp.broad i).1 (hraw i)
      _ ≤ C + 2 * (1 + C ^ 2) := by nlinarith [ha_le_one]
  calc
    ‖s.h t i i‖ = Real.sqrt t * ‖s.g i i‖ := by
      simp [State.h, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t)]
    _ = ‖s.g i i‖ * Real.sqrt t := by ring
    _ ≤ (C + 2 * (1 + C ^ 2)) * Real.sqrt t :=
      mul_le_mul_of_nonneg_right hg hsqrt

lemma g_diag_bound_of_prestate {P : Type*} [Fintype P] [DecidableEq P]
    (t C : ℝ) (Λplus Wstar : Form P) (s : State P)
    (hC : 1 ≤ C) (hsmall : C * power t beta ≤ 1 / 2)
    (hp : Prestate t C Λplus Wstar s) :
    ∀ i, ‖s.g i i‖ + ‖s.r i‖ ≤ 2 * C + 2 * (1 + C ^ 2) := by
  have hraw := rawLag_small_of_prestate t C Λplus Wstar s hC hsmall hp
  have hβ : 0 ≤ AndersonAC.S45.beta := by norm_num [AndersonAC.S45.beta, delta]
  have ha_le_one : power t AndersonAC.S45.beta ≤ 1 :=
    Real.rpow_le_one hp.scale.1.le hp.scale.2.le hβ
  intro i
  have hsplit : s.g i i = s.r i + s.rawLag i := by simp [State.rawLag]
  rw [hsplit]
  have hnorm := norm_add_le (s.r i) (s.rawLag i)
  nlinarith [hnorm, (hp.broad i).1, hraw i, ha_le_one]

lemma momentLaw_mono_constant {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {t C D : ℝ} {ξ : Ω → ℝ}
    (hCD : C ≤ D) (hM : MomentLaw μ t C ξ) : MomentLaw μ t D ξ := by
  refine ⟨hM.measurable, hM.mean, hM.variance, ?_⟩
  filter_upwards [hM.bounded] with ω hω
  exact hω.trans (mul_le_mul_of_nonneg_right hCD (Real.sqrt_nonneg t))

lemma q_minus_p_small_of_prestate {P : Type*} [Fintype P] [DecidableEq P]
    (t C : ℝ) (Λplus Wstar : Form P) (s : State P)
    (hC : 1 ≤ C) (hsmall : C * power t beta ≤ 1 / 2)
    (hp : Prestate t C Λplus Wstar s) :
    ∀ i, |s.q i - s.p i| ≤ 2 * power t beta * (1 + C ^ 2) := by
  have hraw := rawLag_small_of_prestate t C Λplus Wstar s hC hsmall hp
  intro i
  have hqp : s.q i - s.p i = (s.rawLag i).im := by
    simp [State.q, State.p, State.rawLag, Complex.sub_im]
  calc
    |s.q i - s.p i| = |(s.rawLag i).im| := by rw [hqp]
    _ ≤ ‖s.rawLag i‖ := Complex.abs_im_le_norm _
    _ ≤ 2 * power t beta * (1 + C ^ 2) := hraw i

lemma t_le_sqrt_mul_power_beta {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    t ≤ Real.sqrt t * power t beta := by
  have hβ : 0 ≤ AndersonAC.S45.beta := by norm_num [AndersonAC.S45.beta, delta]
  have hexp : 1 / 2 + AndersonAC.S45.beta ≤ 1 := by
    norm_num [AndersonAC.S45.beta, delta]
  have hprod : Real.sqrt t * power t AndersonAC.S45.beta =
      power t (1 / 2 + AndersonAC.S45.beta) := by
    rw [Real.sqrt_eq_rpow]
    change Real.rpow t (1 / 2) * Real.rpow t AndersonAC.S45.beta = _
    exact (Real.rpow_add ht _ _).symm
  calc
    t = power t 1 := by simp [power, Real.rpow_one]
    _ ≤ power t (1 / 2 + AndersonAC.S45.beta) :=
      Real.rpow_le_rpow_of_exponent_ge ht ht1 hexp
    _ = Real.sqrt t * power t beta := hprod.symm

lemma sqrt_le_power_beta {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    Real.sqrt t ≤ power t beta := by
  have hβ : AndersonAC.S45.beta ≤ 1 / 2 := by
    norm_num [AndersonAC.S45.beta, delta]
  calc
    Real.sqrt t = power t (1 / 2) := by simp [power, Real.sqrt_eq_rpow]
    _ ≤ power t AndersonAC.S45.beta :=
      Real.rpow_le_rpow_of_exponent_ge ht ht1 hβ

lemma deletion_denominator_lower_of_prestate {P : Type*} [Fintype P] [DecidableEq P]
    (t C : ℝ) (Λplus Wstar : Form P) (s : State P)
    (hC : 1 ≤ C) (hsmall : C * power t beta ≤ 1 / 2)
    (hsmallq : 2 * (1 + C ^ 2) * power t beta ≤ 1 / (4 * C))
    (hsmallt : C * (C + 2 * (1 + C ^ 2)) ^ 2 * t ≤ 1 / (4 * C))
    (hp : Prestate t C Λplus Wstar s) :
    ∀ i, 1 / (2 * C) ≤ s.q i - s.p i * s.F t i i := by
  have hqp := q_minus_p_small_of_prestate t C Λplus Wstar s hC hsmall hp
  have hdiag := hdiag_small_of_prestate t C Λplus Wstar s hC hsmall hp
  have hCpos : 0 < C := by linarith
  intro i
  have hpLower : 1 / C ≤ s.p i := (hp.broad i).2.1
  have hpUpper : s.p i ≤ C := (hp.broad i).2.2
  have hpNon : 0 ≤ s.p i := by
    have hInv : 0 < 1 / C := by positivity
    linarith
  have hFnon : 0 ≤ s.F t i i := by simp [State.F, entryAbsSquare]
  have hFdiag : s.F t i i ≤ (C + 2 * (1 + C ^ 2)) ^ 2 * t := by
    have hFdef : s.F t i i = ‖s.h t i i‖ ^ 2 := by simp [State.F, entryAbsSquare]
    rw [hFdef]
    have hsquare : ‖s.h t i i‖ ^ 2 ≤
        ((C + 2 * (1 + C ^ 2)) * Real.sqrt t) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (hdiag i)
    have hroot : ((C + 2 * (1 + C ^ 2)) * Real.sqrt t) ^ 2 =
        (C + 2 * (1 + C ^ 2)) ^ 2 * t := by
      rw [mul_pow, Real.sq_sqrt hp.scale.1.le]
    nlinarith [hsquare, hroot]
  have hqplower : -(2 * (1 + C ^ 2) * power t beta) ≤ s.q i - s.p i := by
    nlinarith [(abs_le.mp (hqp i)).1]
  have hpFupper : s.p i * s.F t i i ≤
      C * (C + 2 * (1 + C ^ 2)) ^ 2 * t := by
    calc
      s.p i * s.F t i i ≤ C * s.F t i i :=
        mul_le_mul_of_nonneg_right hpUpper hFnon
      _ ≤ C * ((C + 2 * (1 + C ^ 2)) ^ 2 * t) :=
        mul_le_mul_of_nonneg_left hFdiag hCpos.le
      _ = C * (C + 2 * (1 + C ^ 2)) ^ 2 * t := by ring
  have hdenId : s.q i - s.p i * s.F t i i =
      s.p i + (s.q i - s.p i) - s.p i * s.F t i i := by ring
  have herror : 2 * (1 + C ^ 2) * power t beta +
      C * (C + 2 * (1 + C ^ 2)) ^ 2 * t ≤ 1 / (2 * C) := by
    have := add_le_add hsmallq hsmallt
    calc
      _ ≤ 1 / (4 * C) + 1 / (4 * C) := this
      _ = 1 / (2 * C) := by ring
  have hbase : 1 / C - 2 * (1 + C ^ 2) * power t beta -
      C * (C + 2 * (1 + C ^ 2)) ^ 2 * t ≥ 1 / (2 * C) := by
    have hrecip : 1 / (2 * C) + 1 / (2 * C) = 1 / C := by
      field_simp [ne_of_gt hCpos]
      ring
    linarith
  rw [hdenId]
  linarith [hpLower, hqplower, hpFupper, hbase]

lemma deletion_c_close_to_one_of_prestate {P : Type*} [Fintype P] [DecidableEq P]
    (t C : ℝ) (Λplus Wstar : Form P) (s : State P)
    (hC : 1 ≤ C) (hsmall : C * power t beta ≤ 1 / 2)
    (hsmallq : 2 * (1 + C ^ 2) * power t beta ≤ 1 / (4 * C))
    (hsmallt : C * (C + 2 * (1 + C ^ 2)) ^ 2 * t ≤ 1 / (4 * C))
    (hp : Prestate t C Λplus Wstar s) :
    ∀ i, |s.p i / (s.q i - s.p i * s.F t i i) - 1| ≤
      2 * C * (2 * (1 + C ^ 2) + C * (C + 2 * (1 + C ^ 2)) ^ 2) * power t beta := by
  have hden := deletion_denominator_lower_of_prestate t C Λplus Wstar s hC
    hsmall hsmallq hsmallt hp
  have hqp := q_minus_p_small_of_prestate t C Λplus Wstar s hC hsmall hp
  have hdiag := hdiag_small_of_prestate t C Λplus Wstar s hC hsmall hp
  have hβ : 0 ≤ AndersonAC.S45.beta := by norm_num [AndersonAC.S45.beta, delta]
  have ha : 0 ≤ power t AndersonAC.S45.beta :=
    Real.rpow_nonneg hp.scale.1.le _
  have hta : t ≤ power t beta := by
    have hsqrtle : Real.sqrt t ≤ 1 := by
      have hsq := Real.sq_sqrt hp.scale.1.le
      nlinarith [hp.scale.2.le]
    calc
      t ≤ Real.sqrt t * power t beta :=
        t_le_sqrt_mul_power_beta hp.scale.1 hp.scale.2.le
      _ ≤ 1 * power t beta := mul_le_mul_of_nonneg_right hsqrtle ha
      _ = power t beta := by ring
  have hCpos : 0 < C := by linarith
  intro i
  let d := s.q i - s.p i * s.F t i i
  have hdLower : 1 / (2 * C) ≤ d := by
    simpa [d] using hden i
  have hdpos : 0 < d := lt_of_lt_of_le (by positivity) hdLower
  have hFnon : 0 ≤ s.F t i i := by simp [State.F, entryAbsSquare]
  have hFdiag : s.F t i i ≤ (C + 2 * (1 + C ^ 2)) ^ 2 * t := by
    have hFdef : s.F t i i = ‖s.h t i i‖ ^ 2 := by simp [State.F, entryAbsSquare]
    rw [hFdef]
    have hsquare : ‖s.h t i i‖ ^ 2 ≤
        ((C + 2 * (1 + C ^ 2)) * Real.sqrt t) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (hdiag i)
    have hroot : ((C + 2 * (1 + C ^ 2)) * Real.sqrt t) ^ 2 =
        (C + 2 * (1 + C ^ 2)) ^ 2 * t := by
      rw [mul_pow, Real.sq_sqrt hp.scale.1.le]
    nlinarith [hsquare, hroot]
  have hpNon : 0 ≤ s.p i := by
    have : 0 < 1 / C := by positivity
    linarith [(hp.broad i).2.1]
  have hpF : s.p i * s.F t i i ≤
      C * (C + 2 * (1 + C ^ 2)) ^ 2 * t := by
    calc
      s.p i * s.F t i i ≤ C * s.F t i i :=
        mul_le_mul_of_nonneg_right (hp.broad i).2.2 hFnon
      _ ≤ C * ((C + 2 * (1 + C ^ 2)) ^ 2 * t) :=
        mul_le_mul_of_nonneg_left hFdiag hCpos.le
      _ = C * (C + 2 * (1 + C ^ 2)) ^ 2 * t := by ring
  have hpFa : s.p i * s.F t i i ≤
      C * (C + 2 * (1 + C ^ 2)) ^ 2 * power t beta := by
    calc
      s.p i * s.F t i i ≤ C * (C + 2 * (1 + C ^ 2)) ^ 2 * t := hpF
      _ ≤ C * (C + 2 * (1 + C ^ 2)) ^ 2 * power t beta := by
        exact mul_le_mul_of_nonneg_left hta (by positivity)
  have hpd : s.p i - d = (s.p i - s.q i) + s.p i * s.F t i i := by
    dsimp [d]
    ring
  have hpq : |s.p i - s.q i| = |s.q i - s.p i| := by rw [abs_sub_comm]
  have hqpb : |s.q i - s.p i| ≤ 2 * (1 + C ^ 2) * power t beta := by
    calc
      |s.q i - s.p i| ≤ 2 * power t beta * (1 + C ^ 2) := hqp i
      _ = 2 * (1 + C ^ 2) * power t beta := by ring
  have hnum : |s.p i - d| ≤
      (2 * (1 + C ^ 2) + C * (C + 2 * (1 + C ^ 2)) ^ 2) * power t beta := by
    rw [hpd]
    calc
      |(s.p i - s.q i) + s.p i * s.F t i i| ≤
          |s.p i - s.q i| + |s.p i * s.F t i i| := abs_add_le _ _
      _ = |s.q i - s.p i| + s.p i * s.F t i i := by
        rw [hpq, abs_of_nonneg (mul_nonneg hpNon hFnon)]
      _ ≤ 2 * (1 + C ^ 2) * power t beta +
          C * (C + 2 * (1 + C ^ 2)) ^ 2 * power t beta := by
        exact add_le_add hqpb hpFa
      _ = (2 * (1 + C ^ 2) + C * (C + 2 * (1 + C ^ 2)) ^ 2) * power t beta := by ring
  have hrecip : 1 / d ≤ 2 * C := by
    rw [div_le_iff₀ hdpos]
    have hmul := mul_le_mul_of_nonneg_left hdLower (by positivity : 0 ≤ 2 * C)
    have hleft : (2 * C) * (1 / (2 * C)) = 1 := by field_simp [ne_of_gt hCpos]
    calc
      1 = (2 * C) * (1 / (2 * C)) := hleft.symm
      _ ≤ (2 * C) * d := hmul
  have hc : s.p i / d - 1 = (s.p i - d) / d := by
    field_simp [ne_of_gt hdpos]
  calc
    |s.p i / d - 1| = |(s.p i - d) / d| := by rw [hc]
    _ = |s.p i - d| / d := by rw [abs_div, abs_of_pos hdpos]
    _ ≤ ((2 * (1 + C ^ 2) + C * (C + 2 * (1 + C ^ 2)) ^ 2) * power t beta) / d :=
      div_le_div_of_nonneg_right hnum hdpos.le
    _ = ((2 * (1 + C ^ 2) + C * (C + 2 * (1 + C ^ 2)) ^ 2) * power t beta) * (1 / d) := by ring
    _ ≤ ((2 * (1 + C ^ 2) + C * (C + 2 * (1 + C ^ 2)) ^ 2) * power t beta) * (2 * C) :=
      mul_le_mul_of_nonneg_left hrecip (by positivity)
    _ = 2 * C * (2 * (1 + C ^ 2) + C * (C + 2 * (1 + C ^ 2)) ^ 2) * power t beta := by ring

lemma integrable_sq_norm_of_ae_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℂ} {G : ℝ}
    (hG : 0 ≤ G) (hf : Measurable f) (hbound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ G) :
    Integrable (fun ω => ‖f ω‖ ^ 2) μ := by
  have hmeas : Measurable (fun ω => ‖f ω‖ ^ 2) := hf.norm.pow_const 2
  apply Integrable.of_bound hmeas.aestronglyMeasurable (G ^ 2)
  filter_upwards [hbound] with ω hω
  have hsquare : ‖f ω‖ ^ 2 ≤ G ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hG).2 hω
  simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖f ω‖))] using hsquare

lemma rho_integral_close {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G K t : ℝ) (γ : Ω → ℂ) (c : ℝ)
    (hG : 0 ≤ G) (hγ : Measurable γ)
    (hγBound : ∀ᵐ ω ∂μ, ‖γ ω‖ ≤ G)
    (hsecond : |(∫ ω, ‖γ ω‖ ^ 2 ∂μ) - 1| ≤ G * Real.sqrt t)
    (hc : |c - 1| ≤ K * power t beta) (ht : 0 < t) (ht1 : t ≤ 1) :
    |∫ ω, (‖γ ω‖ ^ 2 - c) ∂μ| ≤ (G + K) * power t beta := by
  have hsqInt := integrable_sq_norm_of_ae_bound (μ := μ) hG hγ hγBound
  have hcInt : Integrable (fun _ : Ω => c) μ := integrable_const c
  have hsplit : (∫ ω, (‖γ ω‖ ^ 2 - c) ∂μ) =
      (∫ ω, ‖γ ω‖ ^ 2 ∂μ) - c := by
    rw [integral_sub hsqInt hcInt]
    simp
  have hc' : |1 - c| ≤ K * power t beta := by simpa [abs_sub_comm] using hc
  calc
    |∫ ω, (‖γ ω‖ ^ 2 - c) ∂μ| =
        |((∫ ω, ‖γ ω‖ ^ 2 ∂μ) - 1) + (1 - c)| := by rw [hsplit]; congr 1 <;> ring
    _ ≤ |(∫ ω, ‖γ ω‖ ^ 2 ∂μ) - 1| + |1 - c| := abs_add_le _ _
    _ ≤ G * Real.sqrt t + K * power t beta := add_le_add hsecond hc'
    _ ≤ G * power t beta + K * power t beta :=
      add_le_add (mul_le_mul_of_nonneg_left (sqrt_le_power_beta ht ht1) hG) le_rfl
    _ = (G + K) * power t beta := by ring

lemma rho_expected_small_of_prestate {P Ω : Type*} [Fintype P] [DecidableEq P]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (t C G : ℝ) (Λplus Wstar : Form P) (s : State P) (x : P)
    (ξ : Ω → ℝ) (hC : 1 ≤ C) (hsmall : C * power t beta ≤ 1 / 2)
    (hsmallq : 2 * (1 + C ^ 2) * power t beta ≤ 1 / (4 * C))
    (hsmallt : C * (C + 2 * (1 + C ^ 2)) ^ 2 * t ≤ 1 / (4 * C))
    (hp : Prestate t C Λplus Wstar s) (hM : MomentLaw μ t C ξ)
    (hG : 0 ≤ G) (hγBound : ∀ᵐ ω ∂μ, ‖gamma t s x (ξ ω)‖ ≤ G)
    (hsecond : |(∫ ω, ‖gamma t s x (ξ ω)‖ ^ 2 ∂μ) - 1| ≤ G * Real.sqrt t) :
    |∫ ω, (‖gamma t s x (ξ ω)‖ ^ 2 -
      s.p x / (s.q x - s.p x * s.F t x x)) ∂μ| ≤
      (G + 2 * C * (2 * (1 + C ^ 2) + C * (C + 2 * (1 + C ^ 2)) ^ 2)) *
        power t beta := by
  let c := s.p x / (s.q x - s.p x * s.F t x x)
  have hc := deletion_c_close_to_one_of_prestate t C Λplus Wstar s hC
    hsmall hsmallq hsmallt hp x
  have hγMeas : Measurable (fun ω => gamma t s x (ξ ω)) := by
    change Measurable (fun ω =>
      ((ξ ω : ℂ) + t * s.r x) /
        ((Real.sqrt t : ℂ) * (1 + ((ξ ω : ℂ) + t * s.r x) * s.g x x)))
    have hξC : Measurable (fun ω => (ξ ω : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp hM.measurable
    have hnum : Measurable (fun ω => (ξ ω : ℂ) + t * s.r x) :=
      hξC.add measurable_const
    have hden : Measurable (fun ω =>
        (Real.sqrt t : ℂ) * (1 + ((ξ ω : ℂ) + t * s.r x) * s.g x x)) :=
      measurable_const.mul (measurable_const.add (hnum.mul measurable_const))
    exact hnum.div hden
  have ht : 0 < t := hp.scale.1
  have ht1 : t ≤ 1 := hp.scale.2.le
  have hclose := rho_integral_close μ G
    (2 * C * (2 * (1 + C ^ 2) + C * (C + 2 * (1 + C ^ 2)) ^ 2)) t
    (fun ω => gamma t s x (ξ ω)) c hG hγMeas hγBound hsecond ?_ ht ht1
  · simpa [c] using hclose
  · simpa [c] using hc

lemma gamma_rho_uniform_bound_of_prestate {P Ω : Type*} [Fintype P] [DecidableEq P]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (t C G : ℝ) (Λplus Wstar : Form P) (s : State P) (x : P)
    (ξ : Ω → ℝ) (hC : 1 ≤ C) (hsmall : C * power t beta ≤ 1 / 2)
    (hsmallq : 2 * (1 + C ^ 2) * power t beta ≤ 1 / (4 * C))
    (hsmallt : C * (C + 2 * (1 + C ^ 2)) ^ 2 * t ≤ 1 / (4 * C))
    (hp : Prestate t C Λplus Wstar s) (hG : 0 ≤ G)
    (hγBound : ∀ᵐ ω ∂μ, ‖gamma t s x (ξ ω)‖ ≤ G) :
    ∀ᵐ ω ∂μ, ‖gamma t s x (ξ ω)‖ +
      |‖gamma t s x (ξ ω)‖ ^ 2 -
        s.p x / (s.q x - s.p x * s.F t x x)| ≤ G + G ^ 2 + 2 * C ^ 2 := by
  have hden := deletion_denominator_lower_of_prestate t C Λplus Wstar s hC
    hsmall hsmallq hsmallt hp x
  have hCpos : 0 < C := by linarith
  have hdpos : 0 < s.q x - s.p x * s.F t x x :=
    lt_of_lt_of_le (by positivity) hden
  have hpNon : 0 ≤ s.p x := by
    have hinv : 0 < 1 / C := by positivity
    linarith [(hp.broad x).2.1]
  have hrecip : 1 / (s.q x - s.p x * s.F t x x) ≤ 2 * C := by
    rw [div_le_iff₀ hdpos]
    have hmul := mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ 2 * C)
    have hleft : (2 * C) * (1 / (2 * C)) = 1 := by
      field_simp [ne_of_gt hCpos]
    linarith
  let c := s.p x / (s.q x - s.p x * s.F t x x)
  have hcNon : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg hpNon hdpos.le
  have hcBound : c ≤ 2 * C ^ 2 := by
    dsimp [c]
    calc
      s.p x / (s.q x - s.p x * s.F t x x) =
          s.p x * (1 / (s.q x - s.p x * s.F t x x)) := by ring
      _ ≤ C * (2 * C) :=
        mul_le_mul (hp.broad x).2.2 hrecip (by positivity) hCpos.le
      _ = 2 * C ^ 2 := by ring
  filter_upwards [hγBound] with ω hω
  have hsq : ‖gamma t s x (ξ ω)‖ ^ 2 ≤ G ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hG).2 hω
  have hrho : |‖gamma t s x (ξ ω)‖ ^ 2 - c| ≤ G ^ 2 + 2 * C ^ 2 := by
    calc
      |‖gamma t s x (ξ ω)‖ ^ 2 - c| ≤
          |‖gamma t s x (ξ ω)‖ ^ 2| + |c| := abs_sub _ _
      _ = ‖gamma t s x (ξ ω)‖ ^ 2 + c := by
        rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg hcNon]
      _ ≤ G ^ 2 + 2 * C ^ 2 := add_le_add hsq hcBound
  change ‖gamma t s x (ξ ω)‖ +
      |‖gamma t s x (ξ ω)‖ ^ 2 - c| ≤ G + G ^ 2 + 2 * C ^ 2
  linarith [hω, hrho]

lemma gamma_mean_small_of_approx {P Ω : Type*} [Fintype P] [DecidableEq P]
    [MeasurableSpace Ω] (μ : Measure Ω) (C G t : ℝ)
    (Λplus Wstar : Form P) (s : State P) (x : P) (ξ : Ω → ℝ)
    (hC : 1 ≤ C) (hG : 0 ≤ G) (hsmall : C * power t beta ≤ 1 / 2)
    (hp : Prestate t C Λplus Wstar s)
    (hmean : ‖(∫ ω, gamma t s x (ξ ω) ∂μ) + s.z t x‖ ≤ G * t) :
    ‖∫ ω, gamma t s x (ξ ω) ∂μ‖ ≤
      (G + 2 * (1 + C ^ 2)) * Real.sqrt t * power t beta := by
  have hraw := rawLag_small_of_prestate t C Λplus Wstar s hC hsmall hp
  have hsqrt : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have htprod : t ≤ Real.sqrt t * power t beta :=
    t_le_sqrt_mul_power_beta hp.scale.1 hp.scale.2.le
  have hz : ‖s.z t x‖ ≤ 2 * (1 + C ^ 2) * Real.sqrt t * power t beta := by
    calc
      ‖s.z t x‖ = Real.sqrt t * ‖s.rawLag x‖ := by
        simp [State.z, Real.norm_eq_abs, abs_of_nonneg hsqrt]
      _ ≤ Real.sqrt t * (2 * power t beta * (1 + C ^ 2)) :=
        mul_le_mul_of_nonneg_left (hraw x) hsqrt
      _ = 2 * (1 + C ^ 2) * Real.sqrt t * power t beta := by ring
  calc
    ‖∫ ω, gamma t s x (ξ ω) ∂μ‖ =
        ‖((∫ ω, gamma t s x (ξ ω) ∂μ) + s.z t x) - s.z t x‖ := by
          congr 1
          abel
    _ ≤ ‖(∫ ω, gamma t s x (ξ ω) ∂μ) + s.z t x‖ + ‖s.z t x‖ := norm_sub_le _ _
    _ ≤ G * t + 2 * (1 + C ^ 2) * Real.sqrt t * power t beta := add_le_add hmean hz
    _ ≤ G * (Real.sqrt t * power t beta) +
        2 * (1 + C ^ 2) * Real.sqrt t * power t beta := by
          exact add_le_add (mul_le_mul_of_nonneg_left htprod hG) le_rfl
    _ = (G + 2 * (1 + C ^ 2)) * Real.sqrt t * power t beta := by ring

lemma gamma_moments_prestate_of_small : ∀ (C : ℝ), 1 ≤ C →
    ∃ G > 0, ∃ tG > 0,
    ∀ (P Ω : Type) [Fintype P] [DecidableEq P] [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℝ) (s : State P)
      (Λplus Wstar : Form P) (x : P) (ξ : Ω → ℝ),
      t < tG → C * power t beta ≤ 1 / 2 →
      Prestate t C Λplus Wstar s → MomentLaw μ t C ξ →
      (∀ᵐ ω ∂μ, ‖gamma t s x (ξ ω)‖ ≤ G ∧
        1 + ((ξ ω : ℂ) + t * s.r x) * s.g x x ≠ 0) ∧
      ‖∫ ω, gamma t s x (ξ ω) ∂μ‖ ≤
        (G + 2 * (1 + C ^ 2)) * Real.sqrt t * power t beta ∧
      |(∫ ω, ‖gamma t s x (ξ ω)‖ ^ 2 ∂μ) - 1| ≤ G * Real.sqrt t := by
  intro C hC
  let D : ℝ := 2 * C + 2 * (1 + C ^ 2)
  have hD : 1 ≤ D := by
    dsimp [D]
    nlinarith [sq_nonneg C]
  have hDC : C ≤ D := by
    dsimp [D]
    nlinarith [sq_nonneg C]
  obtain ⟨G, hG, tG, htG, hGamma⟩ := gamma_moments_proof D hD
  refine ⟨G, hG, tG, htG, ?_⟩
  intro P Ω instP instDec instM μ instProb t s Λplus Wstar x ξ htG' hsmall hp hM
  have hstate : ‖s.g x x‖ + ‖s.r x‖ ≤ D := by
    simpa [D] using g_diag_bound_of_prestate t C Λplus Wstar s hC hsmall hp x
  have hM' : MomentLaw μ t D ξ := momentLaw_mono_constant hDC hM
  have hgamma := hGamma P Ω μ t s x ξ hp.scale.1 htG' hstate hM'
  rcases hgamma with ⟨hpair, hmean, hsecond, hnormsq⟩
  exact ⟨hpair,
    gamma_mean_small_of_approx μ C G t Λplus Wstar s x ξ hC hG.le hsmall hp hmean,
    hnormsq⟩

end AndersonAC.AgentS45
