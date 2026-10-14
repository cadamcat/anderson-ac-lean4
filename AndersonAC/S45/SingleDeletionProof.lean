import AndersonAC.S45.Definitions

noncomputable section
open Matrix
open scoped BigOperators

namespace AndersonAC.AgentS45

open AndersonAC.S45

lemma weighted_norm_sum {ι : Type*} [Fintype ι] (h : ι → ℂ) (p : ι → ℝ) :
    (↑(∑ i, p i * ‖h i‖ ^ 2) : ℂ) =
      ∑ i, h i * (p i : ℂ) * star (h i) := by
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hnorm : star (h i) * h i = (↑(‖h i‖ ^ 2) : ℂ) := by
    simpa [Complex.star_def, Complex.normSq_eq_norm_sq] using
      (Complex.normSq_eq_conj_mul_self (z := h i)).symm
  calc
    (↑(p i * ‖h i‖ ^ 2) : ℂ) =
        (p i : ℂ) * (↑(‖h i‖ ^ 2) : ℂ) := by push_cast; ring
    _ = h i * (p i : ℂ) * star (h i) := by rw [← hnorm]; ring

lemma ward_entry_h {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (hw : s.ward t) (i j : P) :
    (∑ k, s.h t i k * (s.p k : ℂ) * star (s.h t j k)) = (s.g i j).im := by
  have h := congrFun (congrFun hw i) j
  simpa [State.ward, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.conjTranspose_apply, matrixIm, State.h, Matrix.smul_apply,
    mul_assoc, mul_left_comm, mul_comm] using h

lemma sum_survivors_sub {P : Type*} [Fintype P] [DecidableEq P]
    {β : Type*} [AddCommGroup β] (x : P) (f : P → β) :
    (∑ i : survivors x, f i.val) = (∑ i, f i) - f x := by
  rw [← Finset.sum_subtype (Finset.univ.erase x) (by simp [survivors]) f]
  rw [← Finset.sum_erase_add (Finset.univ) f (Finset.mem_univ x)]
  simp <;> abel

lemma ward_diag_row {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (hw : s.ward t) (i : P) :
    (∑ k, s.p k * ‖s.h t i k‖ ^ 2) = s.q i := by
  have h := ward_entry_h t s hw i i
  have hreal : (∑ k, s.h t i k * (s.p k : ℂ) * star (s.h t i k)) =
      (↑(∑ k, s.p k * ‖s.h t i k‖ ^ 2) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hnorm : star (s.h t i k) * s.h t i k =
        (↑(‖s.h t i k‖ ^ 2) : ℂ) := by
      simpa [Complex.star_def, Complex.normSq_eq_norm_sq] using
        (Complex.normSq_eq_conj_mul_self (z := s.h t i k)).symm
    calc
      s.h t i k * (s.p k : ℂ) * star (s.h t i k) =
          (s.p k : ℂ) * (star (s.h t i k) * s.h t i k) := by ring
      _ = (s.p k : ℂ) * (↑(‖s.h t i k‖ ^ 2) : ℂ) := by
        rw [hnorm]
      _ = (↑(s.p k * ‖s.h t i k‖ ^ 2) : ℂ) := by push_cast; ring
  have hq : (↑(∑ k, s.p k * ‖s.h t i k‖ ^ 2) : ℂ) = (s.q i : ℂ) := by
    calc
      (↑(∑ k, s.p k * ‖s.h t i k‖ ^ 2) : ℂ) =
          ∑ k, s.h t i k * (s.p k : ℂ) * star (s.h t i k) := hreal.symm
      _ = (s.g i i).im := h
      _ = (s.q i : ℂ) := rfl
  exact Complex.ofReal_injective hq

lemma D_entry {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (i j : P) :
    s.D t i j = (if i = j then s.p i * s.q i else 0) -
      s.p i * s.F t i j * s.p j := by
  simp [State.D, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.one_apply, mul_assoc]

lemma D_row_sum {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (hw : s.ward t) (i : P) :
    (∑ j, s.D t i j) = 0 := by
  simp_rw [D_entry]
  rw [Finset.sum_sub_distrib]
  have hdiag : (∑ j, if i = j then s.p i * s.q i else 0) = s.p i * s.q i := by
    simp
  rw [hdiag]
  have hfactor : (∑ j, s.p i * s.F t i j * s.p j) =
      s.p i * (∑ j, s.F t i j * s.p j) := by
    calc
      (∑ j, (s.p i * s.F t i j) * s.p j) =
          ∑ j, s.p i * (s.F t i j * s.p j) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = s.p i * (∑ j, s.F t i j * s.p j) := by rw [← Finset.mul_sum]
  have hrow := ward_diag_row t s hw i
  have hrow' : (∑ j, s.F t i j * s.p j) = s.q i := by
    simpa [State.F, entryAbsSquare, mul_comm] using hrow
  calc
    s.p i * s.q i - (∑ j, s.p i * s.F t i j * s.p j) = 0 := by
      rw [hfactor, hrow']
      ring

lemma scalar_ward_coeff (t p q : ℝ) (c d z : ℂ)
    (hcim : c.im = t * p) (hzim : z.im = q)
    (hd : d = 1 + c * z) (hdne : d ≠ 0) :
    (c / d).im + Complex.normSq c / Complex.normSq d * q -
      t * p / Complex.normSq d = 0 := by
  have hnormd : Complex.normSq d ≠ 0 := fun h => hdne (Complex.normSq_eq_zero.mp h)
  have hdre : d.re = 1 + c.re * z.re - c.im * z.im := by
    rw [hd]
    simp [Complex.add_re, Complex.mul_re]
    ring
  have hdim : d.im = c.re * z.im + c.im * z.re := by
    rw [hd]
    simp [Complex.add_im, Complex.mul_im]
  rw [Complex.div_im]
  field_simp [hnormd]
  rw [hdre, hdim, Complex.normSq_apply, hzim, hcim]
  ring

lemma im_mul_sq (a z : ℂ) :
    -2 * (a * z).re * z.im - a.im * Complex.normSq z = -(a * z ^ 2).im := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.normSq_apply, pow_two]
  ring

lemma normSq_sub_update (a b : ℂ) :
    Complex.normSq (a - b) = Complex.normSq a - 2 * (b * (starRingEnd ℂ) a).re +
      Complex.normSq b := by
  rw [Complex.normSq_sub]
  have hre : (a * starRingEnd ℂ b).re = (b * starRingEnd ℂ a).re := by
    simp [Complex.mul_re]
    ring
  nlinarith [hre]

lemma delete_diag_ward_row {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (x : P) (ξ : ℝ) (ht : 0 < t)
    (hsym : s.g.IsSymm) (hw : s.ward t)
    (hden : 1 + ((ξ : ℂ) + t * s.r x) * s.g x x ≠ 0)
    (hupdate : ∀ i j : survivors x,
      (deleteState t s x ξ).h t i j =
        s.h t i.val j.val - gamma t s x ξ * s.h t i.val x * s.h t x j.val)
    (i : survivors x) :
    (∑ j : survivors x, s.p j.val * ‖(deleteState t s x ξ).h t i j‖ ^ 2) =
      (deleteState t s x ξ).q i := by
  classical
  let s' := deleteState t s x ξ
  let c : ℂ := (ξ : ℂ) + t * s.r x
  let d : ℂ := 1 + c * s.g x x
  let a : ℂ := c / d
  let z : ℂ := s.g i.val x
  let b : ℂ := a * z
  let H : P → ℂ := fun k => s.h t i.val k - b * s.h t x k
  have hsqrt_pos : (Real.sqrt t : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 ht))
  have hdne : d ≠ 0 := by
    dsimp [d, c]
    exact hden
  have hcim : c.im = t * s.p x := by
    simp [c, State.p, Complex.add_im, Complex.mul_im]
  have hdz : d = 1 + c * s.g x x := rfl
  have hsymxi : s.g x i.val = z := by
    simpa [z] using hsym.apply i.val x
  have hsymh : s.h t x i.val = s.h t i.val x := by
    change (Real.sqrt t : ℂ) * s.g x i.val =
      (Real.sqrt t : ℂ) * s.g i.val x
    rw [hsymxi]
  have hcoeff : gamma t s x ξ * s.h t i.val x = b := by
    dsimp [gamma, a, b, c, d, z, State.h]
    field_simp [hden, hsqrt_pos]
    <;> ring
  have hfactor : 1 - a * s.g x x = d⁻¹ := by
    dsimp [a]
    field_simp [hdne]
    rw [hdz]
    ring
  have hHx : H x = (Real.sqrt t : ℂ) * z / d := by
    have hentry : s.h t i.val x = (Real.sqrt t : ℂ) * z := by
      simp [State.h, z]
    have hdiag : s.h t x x = (Real.sqrt t : ℂ) * s.g x x := by
      simp [State.h]
    dsimp [H, b]
    rw [hentry, hdiag]
    calc
      (Real.sqrt t : ℂ) * z - (a * z) * ((Real.sqrt t : ℂ) * s.g x x) =
          (Real.sqrt t : ℂ) * z * (1 - a * s.g x x) := by ring
      _ = (Real.sqrt t : ℂ) * z * d⁻¹ := by rw [hfactor]
      _ = (Real.sqrt t : ℂ) * z / d := by simp [div_eq_mul_inv, mul_comm]
  have hnormHx : Complex.normSq (H x) =
      t * Complex.normSq z / Complex.normSq d := by
    rw [hHx, Complex.normSq_div, Complex.normSq_mul, Complex.normSq_ofReal]
    have hsqrtR : Real.sqrt t * Real.sqrt t = t := by
      simpa [pow_two] using Real.sq_sqrt (le_of_lt ht)
    rw [hsqrtR]
  have halphaNorm : Complex.normSq a = Complex.normSq c / Complex.normSq d := by
    simp [a, Complex.normSq_div]
  have hscalar := scalar_ward_coeff t (s.p x) (s.q x) c d (s.g x x)
    hcim (by simp [State.q]) hdz hdne
  have hgii : s'.g i i = s.g i.val i.val - a * z ^ 2 := by
    dsimp [s', deleteState, c, a, d, z]
    rw [hsymxi]
    field_simp [hdne]
    ring
  have hfull :
      (∑ k, H k * (s.p k : ℂ) * star (H k)) =
        (s.g i.val i.val).im - b * (s.g x i.val).im -
          star b * (s.g i.val x).im + b * star b * (s.q x : ℂ) := by
    have hterm (k : P) :
        H k * (s.p k : ℂ) * star (H k) =
          s.h t i.val k * (s.p k : ℂ) * star (s.h t i.val k) -
            b * (s.h t x k * (s.p k : ℂ) * star (s.h t i.val k)) -
            star b * (s.h t i.val k * (s.p k : ℂ) * star (s.h t x k)) +
            b * star b * (s.h t x k * (s.p k : ℂ) * star (s.h t x k)) := by
      simp only [H, star_sub, star_mul]
      ring
    calc
      (∑ k, H k * (s.p k : ℂ) * star (H k)) =
          ∑ k, (s.h t i.val k * (s.p k : ℂ) * star (s.h t i.val k) -
            b * (s.h t x k * (s.p k : ℂ) * star (s.h t i.val k)) -
            star b * (s.h t i.val k * (s.p k : ℂ) * star (s.h t x k)) +
            b * star b * (s.h t x k * (s.p k : ℂ) * star (s.h t x k))) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hterm k
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
        rw [ward_entry_h t s hw i.val i.val,
          ward_entry_h t s hw x i.val, ward_entry_h t s hw i.val x]
        have hxx := ward_entry_h t s hw x x
        rw [show (∑ k, s.h t x k * (s.p k : ℂ) * star (s.h t x k)) =
          (s.q x : ℂ) by simpa [State.q] using hxx]
        <;> ring
  have hsplit :
      (∑ j : survivors x, s'.h t i j * (s'.p j : ℂ) * star (s'.h t i j)) =
        (∑ k, H k * (s.p k : ℂ) * star (H k)) -
          H x * (s.p x : ℂ) * star (H x) := by
    calc
      (∑ j : survivors x, s'.h t i j * (s'.p j : ℂ) * star (s'.h t i j)) =
          ∑ j : survivors x, H j.val * (s.p j.val : ℂ) * star (H j.val) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hentry : s'.h t i j = H j.val := by
          dsimp [H]
          rw [hupdate i j, hcoeff]
        rw [hentry]
        rfl
      _ = _ := by
        simpa [H] using (sum_survivors_sub x
          (fun k => H k * (s.p k : ℂ) * star (H k)))
  have hdel : H x * (s.p x : ℂ) * star (H x) =
      (↑(s.p x * (t * Complex.normSq z / Complex.normSq d)) : ℂ) := by
    have hstar : star (H x) * H x = (Complex.normSq (H x) : ℂ) := by
      simpa [Complex.star_def] using
        (Complex.normSq_eq_conj_mul_self (z := H x)).symm
    calc
      H x * (s.p x : ℂ) * star (H x) =
          (s.p x : ℂ) * (star (H x) * H x) := by ring
      _ = (s.p x : ℂ) * (Complex.normSq (H x) : ℂ) := by rw [hstar]
      _ = (↑(s.p x * (t * Complex.normSq z / Complex.normSq d)) : ℂ) := by
        rw [hnormHx]
        push_cast
        ring
  have hrowC : (↑(∑ j : survivors x,
      s.p j.val * ‖s'.h t i j‖ ^ 2) : ℂ) = (s'.q i : ℂ) := by
    calc
      (↑(∑ j : survivors x, s.p j.val * ‖s'.h t i j‖ ^ 2) : ℂ) =
          ∑ j : survivors x, s'.h t i j * (s'.p j : ℂ) * star (s'.h t i j) := by
        simpa [s', State.p, deleteState] using (weighted_norm_sum
          (fun j : survivors x => s'.h t i j) (fun j => s'.p j))
      _ = (s.g i.val i.val).im - b * (s.g x i.val).im -
            star b * (s.g i.val x).im + b * star b * (s.q x : ℂ) -
            (↑(s.p x * (t * Complex.normSq z / Complex.normSq d)) : ℂ) := by
        rw [hsplit, hfull, hdel]
      _ = (s'.g i i).im := by
        rw [hsymxi, show (s.g i.val x).im = z.im by rfl]
        have hz : z.im = (s.g i.val x).im := rfl
        have hcoeff' : Complex.normSq b * s.q x -
            s.p x * (t * Complex.normSq z / Complex.normSq d) =
              -a.im * Complex.normSq z := by
          have hcoeffBase : Complex.normSq a * s.q x -
              t * s.p x / Complex.normSq d = -a.im := by
            rw [halphaNorm]
            linarith [hscalar]
          calc
            Complex.normSq b * s.q x -
                s.p x * (t * Complex.normSq z / Complex.normSq d) =
              (Complex.normSq a * s.q x - t * s.p x / Complex.normSq d) *
                Complex.normSq z := by
                  dsimp [b]
                  rw [Complex.normSq_mul]
                  field_simp [hdne]
            _ = -a.im * Complex.normSq z := by rw [hcoeffBase]
        have hbb : b * star b = (Complex.normSq b : ℂ) := by
          simpa [Complex.star_def] using Complex.mul_conj b
        rw [hbb]
        have hadd : b + star b = ((2 * b.re : ℝ) : ℂ) := by
          simpa [Complex.star_def] using Complex.add_conj b
        have hcross : b * (z.im : ℂ) + star b * (z.im : ℂ) =
            ((2 * b.re * z.im : ℝ) : ℂ) := by
          calc
            b * (z.im : ℂ) + star b * (z.im : ℂ) =
                (b + star b) * (z.im : ℂ) := by ring
            _ = ((2 * b.re : ℝ) : ℂ) * (z.im : ℂ) := by rw [hadd]
            _ = ((2 * b.re * z.im : ℝ) : ℂ) := by push_cast; ring
        have hcross' : -b * (z.im : ℂ) - star b * (z.im : ℂ) =
            ((-2 * b.re * z.im : ℝ) : ℂ) := by
          calc
            -b * (z.im : ℂ) - star b * (z.im : ℂ) =
                -(b * (z.im : ℂ) + star b * (z.im : ℂ)) := by ring
            _ = -((2 * b.re * z.im : ℝ) : ℂ) := by rw [hcross]
            _ = ((-2 * b.re * z.im : ℝ) : ℂ) := by push_cast; ring
        have hcoeffC :
            (Complex.normSq b * (s.q x : ℂ) -
              (↑(s.p x * (t * Complex.normSq z / Complex.normSq d)) : ℂ)) =
                (↑(-a.im * Complex.normSq z) : ℂ) := by
          exact_mod_cast hcoeff'
        have hcoeffGroup : (s.g i.val i.val).im - b * (z.im : ℂ) -
            star b * (z.im : ℂ) +
              (Complex.normSq b : ℂ) * (s.q x : ℂ) -
                (↑(s.p x * (t * Complex.normSq z / Complex.normSq d)) : ℂ) =
            (s.g i.val i.val).im - b * (z.im : ℂ) - star b * (z.im : ℂ) +
              ((Complex.normSq b : ℂ) * (s.q x : ℂ) -
                (↑(s.p x * (t * Complex.normSq z / Complex.normSq d)) : ℂ)) := by ring
        rw [hcoeffGroup, hcoeffC]
        rw [hgii, Complex.sub_im]
        have hgroup : (s.g i.val i.val).im - b * (z.im : ℂ) -
            star b * (z.im : ℂ) = (s.g i.val i.val).im +
              (-b * (z.im : ℂ) - star b * (z.im : ℂ)) := by ring
        rw [hgroup, hcross']
        push_cast
        dsimp [b]
        have hfinal : (s.g i.val i.val).im +
            (-2 * (a * z).re * z.im) + (-a.im * Complex.normSq z) =
              (s.g i.val i.val).im - (a * z ^ 2).im := by
          calc
            (s.g i.val i.val).im + (-2 * (a * z).re * z.im) +
                (-a.im * Complex.normSq z) =
              (s.g i.val i.val).im +
                (-2 * (a * z).re * z.im - a.im * Complex.normSq z) := by ring
            _ = (s.g i.val i.val).im - (a * z ^ 2).im := by
              simpa [sub_eq_add_neg] using congrArg
                (fun q : ℝ => (s.g i.val i.val).im + q) (im_mul_sq a z)
        exact_mod_cast hfinal
  exact Complex.ofReal_injective hrowC

lemma delete_D_row_sum {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (x : P) (ξ : ℝ) (ht : 0 < t)
    (hsym : s.g.IsSymm) (hw : s.ward t)
    (hden : 1 + ((ξ : ℂ) + t * s.r x) * s.g x x ≠ 0)
    (hupdate : ∀ i j : survivors x,
      (deleteState t s x ξ).h t i j =
        s.h t i.val j.val - gamma t s x ξ * s.h t i.val x * s.h t x j.val)
    (i : survivors x) :
    (∑ j : survivors x, (deleteState t s x ξ).D t i j) = 0 := by
  classical
  let s' := deleteState t s x ξ
  simp_rw [D_entry]
  rw [Finset.sum_sub_distrib]
  have hdiag : (∑ j : survivors x,
      if i = j then s'.p i * s'.q i else 0) = s'.p i * s'.q i := by
    simp
  rw [hdiag]
  have hfactor : (∑ j : survivors x, s'.p i * s'.F t i j * s'.p j) =
      s'.p i * (∑ j : survivors x, s'.F t i j * s'.p j) := by
    calc
      (∑ j : survivors x, (s'.p i * s'.F t i j) * s'.p j) =
          ∑ j : survivors x, s'.p i * (s'.F t i j * s'.p j) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = s'.p i * (∑ j : survivors x, s'.F t i j * s'.p j) := by
        rw [← Finset.mul_sum]
  have hrow := delete_diag_ward_row t s x ξ ht hsym hw hden hupdate i
  have hrow' : (∑ j : survivors x, s'.F t i j * s'.p j) = s'.q i := by
    simpa [s', deleteState, State.F, entryAbsSquare, State.p, mul_comm] using hrow
  calc
    s'.p i * s'.q i - (∑ j : survivors x, s'.p i * s'.F t i j * s'.p j) = 0 := by
      rw [hfactor, hrow']
      ring

lemma delete_D_offdiag {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (x : P) (ξ : ℝ) (ht : 0 < t)
    (hsym : s.g.IsSymm) (hw : s.ward t)
    (hden : 1 + ((ξ : ℂ) + t * s.r x) * s.g x x ≠ 0)
    (hpivot : 0 < s.q x - s.p x * s.F t x x)
    (hupdate : ∀ i j : survivors x,
      (deleteState t s x ξ).h t i j =
        s.h t i.val j.val - gamma t s x ξ * s.h t i.val x * s.h t x j.val)
    (i j : survivors x) (hij : i ≠ j) :
    (deleteState t s x ξ).D t i j =
      (scalarSchur (s.D t) x + restrict (Linc t s x ξ) (survivors x)) i j := by
  classical
  let s' := deleteState t s x ξ
  let A : ℂ := s.h t i.val j.val
  let B : ℂ := gamma t s x ξ * s.h t i.val x * s.h t x j.val
  have hDij : s.D t i.val j.val =
      -(s.p i.val * s.p j.val * s.F t i.val j.val) := by
    rw [D_entry]
    simp [hij]
    ring
  have hDix : s.D t i.val x =
      -(s.p i.val * s.p x * s.F t i.val x) := by
    have hi : i.val ≠ x := Finset.mem_erase.mp i.property |>.1
    rw [D_entry]
    simp [hi]
    ring
  have hDxj : s.D t x j.val =
      -(s.p x * s.p j.val * s.F t x j.val) := by
    have hj : j.val ≠ x := Finset.mem_erase.mp j.property |>.1
    rw [D_entry]
    simp [Ne.symm hj] <;> ring
  have hDxx : s.D t x x = s.p x * (s.q x - s.p x * s.F t x x) := by
    rw [D_entry]
    simp
    ring
  have hDprod : s.D t i.val x * (s.D t x x)⁻¹ * s.D t x j.val =
      s.p i.val * s.p j.val * (s.p x / (s.q x - s.p x * s.F t x x)) *
        s.F t i.val x * s.F t x j.val := by
    by_cases hpx : s.p x = 0
    · rw [hDix, hDxx, hDxj]
      simp [hpx]
    · rw [hDix, hDxx, hDxj]
      have hpiv : s.q x - s.p x * s.F t x x ≠ 0 := ne_of_gt hpivot
      field_simp [hpx, hpiv]
      <;> ring
  have hDnew : s'.D t i j =
      -(s.p i.val * s.p j.val * Complex.normSq (A - B)) := by
    rw [D_entry]
    simp only [if_neg hij, sub_zero]
    have hpi : s'.p i = s.p i.val := rfl
    have hpj : s'.p j = s.p j.val := rfl
    have hF : s'.F t i j = ‖s'.h t i j‖ ^ 2 := rfl
    have hentry : s'.h t i j = A - B := by
      rw [hupdate i j]
    rw [hpi, hpj, hF, hentry, ← Complex.normSq_eq_norm_sq]
    dsimp [A, B]
    ring
  have hFij : s.F t i.val j.val = Complex.normSq A := by
    simp [A, State.F, entryAbsSquare, Complex.normSq_eq_norm_sq]
  have hFix : s.F t i.val x = Complex.normSq (s.h t i.val x) := by
    simp [State.F, entryAbsSquare, Complex.normSq_eq_norm_sq]
  have hFxj : s.F t x j.val = Complex.normSq (s.h t x j.val) := by
    simp [State.F, entryAbsSquare, Complex.normSq_eq_norm_sq]
  have hBnorm : Complex.normSq B =
      Complex.normSq (gamma t s x ξ) * s.F t i.val x * s.F t x j.val := by
    dsimp [B]
    rw [Complex.normSq_mul, Complex.normSq_mul, hFix, hFxj]
  have hcross : (B * star A).re =
      (gamma t s x ξ * star A * s.h t i.val x * s.h t x j.val).re := by
    dsimp [A, B]
    ring
  have hLedge : Ledge t s x ξ i j =
      s.p i.val * s.p j.val *
        (-2 * (B * star A).re +
          (Complex.normSq (gamma t s x ξ) -
            s.p x / (s.q x - s.p x * s.F t x x)) *
            s.F t i.val x * s.F t x j.val) := by
    simp only [Ledge]
    rw [← hcross, hFix, hFxj, ← Complex.normSq_eq_norm_sq]
  have hR :
      (scalarSchur (s.D t) x + restrict (Linc t s x ξ) (survivors x)) i j =
        s.D t i.val j.val - s.D t i.val x * (s.D t x x)⁻¹ * s.D t x j.val -
          Ledge t s x ξ i j := by
    simp [scalarSchur, restrict, Linc, pad, laplacian, hij] <;> ring
  rw [hDnew, hR, hDij, hDprod, hLedge, hFij]
  rw [normSq_sub_update, hBnorm]
  rw [show star A = (starRingEnd ℂ) A by rfl]
  ring

private lemma laplacian_row_sum {P : Type*} [Fintype P] [DecidableEq P]
    (c : RMat P) (i : P) : (∑ j, laplacian c i j) = 0 := by
  classical
  have hdiag : laplacian c i i = ∑ k, if k = i then 0 else c i k := by
    simp [laplacian]
  have hoff {j : P} (hj : j ≠ i) : laplacian c i j = -c i j := by
    simp [laplacian, hj, Ne.symm hj]
  have hIf : (∑ k, if k = i then 0 else c i k) =
      (∑ k, c i k) - c i i := by
    calc
      (∑ k, if k = i then 0 else c i k) =
          ∑ k, (c i k - (if k = i then c i k else 0)) := by
            apply Finset.sum_congr rfl
            intro k hk
            by_cases hki : k = i <;> simp [hki]
      _ = (∑ k, c i k) - c i i := by
        rw [Finset.sum_sub_distrib]
        simp
  have hErase : (∑ j ∈ (Finset.univ.erase i), c i j) =
      (∑ j, c i j) - c i i := by
    have h := Finset.sum_erase_add (Finset.univ) (fun j => c i j) (Finset.mem_univ i)
    linarith
  have hrest :
      (∑ j ∈ (Finset.univ.erase i), laplacian c i j) =
        -(∑ k, if k = i then 0 else c i k) := by
    calc
      (∑ j ∈ (Finset.univ.erase i), laplacian c i j) =
          ∑ j ∈ (Finset.univ.erase i), -c i j := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hoff (Finset.mem_erase.mp hj).1]
      _ = -(∑ j ∈ (Finset.univ.erase i), c i j) := by simp
      _ = -(∑ k, if k = i then 0 else c i k) := by rw [hErase, hIf]
  rw [← Finset.sum_erase_add (Finset.univ) (fun j => laplacian c i j)
    (Finset.mem_univ i), hrest, hdiag]
  ring

private lemma Linc_row_sum {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (x : P) (ξ : ℝ) (i : survivors x) :
    (∑ j : survivors x, restrict (Linc t s x ξ) (survivors x) i j) = 0 := by
  simpa [Linc, restrict, pad] using laplacian_row_sum (Ledge t s x ξ) i

lemma scalarSchur_D_row_sum {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (x : P) (hw : s.ward t)
    (hpivot : 0 < s.q x - s.p x * s.F t x x) (i : survivors x) :
    (∑ j : survivors x, scalarSchur (s.D t) x i j) = 0 := by
  classical
  have hrowi : (∑ j : survivors x, s.D t i.val j.val) = -s.D t i.val x := by
    have h := sum_survivors_sub x (fun k => s.D t i.val k)
    rw [D_row_sum t s hw i.val] at h
    simpa using h
  have hrowx : (∑ j : survivors x, s.D t x j.val) = -s.D t x x := by
    have h := sum_survivors_sub x (fun k => s.D t x k)
    rw [D_row_sum t s hw x] at h
    simpa using h
  have hfactor :
      (∑ j : survivors x, s.D t i.val x * (s.D t x x)⁻¹ * s.D t x j.val) =
        s.D t i.val x * (s.D t x x)⁻¹ * (∑ j : survivors x, s.D t x j.val) := by
    rw [← Finset.mul_sum]
  have hDix : s.D t i.val x = -(s.p i.val * s.p x * s.F t i.val x) := by
    have hi : i.val ≠ x := Finset.mem_erase.mp i.property |>.1
    rw [D_entry]
    simp [hi]
    ring
  simp only [scalarSchur]
  rw [Finset.sum_sub_distrib]
  rw [hfactor, hrowi, hrowx]
  by_cases hpx : s.p x = 0
  · have hzero : s.D t i.val x = 0 := by rw [hDix, hpx]; simp
    rw [hzero]
    ring
  · have hDxxne : s.D t x x ≠ 0 := by
      rw [D_entry]
      simp
      have hfac : s.p x * s.q x - s.p x * s.F t x x * s.p x =
          s.p x * (s.q x - s.p x * s.F t x x) := by ring
      rw [hfac]
      exact mul_ne_zero hpx (ne_of_gt hpivot)
    have hinv : (s.D t x x)⁻¹ * s.D t x x = 1 := inv_mul_cancel₀ hDxxne
    calc
      -s.D t i.val x -
          s.D t i.val x * (s.D t x x)⁻¹ * (-s.D t x x) =
        -s.D t i.val x + s.D t i.val x *
          ((s.D t x x)⁻¹ * s.D t x x) := by ring
      _ = 0 := by rw [hinv]; ring

theorem single_deletion_proof {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (x : P) (ξ : ℝ) (ht : 0 < t)
    (hsym : s.g.IsSymm) (hw : s.ward t)
    (hden : 1 + ((ξ : ℂ) + t * s.r x) * s.g x x ≠ 0)
    (ha : 1 - s.K t x x ≠ 0) (hpivot : 0 < s.q x - s.p x * s.F t x x) :
    let s' := deleteState t s x ξ
    (∀ i j, s'.h t i j = s.h t i j - gamma t s x ξ * s.h t i x * s.h t x j) ∧
    1 - s'.K t = scalarSchur (1 - s.K t) x - restrict (Jinc t s x ξ) (survivors x) ∧
    s'.D t = scalarSchur (s.D t) x + restrict (Linc t s x ξ) (survivors x) := by
  classical
  dsimp only
  let s' := deleteState t s x ξ
  have hsqrt_pos : (Real.sqrt t : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 ht))
  have hsqrt_sq : (Real.sqrt t : ℂ) * (Real.sqrt t : ℂ) = (t : ℂ) := by
    have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt (le_of_lt ht)
    push_cast
    simpa [pow_two] using congrArg (fun z : ℝ => (z : ℂ)) hsq
  have hupdate : ∀ i j : survivors x,
      s'.h t i j = s.h t i.val j.val -
        gamma t s x ξ * s.h t i.val x * s.h t x j.val := by
    intro i j
    change (Real.sqrt t : ℂ) *
        (s.g i.val j.val - ((ξ : ℂ) + t * s.r x) * s.g i.val x * s.g x j.val /
          (1 + ((ξ : ℂ) + t * s.r x) * s.g x x)) =
      (Real.sqrt t : ℂ) * s.g i.val j.val -
        (((ξ : ℂ) + t * s.r x) /
          ((Real.sqrt t : ℂ) * (1 + ((ξ : ℂ) + t * s.r x) * s.g x x))) *
          ((Real.sqrt t : ℂ) * s.g i.val x) * ((Real.sqrt t : ℂ) * s.g x j.val)
    field_simp [hden, hsqrt_pos]
  constructor
  · intro i j
    exact hupdate i j
  · constructor
    · ext i j
      have hi : i.val ≠ x := Finset.mem_erase.mp i.property |>.1
      have hj : j.val ≠ x := Finset.mem_erase.mp j.property |>.1
      change (((1 : CMat (survivors x)) - s'.K t) i j) =
        (((scalarSchur (1 - s.K t) x : CMat (survivors x)) -
          (restrict (Jinc t s x ξ) (survivors x) : CMat (survivors x))) i j)
      simp [scalarSchur, restrict, Jinc, pad, State.K,
        AndersonAC.Blueprint.entrywiseSquare, hupdate i j,
        Matrix.one_apply, hi, Ne.symm hj] <;>
        field_simp [ha] <;> ring
    · ext i j
      change s'.D t i j =
        (scalarSchur (s.D t) x + restrict (Linc t s x ξ) (survivors x)) i j
      by_cases hij : i = j
      · subst j
        have hnewrow := delete_D_row_sum t s x ξ ht hsym hw hden hupdate i
        have hschurrow := scalarSchur_D_row_sum t s x hw hpivot i
        have hLrow := Linc_row_sum t s x ξ i
        have hrightrow :
            (∑ k : survivors x,
              (scalarSchur (s.D t) x + restrict (Linc t s x ξ) (survivors x)) i k) = 0 := by
          simp only [Matrix.add_apply]
          rw [Finset.sum_add_distrib, hschurrow, hLrow]
          ring
        have hErase :
            (∑ k ∈ (Finset.univ.erase i), s'.D t i k) =
              (∑ k ∈ (Finset.univ.erase i),
                (scalarSchur (s.D t) x + restrict (Linc t s x ξ)
                  (survivors x)) i k) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact delete_D_offdiag t s x ξ ht hsym hw hden hpivot hupdate i k
            ((Finset.mem_erase.mp hk).1).symm
        have hnewdec :
            (∑ k ∈ (Finset.univ.erase i), s'.D t i k) + s'.D t i i =
              ∑ k : survivors x, s'.D t i k := by
          simpa using (Finset.sum_erase_add (Finset.univ : Finset (survivors x))
            (fun k => s'.D t i k) (Finset.mem_univ i))
        have hschurdec :
            (∑ k ∈ (Finset.univ.erase i),
              (scalarSchur (s.D t) x + restrict (Linc t s x ξ) (survivors x)) i k) +
                (scalarSchur (s.D t) x + restrict (Linc t s x ξ) (survivors x)) i i =
              ∑ k : survivors x,
                (scalarSchur (s.D t) x + restrict (Linc t s x ξ) (survivors x)) i k := by
          simpa using (Finset.sum_erase_add (Finset.univ : Finset (survivors x))
            (fun k => (scalarSchur (s.D t) x + restrict (Linc t s x ξ)
              (survivors x)) i k) (Finset.mem_univ i))
        rw [hnewrow] at hnewdec
        rw [hrightrow] at hschurdec
        rw [hErase] at hnewdec
        linarith
      · exact delete_D_offdiag t s x ξ ht hsym hw hden hpivot hupdate i j hij

end AndersonAC.AgentS45
