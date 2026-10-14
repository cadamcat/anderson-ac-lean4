import AndersonAC.S45.Definitions

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder

namespace AndersonAC.AgentS45

open AndersonAC.S45

variable {P I : Type*} [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]

theorem port_Q_isometry (v : PortMap P I) (hmass : ∀ i, v.mass i = 1) :
    v.Qᴴ * v.Q = 1 := by
  classical
  ext i j
  simp only [Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    have hterm (x : P) :
        star (if v.site x = i then (v.weight x ^ 2 : ℝ) else 0 : ℂ) *
          (if v.site x = i then (v.weight x ^ 2 : ℝ) else 0 : ℂ) =
        (if v.site x = i then (v.weight x ^ 4 : ℝ) else 0 : ℂ) := by
      by_cases hx : v.site x = i <;> simp [PortMap.Q, hx] <;> ring
    calc
      (∑ x, star (v.Q x i) * v.Q x i) =
          ∑ x, (if v.site x = i then (v.weight x ^ 4 : ℝ) else 0 : ℂ) := by
            apply Finset.sum_congr rfl
            intro x hx
            simpa only [PortMap.Q] using hterm x
      _ = (v.mass i : ℂ) := by
            rw [PortMap.mass]
            calc
              (∑ x, if v.site x = i then (v.weight x ^ 4 : ℝ) else 0 : ℂ) =
                  ∑ x, ((if v.site x = i then v.weight x ^ 4 else 0 : ℝ) : ℂ) := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    by_cases h : v.site x = i <;> simp [h]
              _ = (∑ x, if v.site x = i then v.weight x ^ 4 else 0 : ℝ) := by
                    exact (Complex.ofReal_sum (s := Finset.univ)
                      (fun x => if v.site x = i then v.weight x ^ 4 else 0)).symm
      _ = 1 := by simpa using congrArg (fun z : ℝ => (z : ℂ)) (hmass i)
  · simp only [hij, if_false]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hxi : v.site x = i
    · have hxj : v.site x ≠ j := by
        intro h
        exact hij (hxi.symm.trans h)
      change star (if v.site x = i then (v.weight x ^ 2 : ℝ) else 0 : ℂ) *
        (if v.site x = j then (v.weight x ^ 2 : ℝ) else 0 : ℂ) = 0
      simp [hxi, hxj, hij]
    · change star (if v.site x = i then (v.weight x ^ 2 : ℝ) else 0 : ℂ) *
        (if v.site x = j then (v.weight x ^ 2 : ℝ) else 0 : ℂ) = 0
      simp [hxi]

theorem sum_weight_fourth_site (v : PortMap P I) (b : I → ℝ) :
    (∑ x, v.weight x ^ 4 * b (v.site x)) = ∑ i, v.mass i * b i := by
  classical
  calc
    (∑ x, v.weight x ^ 4 * b (v.site x)) =
        ∑ x, ∑ i, if v.site x = i then v.weight x ^ 4 * b i else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [← eq_comm]
    _ = ∑ i, ∑ x, if v.site x = i then v.weight x ^ 4 * b i else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ i, v.mass i * b i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [PortMap.mass]
          calc
            (∑ x, if v.site x = i then v.weight x ^ 4 * b i else 0) =
                ∑ x, (if v.site x = i then v.weight x ^ 4 else 0) * b i := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  by_cases h : v.site x = i <;> simp [h]
            _ = (∑ x, if v.site x = i then v.weight x ^ 4 else 0) * b i := by
                  exact (Finset.sum_mul Finset.univ
                    (fun x => if v.site x = i then v.weight x ^ 4 else 0) (b i)).symm

theorem sum_portwise_site (v : PortMap P I) (a : P → ℝ) (b : I → ℝ) :
    (∑ x, a x * b (v.site x)) =
      ∑ i, (∑ x, if v.site x = i then a x else 0) * b i := by
  classical
  calc
    (∑ x, a x * b (v.site x)) =
        ∑ x, ∑ i, if v.site x = i then a x * b i else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [← eq_comm]
    _ = ∑ i, ∑ x, if v.site x = i then a x * b i else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ i, (∑ x, if v.site x = i then a x else 0) * b i := by
          apply Finset.sum_congr rfl
          intro i hi
          calc
            (∑ x, if v.site x = i then a x * b i else 0) =
                ∑ x, (if v.site x = i then a x else 0) * b i := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  by_cases h : v.site x = i <;> simp [h]
            _ = (∑ x, if v.site x = i then a x else 0) * b i :=
                  (Finset.sum_mul Finset.univ
                    (fun x => if v.site x = i then a x else 0) (b i)).symm

theorem lift_p_entry (v : PortMap P I) (s : State I) (x : P) :
    (v.liftState s).p x = v.weight x ^ 2 * s.p (v.site x) := by
  simp only [State.p, PortMap.liftState]
  rw [← Complex.ofReal_pow, Complex.im_ofReal_mul]

theorem lift_q_entry (v : PortMap P I) (s : State I) (x : P) :
    (v.liftState s).q x = v.weight x ^ 2 * s.q (v.site x) := by
  simp only [State.q, PortMap.liftState]
  rw [← Complex.ofReal_mul, Complex.im_ofReal_mul]
  ring

theorem state_D_entry (s : State I) (t : ℝ) (i j : I) :
    s.D t i j = (if i = j then s.p i * s.q i else 0) -
      s.p i * s.F t i j * s.p j := by
  simp [State.D, Matrix.mul_apply, Matrix.diagonal]

theorem qform_state_expansion (s : State I) (t : ℝ) (f : I → ℝ) :
    qform (s.D t) f =
      (∑ i, s.p i * s.q i * f i ^ 2) -
        ∑ i, ∑ j, s.p i * s.p j * s.F t i j * f i * f j := by
  classical
  calc
    qform (s.D t) f =
        ∑ i, f i * (s.p i * s.q i * f i -
          ∑ j, s.p i * s.F t i j * s.p j * f j) := by
            calc
              qform (s.D t) f = ∑ i, f i * (∑ j, s.D t i j * f j) := by
                simp [qform, Matrix.mulVec, dotProduct]
              _ = _ := by
                apply Finset.sum_congr rfl
                intro i hi
                simp [state_D_entry, sub_mul, Finset.sum_sub_distrib,
                  Finset.sum_ite_eq', eq_comm]
    _ = (∑ i, f i * (s.p i * s.q i * f i)) -
          ∑ i, f i * (∑ j, s.p i * s.F t i j * s.p j * f j) := by
            calc
              (∑ i, f i * (s.p i * s.q i * f i -
                ∑ j, s.p i * s.F t i j * s.p j * f j)) =
                  ∑ i, (f i * (s.p i * s.q i * f i) -
                    f i * (∑ j, s.p i * s.F t i j * s.p j * f j)) := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      ring
              _ = _ := by rw [Finset.sum_sub_distrib]
    _ = (∑ i, s.p i * s.q i * f i ^ 2) -
          ∑ i, ∑ j, s.p i * s.p j * s.F t i j * f i * f j := by
            congr 1
            · apply Finset.sum_congr rfl
              intro i hi
              ring
            · apply Finset.sum_congr rfl
              intro i hi
              calc
                f i * (∑ j, s.p i * s.F t i j * s.p j * f j) =
                    ∑ j, f i * (s.p i * s.F t i j * s.p j * f j) :=
                      Finset.mul_sum Finset.univ
                        (fun j => s.p i * s.F t i j * s.p j * f j) (f i)
                _ = ∑ j, s.p i * s.p j * s.F t i j * f i * f j := by
                      apply Finset.sum_congr rfl
                      intro j hj
                      ring

theorem qform_sub_formula (D : RMat I) (hD : D.IsSymm) (f z : I → ℝ) :
    qform D (f - z) = qform D f + qform D z -
      2 * (∑ i, f i * (D *ᵥ z) i) := by
  change dotProduct (f - z) (D *ᵥ (f - z)) =
    dotProduct f (D *ᵥ f) + dotProduct z (D *ᵥ z) -
      2 * dotProduct f (D *ᵥ z)
  rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub]
  rw [hD.dotProduct_mulVec_comm (x := z) (y := f)]
  simp only [dotProduct]
  ring

theorem dualForm_eq_of_solve (D : RMat I) (hD : D.IsSymm)
    (hpos : ∀ f, 0 ≤ qform D f) (y z : I → ℝ) (hsolve : D *ᵥ z = y) :
    dualForm (qform D) y = ∑ i, y i * z i := by
  classical
  have hz : qform D z = ∑ i, z i * y i := by
    simp [qform, hsolve]
  have hcomm (a b : I → ℝ) :
      (∑ i, a i * b i) = ∑ i, b i * a i := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hobj (f : I → ℝ) :
      2 * (∑ i, y i * f i) - qform D f =
        (∑ i, y i * z i) - qform D (f - z) := by
    have hsub := qform_sub_formula D hD f z
    rw [hsolve] at hsub
    rw [hz] at hsub
    calc
      2 * (∑ i, y i * f i) - qform D f =
          (∑ i, z i * y i) - qform D (f - z) := by
            rw [hsub]
            calc
              2 * (∑ i, y i * f i) - qform D f =
                  2 * (∑ i, f i * y i) - qform D f := by rw [hcomm y f]
              _ = -qform D f + (∑ i, f i * y i) * 2 := by ring
              _ = (∑ i, z i * y i) -
                    (qform D f + ∑ i, z i * y i - 2 * ∑ i, f i * y i) := by ring
      _ = (∑ i, y i * z i) - qform D (f - z) := by
            rw [hcomm z y]
  unfold dualForm
  apply le_antisymm
  · apply csSup_le
    · refine ⟨∑ i, y i * z i, ?_⟩
      refine ⟨z, ?_⟩
      rw [hz, hcomm z y]
      ring
    · intro a ha
      rcases ha with ⟨f, rfl⟩
      rw [hobj]
      linarith [hpos (f - z)]
  · apply le_csSup
    · refine ⟨∑ i, y i * z i, ?_⟩
      intro a ha
      rcases ha with ⟨f, rfl⟩
      rw [hobj]
      linarith [hpos (f - z)]
    · refine ⟨z, ?_⟩
      rw [hz]
      rw [hcomm z y]
      ring

set_option maxHeartbeats 1000000 in
theorem exists_solution_constantKernel {D : RMat I} (hD : constantKernel D)
    (y : I → ℝ) (hy : neutral y) [Nonempty I] :
    ∃ z, D *ᵥ z = y ∧ neutral z := by
  classical
  let J : RMat I := fun _ _ => 1
  let A : RMat I := D + J
  have hDherm : D.IsHermitian := by
    rw [Matrix.isHermitian_iff_isSymm]
    exact hD.1
  have hDpsd : D.PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hDherm
    intro f
    simpa [qform, dotProduct, Matrix.mulVec] using hD.2.1 f
  have hJsymm : J.IsSymm := by
    ext i j
    rfl
  have hAsymm : A.IsSymm := by
    exact hD.1.add hJsymm
  have hAherm : A.IsHermitian := by
    rw [Matrix.isHermitian_iff_isSymm]
    exact hAsymm
  have hJq (f : I → ℝ) : qform J f = (∑ i, f i) ^ 2 := by
    calc
      qform J f = (∑ i, f i) * (∑ i, f i) := by
        simp [qform, Matrix.mulVec, Matrix.mul_apply, dotProduct, J]
        exact (Finset.sum_mul Finset.univ f (∑ i, f i)).symm
      _ = _ := by ring
  have hAform (f : I → ℝ) :
      dotProduct f (A *ᵥ f) = qform D f + (∑ i, f i) ^ 2 := by
    calc
      dotProduct f (A *ᵥ f) = qform A f := by simp [qform, dotProduct]
      _ = qform D f + qform J f := by
        change (∑ i ∈ Finset.univ, f i * ((D + J) *ᵥ f) i) =
          (∑ i ∈ Finset.univ, f i * (D *ᵥ f) i) +
            ∑ i ∈ Finset.univ, f i * (J *ᵥ f) i
        simp only [add_mulVec, Pi.add_apply, mul_add]
        rw [Finset.sum_add_distrib]
      _ = qform D f + (∑ i, f i) ^ 2 := by rw [hJq]
  have hcardNat : 0 < Fintype.card I := Fintype.card_pos_iff.mpr inferInstance
  have hcard : (0 : ℝ) < (Fintype.card I : ℝ) := by exact_mod_cast hcardNat
  have hApos : A.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hAherm
    intro f hf
    have hAform' : star f ⬝ᵥ A *ᵥ f = qform D f + (∑ i, f i) ^ 2 := by
      simpa [dotProduct] using hAform f
    rw [hAform']
    by_cases hsum : ∑ i, f i = 0
    · have hqne : qform D f ≠ 0 := by
        intro hqzero
        obtain ⟨a, ha⟩ := (hD.2.2 f).mp hqzero
        have hfconst : f = fun _ => a := funext ha
        have hsumA : (∑ i, f i) = (Fintype.card I : ℝ) * a := by
          simp [hfconst]
        have ha0 : a = 0 := by nlinarith [hsum, hsumA, hcard]
        apply hf
        ext i
        rw [hfconst]
        simp [ha0]
      have hqpos : 0 < qform D f :=
        lt_of_le_of_ne (hD.2.1 f) (Ne.symm hqne)
      nlinarith
    · have hsquare : 0 < (∑ i, f i) ^ 2 := sq_pos_of_ne_zero hsum
      nlinarith [hD.2.1 f, hsquare]
  have hAunit : IsUnit A := hApos.isUnit
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hAunit
  let z : I → ℝ := A⁻¹ *ᵥ y
  have hAz : A *ᵥ z = y := by
    dsimp [z]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet]
    simp
  have hDones : D *ᵥ (fun _ => 1) = 0 := by
    apply hDpsd.dotProduct_mulVec_zero_iff.mp
    have hone : qform D (fun _ => 1) = 0 := by
      apply (hD.2.2 _).2
      exact ⟨1, fun _ => rfl⟩
    change qform D (fun _ => 1) = 0
    exact hone
  have hDcol (j : I) : (∑ i, D i j) = 0 := by
    calc
      (∑ i, D i j) = ∑ i, D j i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hij := congrFun (congrFun hD.1.eq i) j
        simpa using hij.symm
      _ = (D *ᵥ (fun _ => 1)) j := by
        change (∑ i, D j i) = (∑ i, D j i * (1 : ℝ))
        simp
      _ = 0 := by simpa using congrFun hDones j
  have hDsum : (∑ i, (D *ᵥ z) i) = 0 := by
    calc
      (∑ i, (D *ᵥ z) i) = ∑ i, ∑ j, D i j * z j := by
        simp [Matrix.mulVec, dotProduct]
      _ = ∑ j, ∑ i, D i j * z j := by rw [Finset.sum_comm]
      _ = ∑ j, (∑ i, D i j) * z j := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (Finset.sum_mul Finset.univ (fun i => D i j) (z j)).symm
      _ = 0 := by simp [hDcol]
  have hJmul (i : I) : (J *ᵥ z) i = ∑ j, z j := by
    change dotProduct (fun _ : I => (1 : ℝ)) z = ∑ j, z j
    simp [dotProduct]
  have hAeq : A *ᵥ z = D *ᵥ z + (fun _ => ∑ j, z j) := by
    calc
      A *ᵥ z = D *ᵥ z + J *ᵥ z := by dsimp [A]; rw [add_mulVec]
      _ = D *ᵥ z + (fun _ => ∑ j, z j) := by
            congr 1
            funext i
            exact hJmul i
  have hAsum : (∑ i, (A *ᵥ z) i) =
      (Fintype.card I : ℝ) * (∑ j, z j) := by
    calc
      (∑ i, (A *ᵥ z) i) =
          (∑ i, (D *ᵥ z) i) + ∑ i, (∑ j, z j) := by
            rw [hAeq]
            change (Finset.univ : Finset I).sum (fun i : I =>
                (D *ᵥ z) i + ∑ j, z j) =
              (Finset.univ : Finset I).sum (fun i : I => (D *ᵥ z) i) +
                (Finset.univ : Finset I).sum (fun i : I => ∑ j, z j)
            rw [Finset.sum_add_distrib]
      _ = (Fintype.card I : ℝ) * (∑ j, z j) := by
            simp [hDsum, Finset.sum_const, nsmul_eq_mul]
  have hsumz : (∑ j, z j) = 0 := by
    have hprod : (Fintype.card I : ℝ) * (∑ j, z j) = 0 := by
      calc
        _ = ∑ i, (A *ᵥ z) i := hAsum.symm
        _ = ∑ i, y i := by rw [hAz]
        _ = 0 := hy
    rcases mul_eq_zero.mp hprod with hcard0 | hsum0
    · exact False.elim ((ne_of_gt hcard) hcard0)
    · exact hsum0
  have hDz : D *ᵥ z = y := by
    rw [hAeq, hsumz] at hAz
    ext i
    simpa using congrFun hAz i
  exact ⟨z, hDz, hsumz⟩

theorem port_deviation_weighted_mean {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] (v : PortMap P I) (s : State I)
    (y : P → ℝ) (hmass : ∀ i, v.mass i = 1) (hk : ∀ x, 0 < v.weight x)
    (hp : ∀ i, 0 < s.p i) (i : I) :
    (∑ x, if v.site x = i then v.weight x ^ 4 *
      (y x / (s.p i ^ 2 * v.weight x ^ 4) - v.sumCharge y i / s.p i ^ 2) else 0) = 0 := by
  classical
  let c : P → ℝ := fun x =>
    y x / (s.p i ^ 2 * v.weight x ^ 4) - v.sumCharge y i / s.p i ^ 2
  have hp2 : s.p i ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos (hp i))
  have hw4 (x : P) : v.weight x ^ 4 ≠ 0 := ne_of_gt (pow_pos (hk x) 4)
  have hpoint (x : P) :
      v.weight x ^ 4 * c x =
        y x / s.p i ^ 2 - v.weight x ^ 4 * v.sumCharge y i / s.p i ^ 2 := by
    dsimp [c]
    field_simp [hp2, hw4 x]
    have hnum : v.weight x ^ 4 *
        (y x / v.weight x ^ 4 - v.sumCharge y i) =
          y x - v.weight x ^ 4 * v.sumCharge y i := by
      rw [div_eq_mul_inv]
      calc
        v.weight x ^ 4 *
            (y x * (v.weight x ^ 4)⁻¹ - v.sumCharge y i) =
          y x * (v.weight x ^ 4 * (v.weight x ^ 4)⁻¹) -
            v.weight x ^ 4 * v.sumCharge y i := by ring
        _ = y x - v.weight x ^ 4 * v.sumCharge y i := by
          rw [mul_inv_cancel₀ (hw4 x)]
          ring
    rw [hnum]
  have hYfiber : ∀ j, v.sumCharge y j = ∑ x, if v.site x = j then y x else 0 := by
    intro j
    rfl
  have hMfiber : ∀ j, (∑ x, if v.site x = j then v.weight x ^ 4 else 0) = v.mass j := by
    intro j
    rfl
  have hYdiv :
      (∑ x, if v.site x = i then y x / s.p i ^ 2 else 0) =
        v.sumCharge y i / s.p i ^ 2 := by
    calc
      _ = ∑ x, (if v.site x = i then y x else 0) * (1 / s.p i ^ 2) := by
            apply Finset.sum_congr rfl
            intro x hx
            by_cases h : v.site x = i <;> simp [h, div_eq_mul_inv]
      _ = (∑ x, if v.site x = i then y x else 0) * (1 / s.p i ^ 2) :=
            (Finset.sum_mul Finset.univ
              (fun x => if v.site x = i then y x else 0) (1 / s.p i ^ 2)).symm
      _ = v.sumCharge y i / s.p i ^ 2 := by rw [← hYfiber i]; ring
  have hMdiv :
      (∑ x, if v.site x = i then
        v.weight x ^ 4 * v.sumCharge y i / s.p i ^ 2 else 0) =
          v.mass i * (v.sumCharge y i / s.p i ^ 2) := by
    calc
      _ = ∑ x, (if v.site x = i then v.weight x ^ 4 else 0) *
          (v.sumCharge y i / s.p i ^ 2) := by
            apply Finset.sum_congr rfl
            intro x hx
            by_cases h : v.site x = i <;> simp [h, div_eq_mul_inv, mul_assoc]
      _ = (∑ x, if v.site x = i then v.weight x ^ 4 else 0) *
          (v.sumCharge y i / s.p i ^ 2) :=
            (Finset.sum_mul Finset.univ
              (fun x => if v.site x = i then v.weight x ^ 4 else 0)
              (v.sumCharge y i / s.p i ^ 2)).symm
      _ = v.mass i * (v.sumCharge y i / s.p i ^ 2) := by rw [hMfiber i]
  calc
    (∑ x, if v.site x = i then v.weight x ^ 4 * c x else 0) =
        (∑ x, if v.site x = i then y x / s.p i ^ 2 else 0) -
          ∑ x, if v.site x = i then
            v.weight x ^ 4 * v.sumCharge y i / s.p i ^ 2 else 0 := by
              calc
                _ = ∑ x, ((if v.site x = i then y x / s.p i ^ 2 else 0) -
                    (if v.site x = i then
                      v.weight x ^ 4 * v.sumCharge y i / s.p i ^ 2 else 0)) := by
                        apply Finset.sum_congr rfl
                        intro x hx
                        by_cases h : v.site x = i
                        · simpa [h] using hpoint x
                        · simp [h]
                _ = _ := by
                      change (Finset.univ : Finset P).sum (fun x =>
                          (if v.site x = i then y x / s.p i ^ 2 else 0) -
                            (if v.site x = i then
                              v.weight x ^ 4 * v.sumCharge y i / s.p i ^ 2 else 0)) =
                        (Finset.univ : Finset P).sum (fun x =>
                          if v.site x = i then y x / s.p i ^ 2 else 0) -
                        (Finset.univ : Finset P).sum (fun x =>
                          if v.site x = i then
                            v.weight x ^ 4 * v.sumCharge y i / s.p i ^ 2 else 0)
                      rw [Finset.sum_sub_distrib]
    _ = v.sumCharge y i / s.p i ^ 2 -
          v.mass i * (v.sumCharge y i / s.p i ^ 2) := by rw [hYdiv, hMdiv]
    _ = 0 := by rw [hmass i]; ring

theorem sumCharge_neutral {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] (v : PortMap P I) (y : P → ℝ)
    (hy : neutral y) : neutral (v.sumCharge y) := by
  classical
  unfold neutral PortMap.sumCharge
  calc
    (∑ i, ∑ x, if v.site x = i then y x else 0) =
        ∑ x, ∑ i, if v.site x = i then y x else 0 := by rw [Finset.sum_comm]
    _ = ∑ x, y x := by
        apply Finset.sum_congr rfl
        intro x hx
        simp
    _ = 0 := hy

theorem lift_h_entry (v : PortMap P I) (s : State I) (t : ℝ) (x y : P) :
    (v.liftState s).h t x y =
      (v.weight x : ℂ) * (v.weight y : ℂ) * s.h t (v.site x) (v.site y) := by
  change (Real.sqrt t : ℂ) *
      ((v.weight x : ℂ) * (v.weight y : ℂ) * s.g (v.site x) (v.site y)) =
    (v.weight x : ℂ) * (v.weight y : ℂ) *
      ((Real.sqrt t : ℂ) * s.g (v.site x) (v.site y))
  ring

theorem lift_F_entry (v : PortMap P I) (s : State I) (t : ℝ) (x y : P) :
    (v.liftState s).F t x y =
      v.weight x ^ 2 * v.weight y ^ 2 * s.F t (v.site x) (v.site y) := by
  change ‖(v.liftState s).h t x y‖ ^ 2 =
    v.weight x ^ 2 * v.weight y ^ 2 * ‖s.h t (v.site x) (v.site y)‖ ^ 2
  rw [lift_h_entry, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]
  rw [mul_pow, mul_pow, sq_abs, sq_abs]

theorem lift_D_entry_scaled (v : PortMap P I) (s : State I) (t : ℝ)
    (hfix : ∀ i, s.g i i = s.r i) (x y : P) :
    (v.liftState s).D t x y =
      (if x = y then v.weight x ^ 4 * s.p (v.site x) ^ 2 else 0) +
        v.weight x ^ 4 * v.weight y ^ 4 *
          (s.D t (v.site x) (v.site y) -
            (if v.site x = v.site y then s.p (v.site x) ^ 2 else 0)) := by
  have hqp : ∀ i, s.q i = s.p i := by
    intro i
    simp [State.p, State.q, hfix i]
  simp_rw [state_D_entry, lift_p_entry, lift_q_entry, lift_F_entry, hqp]
  by_cases hxy : x = y
  · subst y
    simp
    ring
  · simp [hxy]
    ring

theorem lift_D_mulVec_of_centered (v : PortMap P I) (s : State I) (t : ℝ)
    (hmass : ∀ i, v.mass i = 1) (hfix : ∀ i, s.g i i = s.r i)
    (a : P → ℝ) (b : I → ℝ) (y : P → ℝ)
    (hamean : ∀ i,
      (∑ x, if v.site x = i then v.weight x ^ 4 * a x else 0) = 0)
    (hbase : s.D t *ᵥ b = v.sumCharge y)
    (hpoint : ∀ x, v.weight x ^ 4 *
      (s.p (v.site x) ^ 2 * a x + v.sumCharge y (v.site x)) = y x) :
    (v.liftState s).D t *ᵥ (fun x => b (v.site x) + a x) = y := by
  classical
  ext x
  let i := v.site x
  have hfiber (j : I) :
      (∑ z, if v.site z = j then
        v.weight z ^ 4 * (b (v.site z) + a z) else 0) = b j := by
    calc
      _ = (∑ z, if v.site z = j then v.weight z ^ 4 * b j else 0) +
          ∑ z, if v.site z = j then v.weight z ^ 4 * a z else 0 := by
            calc
              _ = ∑ z, ((if v.site z = j then v.weight z ^ 4 * b j else 0) +
                  (if v.site z = j then v.weight z ^ 4 * a z else 0)) := by
                    apply Finset.sum_congr rfl
                    intro z hz
                    by_cases h : v.site z = j <;> simp [h] <;> ring
              _ = _ := Finset.sum_add_distrib
      _ = v.mass j * b j + 0 := by
            rw [hamean j]
            have hmass' :
                (∑ z, if v.site z = j then v.weight z ^ 4 * b j else 0) =
                  v.mass j * b j := by
              calc
                _ = ∑ z, (if v.site z = j then v.weight z ^ 4 else 0) * b j := by
                      apply Finset.sum_congr rfl
                      intro z hz
                      by_cases h : v.site z = j <;> simp [h]
                _ = _ := by
                      rw [PortMap.mass]
                      exact (Finset.sum_mul Finset.univ
                        (fun z => if v.site z = j then v.weight z ^ 4 else 0)
                        (b j)).symm
            rw [hmass']
      _ = b j := by rw [hmass j]; ring
  have hdiag :
      (∑ z, (if x = z then v.weight x ^ 4 * s.p i ^ 2 else 0) *
        (b (v.site z) + a z)) =
        v.weight x ^ 4 * s.p i ^ 2 * (b i + a x) := by
    simp [Finset.sum_ite_eq', eq_comm, i]
  have houter :
      (∑ z, v.weight x ^ 4 * v.weight z ^ 4 *
        (s.D t i (v.site z) -
          (if i = v.site z then s.p i ^ 2 else 0)) *
        (b (v.site z) + a z)) =
        v.weight x ^ 4 * ((s.D t *ᵥ b) i - s.p i ^ 2 * b i) := by
    calc
      _ = ∑ z, v.weight x ^ 4 *
          ((v.weight z ^ 4 * (b (v.site z) + a z)) *
            (s.D t i (v.site z) -
              (if i = v.site z then s.p i ^ 2 else 0))) := by
              apply Finset.sum_congr rfl
              intro z hz
              ring
      _ = v.weight x ^ 4 *
          ∑ z, (v.weight z ^ 4 * (b (v.site z) + a z)) *
            (s.D t i (v.site z) -
              (if i = v.site z then s.p i ^ 2 else 0)) := by
              exact (Finset.mul_sum Finset.univ
                (fun z => (v.weight z ^ 4 * (b (v.site z) + a z)) *
                  (s.D t i (v.site z) -
                    (if i = v.site z then s.p i ^ 2 else 0)))
                (v.weight x ^ 4)).symm
      _ = v.weight x ^ 4 * ∑ j,
          (∑ z, if v.site z = j then
            v.weight z ^ 4 * (b (v.site z) + a z) else 0) *
            (s.D t i j - (if i = j then s.p i ^ 2 else 0)) := by
              congr 1
              exact sum_portwise_site v
                (fun z => v.weight z ^ 4 * (b (v.site z) + a z))
                (fun j => s.D t i j - (if i = j then s.p i ^ 2 else 0))
      _ = v.weight x ^ 4 * ∑ j,
          b j * (s.D t i j - (if i = j then s.p i ^ 2 else 0)) := by
              congr 1
              apply Finset.sum_congr rfl
              intro j hj
              rw [hfiber j]
      _ = v.weight x ^ 4 * ((s.D t *ᵥ b) i - s.p i ^ 2 * b i) := by
              congr 1
              calc
                (∑ j, b j * (s.D t i j -
                    (if i = j then s.p i ^ 2 else 0))) =
                    (∑ j, s.D t i j * b j) -
                      ∑ j, (if i = j then s.p i ^ 2 else 0) * b j := by
                        calc
                          _ = ∑ j, (s.D t i j * b j -
                              (if i = j then s.p i ^ 2 else 0) * b j) := by
                                apply Finset.sum_congr rfl
                                intro j hj
                                ring
                          _ = _ := by rw [Finset.sum_sub_distrib]
                _ = _ := by
                      simp [Matrix.mulVec, dotProduct, Finset.sum_ite_eq', eq_comm]
  have hrow :
      ((v.liftState s).D t *ᵥ (fun z => b (v.site z) + a z)) x =
        v.weight x ^ 4 * s.p i ^ 2 * (b i + a x) +
          v.weight x ^ 4 * ((s.D t *ᵥ b) i - s.p i ^ 2 * b i) := by
    change ∑ z, (v.liftState s).D t x z * (b (v.site z) + a z) = _
    calc
      _ = ∑ z, ((if x = z then v.weight x ^ 4 * s.p i ^ 2 else 0) +
          v.weight x ^ 4 * v.weight z ^ 4 *
            (s.D t i (v.site z) -
              (if i = v.site z then s.p i ^ 2 else 0))) *
            (b (v.site z) + a z) := by
              apply Finset.sum_congr rfl
              intro z hz
              rw [lift_D_entry_scaled v s t hfix]
      _ = _ := by
            simp_rw [add_mul]
            rw [Finset.sum_add_distrib, hdiag, houter]
  rw [hrow, hbase]
  change v.weight x ^ 4 * s.p (v.site x) ^ 2 *
      (b (v.site x) + a x) +
        v.weight x ^ 4 *
          (v.sumCharge y (v.site x) - s.p (v.site x) ^ 2 * b (v.site x)) = y x
  calc
    _ = v.weight x ^ 4 *
        (s.p (v.site x) ^ 2 * a x + v.sumCharge y (v.site x)) := by ring
    _ = y x := hpoint x

theorem weighted_site_variance (v : PortMap P I) (f : P → ℝ)
    (hmass : ∀ i, v.mass i = 1) (i : I) :
    (∑ x, if v.site x = i then v.weight x ^ 4 *
        (f x - v.average f i) ^ 2 else 0) =
      (∑ x, if v.site x = i then v.weight x ^ 4 * f x ^ 2 else 0) -
        (v.average f i) ^ 2 := by
  classical
  let a := v.average f i
  have ha : (∑ x, if v.site x = i then v.weight x ^ 4 * f x else 0) = a := rfl
  have hm : (∑ x, if v.site x = i then v.weight x ^ 4 else 0) = v.mass i := rfl
  have hexpand :
      (∑ x, if v.site x = i then v.weight x ^ 4 * (f x - a) ^ 2 else 0) =
        (∑ x, if v.site x = i then v.weight x ^ 4 * f x ^ 2 else 0) -
          2 * a * (∑ x, if v.site x = i then v.weight x ^ 4 * f x else 0) +
            a ^ 2 * (∑ x, if v.site x = i then v.weight x ^ 4 else 0) := by
    calc
      _ = ∑ x, ((if v.site x = i then v.weight x ^ 4 * f x ^ 2 else 0) -
          2 * a * (if v.site x = i then v.weight x ^ 4 * f x else 0) +
          a ^ 2 * (if v.site x = i then v.weight x ^ 4 else 0)) := by
            apply Finset.sum_congr rfl
            intro x hx
            by_cases h : v.site x = i
            · simp [h, a, pow_two]
              ring
            · simp [h]
      _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            rw [(Finset.mul_sum Finset.univ
              (fun x => if v.site x = i then v.weight x ^ 4 * f x else 0) (2 * a)).symm]
            rw [(Finset.mul_sum Finset.univ
              (fun x => if v.site x = i then v.weight x ^ 4 else 0) (a ^ 2)).symm]
  rw [hexpand, ha, hm, hmass i]
  dsimp [a]
  ring

theorem lift_qform_split (v : PortMap P I) (s : State I) (t : ℝ) (f : P → ℝ)
    (hmass : ∀ i, v.mass i = 1) (hfix : ∀ i, s.g i i = s.r i) :
    qform ((v.liftState s).D t) f =
      qform (s.D t) (v.average f) +
        ∑ x, s.p (v.site x) ^ 2 * v.weight x ^ 4 *
          (f x - v.average f (v.site x)) ^ 2 := by
  classical
  let avg := v.average f
  have hqp : ∀ i, s.q i = s.p i := by
    intro i
    simp [State.p, State.q, hfix i]
  have hdiag :
      (∑ x, (v.weight x ^ 4 * f x ^ 2) * s.p (v.site x) ^ 2) =
        ∑ i, (∑ x, if v.site x = i then v.weight x ^ 4 * f x ^ 2 else 0) *
          s.p i ^ 2 := by
    exact sum_portwise_site v (fun x => v.weight x ^ 4 * f x ^ 2)
      (fun i => s.p i ^ 2)
  have hinner (i : I) :
      (∑ y, (v.weight y ^ 4 * f y) *
        (s.p (v.site y) * s.F t i (v.site y))) =
        ∑ j, (∑ y, if v.site y = j then v.weight y ^ 4 * f y else 0) *
          (s.p j * s.F t i j) := by
    exact sum_portwise_site v (fun y => v.weight y ^ 4 * f y)
      (fun j => s.p j * s.F t i j)
  have hcrossGrouped :
      (∑ x, (v.weight x ^ 4 * f x) *
        (s.p (v.site x) *
          ∑ y, (v.weight y ^ 4 * f y) *
            (s.p (v.site y) * s.F t (v.site x) (v.site y)))) =
        ∑ i, avg i * (s.p i *
          ∑ j, avg j * (s.p j * s.F t i j)) := by
    calc
      _ = ∑ i, avg i * (s.p i *
          ∑ y, (v.weight y ^ 4 * f y) *
            (s.p (v.site y) * s.F t i (v.site y))) := by
              simpa [avg, PortMap.average] using
                (sum_portwise_site v (fun x => v.weight x ^ 4 * f x)
                  (fun i => s.p i *
                    ∑ y, (v.weight y ^ 4 * f y) *
                      (s.p (v.site y) * s.F t i (v.site y))))
      _ = ∑ i, avg i * (s.p i *
          ∑ j, avg j * (s.p j * s.F t i j)) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hinner i]
              simp [avg, PortMap.average]
  have hcrossFactor :
      (∑ i, avg i * (s.p i *
          ∑ j, avg j * (s.p j * s.F t i j))) =
        ∑ i, ∑ j, s.p i * s.p j * s.F t i j * avg i * avg j := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      avg i * (s.p i * ∑ j, avg j * (s.p j * s.F t i j)) =
          ∑ j, (avg i * s.p i) * (avg j * (s.p j * s.F t i j)) := by
            calc
              _ = (avg i * s.p i) * ∑ j, avg j * (s.p j * s.F t i j) := by ring
              _ = _ := Finset.mul_sum Finset.univ
                (fun j => avg j * (s.p j * s.F t i j)) (avg i * s.p i)
      _ = ∑ j, s.p i * s.p j * s.F t i j * avg i * avg j := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
  have hcrossLift :
      (∑ x, ∑ y, (v.liftState s).p x * (v.liftState s).p y *
        (v.liftState s).F t x y * f x * f y) =
        ∑ i, ∑ j, s.p i * s.p j * s.F t i j * avg i * avg j := by
    calc
      _ = ∑ x, ∑ y,
          (v.weight x ^ 4 * f x) * (v.weight y ^ 4 * f y) *
            (s.p (v.site x) * s.p (v.site y) *
              s.F t (v.site x) (v.site y)) := by
                simp_rw [lift_p_entry, lift_F_entry]
                apply Finset.sum_congr rfl
                intro x hx
                apply Finset.sum_congr rfl
                intro y hy
                ring
      _ = ∑ x, (v.weight x ^ 4 * f x) *
          (s.p (v.site x) *
            ∑ y, (v.weight y ^ 4 * f y) *
              (s.p (v.site y) * s.F t (v.site x) (v.site y))) := by
                apply Finset.sum_congr rfl
                intro x hx
                calc
                  _ = ∑ y, ((v.weight x ^ 4 * f x) * s.p (v.site x)) *
                      ((v.weight y ^ 4 * f y) *
                        (s.p (v.site y) * s.F t (v.site x) (v.site y))) := by
                          apply Finset.sum_congr rfl
                          intro y hy
                          ring
                  _ = _ := by
                        calc
                          _ = ((v.weight x ^ 4 * f x) * s.p (v.site x)) *
                              ∑ y, (v.weight y ^ 4 * f y) *
                                (s.p (v.site y) * s.F t (v.site x) (v.site y)) :=
                                  (Finset.mul_sum Finset.univ
                                    (fun y => (v.weight y ^ 4 * f y) *
                                      (s.p (v.site y) * s.F t (v.site x) (v.site y)))
                                    ((v.weight x ^ 4 * f x) * s.p (v.site x))).symm
                          _ = _ := by ring
      _ = _ := hcrossGrouped.trans hcrossFactor
  have hdiagSplit :
      (∑ x, (v.weight x ^ 4 * f x ^ 2) * s.p (v.site x) ^ 2) =
        (∑ i, s.p i ^ 2 * avg i ^ 2) +
          ∑ x, s.p (v.site x) ^ 2 * v.weight x ^ 4 *
            (f x - avg (v.site x)) ^ 2 := by
    calc
      _ = ∑ i, (∑ x, if v.site x = i then v.weight x ^ 4 * f x ^ 2 else 0) *
            s.p i ^ 2 := hdiag
      _ = ∑ i, (avg i ^ 2 +
            (∑ x, if v.site x = i then v.weight x ^ 4 *
              (f x - avg i) ^ 2 else 0)) * s.p i ^ 2 := by
              apply Finset.sum_congr rfl
              intro i hi
              have hv := weighted_site_variance v f hmass i
              change (∑ x, if v.site x = i then v.weight x ^ 4 *
                (f x - avg i) ^ 2 else 0) =
                (∑ x, if v.site x = i then v.weight x ^ 4 * f x ^ 2 else 0) - avg i ^ 2 at hv
              have hsum :
                  (∑ x, if v.site x = i then v.weight x ^ 4 * f x ^ 2 else 0) =
                    avg i ^ 2 +
                      (∑ x, if v.site x = i then v.weight x ^ 4 *
                        (f x - avg i) ^ 2 else 0) := by linarith
              rw [hsum]
      _ = _ := by
            simp_rw [add_mul]
            rw [Finset.sum_add_distrib]
            have hvarTotal :
                (∑ i, (∑ x, if v.site x = i then v.weight x ^ 4 *
                  (f x - avg i) ^ 2 else 0) * s.p i ^ 2) =
                  ∑ x, s.p (v.site x) ^ 2 * v.weight x ^ 4 *
                    (f x - avg (v.site x)) ^ 2 := by
              symm
              calc
                (∑ x, s.p (v.site x) ^ 2 * v.weight x ^ 4 *
                    (f x - avg (v.site x)) ^ 2) =
                  ∑ x, (v.weight x ^ 4 * (f x - avg (v.site x)) ^ 2) *
                    s.p (v.site x) ^ 2 := by
                      apply Finset.sum_congr rfl
                      intro x hx
                      ring
                _ = ∑ i, (∑ x, if v.site x = i then
                    v.weight x ^ 4 * (f x - avg (v.site x)) ^ 2 else 0) * s.p i ^ 2 :=
                      sum_portwise_site v (fun x => v.weight x ^ 4 *
                        (f x - avg (v.site x)) ^ 2) (fun i => s.p i ^ 2)
                _ = ∑ i, (∑ x, if v.site x = i then
                    v.weight x ^ 4 * (f x - avg i) ^ 2 else 0) * s.p i ^ 2 := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      apply congrArg (fun z : ℝ => z * s.p i ^ 2)
                      apply Finset.sum_congr rfl
                      intro x hx
                      by_cases h : v.site x = i <;> simp [h]
            rw [hvarTotal]
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            ring
  calc
    qform ((v.liftState s).D t) f =
        (∑ x, (v.liftState s).p x * (v.liftState s).q x * f x ^ 2) -
          ∑ x, ∑ y, (v.liftState s).p x * (v.liftState s).p y *
            (v.liftState s).F t x y * f x * f y :=
              qform_state_expansion (v.liftState s) t f
    _ = (∑ x, (v.weight x ^ 4 * f x ^ 2) * s.p (v.site x) ^ 2) -
          ∑ i, ∑ j, s.p i * s.p j * s.F t i j * avg i * avg j := by
            rw [hcrossLift]
            congr 1
            apply Finset.sum_congr rfl
            intro x hx
            rw [lift_p_entry, lift_q_entry, hqp]
            ring
    _ = qform (s.D t) avg +
          ∑ x, s.p (v.site x) ^ 2 * v.weight x ^ 4 *
            (f x - avg (v.site x)) ^ 2 := by
            rw [hdiagSplit, qform_state_expansion]
            simp_rw [hqp]
            ring

theorem lift_D_isSymm (v : PortMap P I) (s : State I) (t : ℝ)
    (hfix : ∀ i, s.g i i = s.r i) (hD : constantKernel (s.D t)) :
    (v.liftState s).D t |>.IsSymm := by
  apply Matrix.IsSymm.ext
  intro x y
  rw [lift_D_entry_scaled v s t hfix, lift_D_entry_scaled v s t hfix]
  have hphysical : s.D t (v.site x) (v.site y) =
      s.D t (v.site y) (v.site x) := by
    have h := congrFun (congrFun hD.1.eq (v.site y)) (v.site x)
    simpa using h
  by_cases hxy : x = y
  · subst y
    simp
  · by_cases hsites : v.site x = v.site y
    · rw [hsites]
      have hyx : y ≠ x := fun h => hxy h.symm
      simp only [if_neg hxy, if_neg hyx, if_pos rfl]
      ring
    · simp [hxy, hsites, hphysical, eq_comm, mul_comm, mul_left_comm, mul_assoc]

theorem lift_K_entry (v : PortMap P I) (s : State I) (t : ℝ) (x y : P) :
    (v.liftState s).K t x y =
      (v.weight x : ℂ) ^ 2 * (v.weight y : ℂ) ^ 2 * s.K t (v.site x) (v.site y) := by
  change ((v.liftState s).h t x y) ^ 2 =
    (v.weight x : ℂ) ^ 2 * (v.weight y : ℂ) ^ 2 * (s.h t (v.site x) (v.site y)) ^ 2
  rw [lift_h_entry]
  ring

theorem lift_K_matrix (v : PortMap P I) (s : State I) (t : ℝ) :
    (v.liftState s).K t = v.Q * s.K t * v.Qᵀ := by
  classical
  ext x y
  rw [lift_K_entry]
  simp [Matrix.mul_apply, PortMap.Q]
  ac_rfl

theorem norm_isometric_conjugation {Q : Matrix P I ℂ} (hQ : Qᴴ * Q = 1)
    (A : Matrix I I ℂ) : ‖Q * A * Qᴴ‖ = ‖A‖ := by
  have hQsq : ‖Q‖ ^ 2 = ‖(1 : Matrix I I ℂ)‖ := by
    rw [pow_two, ← Matrix.l2_opNorm_conjTranspose_mul_self, hQ]
  have hOne : ‖(1 : Matrix I I ℂ)‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_toEuclideanCLM]
    have hId : Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (1 : Matrix I I ℂ) =
        ContinuousLinearMap.id ℂ (EuclideanSpace ℂ I) := by
      ext x i
      simp [Matrix.ofLp_toEuclideanCLM]
    rw [hId]
    exact ContinuousLinearMap.norm_id_le
  have hQnorm : ‖Q‖ ≤ 1 := by
    have hnonneg := norm_nonneg Q
    nlinarith
  have hQtnorm : ‖Qᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hQnorm
  have hQprod : ‖Qᴴ‖ * ‖Q‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    nlinarith [norm_nonneg Q]
  have hQprod' : ‖Q‖ * ‖Qᴴ‖ ≤ 1 := by simpa [mul_comm] using hQprod
  apply le_antisymm
  · calc
      ‖Q * A * Qᴴ‖ ≤ ‖Q * A‖ * ‖Qᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖Q‖ * ‖A‖) * ‖Qᴴ‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul Q A) (norm_nonneg _)
      _ ≤ ‖A‖ := by
        calc
          (‖Q‖ * ‖A‖) * ‖Qᴴ‖ = (‖Q‖ * ‖Qᴴ‖) * ‖A‖ := by ring
          _ ≤ 1 * ‖A‖ := mul_le_mul_of_nonneg_right hQprod' (norm_nonneg _)
          _ = ‖A‖ := one_mul _
  · have hcancel : Qᴴ * (Q * A * Qᴴ) * Q = A := by
      calc
        Qᴴ * (Q * A * Qᴴ) * Q = Qᴴ * ((Q * A) * (Qᴴ * Q)) := by
          rw [Matrix.mul_assoc]
          congr 1
          exact Matrix.mul_assoc (Q * A) Qᴴ Q
        _ = (Qᴴ * (Q * A)) * (Qᴴ * Q) := by rw [← Matrix.mul_assoc]
        _ = ((Qᴴ * Q) * A) * (Qᴴ * Q) := by rw [← Matrix.mul_assoc Qᴴ Q A]
        _ = A := by rw [hQ]; simp
    calc
      ‖A‖ = ‖Qᴴ * (Q * A * Qᴴ) * Q‖ := by rw [hcancel]
      _ ≤ ‖Qᴴ‖ * ‖Q * A * Qᴴ‖ * ‖Q‖ := by
        calc
          ‖Qᴴ * (Q * A * Qᴴ) * Q‖ ≤ ‖Qᴴ * (Q * A * Qᴴ)‖ * ‖Q‖ :=
            Matrix.l2_opNorm_mul _ _
          _ ≤ (‖Qᴴ‖ * ‖Q * A * Qᴴ‖) * ‖Q‖ :=
            mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
          _ = ‖Qᴴ‖ * ‖Q * A * Qᴴ‖ * ‖Q‖ := by ring
      _ ≤ ‖Q * A * Qᴴ‖ := by
        calc
          ‖Qᴴ‖ * ‖Q * A * Qᴴ‖ * ‖Q‖ =
              (‖Qᴴ‖ * ‖Q‖) * ‖Q * A * Qᴴ‖ := by ring
          _ ≤ 1 * ‖Q * A * Qᴴ‖ :=
            mul_le_mul_of_nonneg_right hQprod (norm_nonneg _)
          _ = _ := one_mul _

theorem lift_fourthRow (v : PortMap P I) (s : State I) (t : ℝ)
    (hmass : ∀ i, v.mass i = 1) (x : P) :
    (v.liftState s).fourthRow t Finset.univ x =
      v.weight x ^ 4 * s.fourthRow t Finset.univ (v.site x) := by
  classical
  rw [State.fourthRow]
  have hterm (y : P) :
      ‖(v.liftState s).h t x y‖ ^ 4 =
        v.weight x ^ 4 * v.weight y ^ 4 * ‖s.h t (v.site x) (v.site y)‖ ^ 4 := by
    rw [lift_h_entry, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real]
    have hx : |v.weight x| ^ 4 = v.weight x ^ 4 := by nlinarith [sq_abs (v.weight x)]
    have hy : |v.weight y| ^ 4 = v.weight y ^ 4 := by nlinarith [sq_abs (v.weight y)]
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    calc
      (|v.weight x| * |v.weight y| * ‖s.h t (v.site x) (v.site y)‖) ^ 4 =
          |v.weight x| ^ 4 * |v.weight y| ^ 4 * ‖s.h t (v.site x) (v.site y)‖ ^ 4 := by ring
      _ = _ := by rw [hx, hy]
  simp_rw [hterm]
  calc
    (∑ y, v.weight x ^ 4 * v.weight y ^ 4 *
        ‖s.h t (v.site x) (v.site y)‖ ^ 4) =
      v.weight x ^ 4 * ∑ y, v.weight y ^ 4 *
        ‖s.h t (v.site x) (v.site y)‖ ^ 4 := by
          simpa [mul_assoc] using (Finset.mul_sum Finset.univ
            (fun y => v.weight y ^ 4 * ‖s.h t (v.site x) (v.site y)‖ ^ 4)
            (v.weight x ^ 4)).symm
    _ = v.weight x ^ 4 *
        ∑ i, v.mass i * ‖s.h t (v.site x) i‖ ^ 4 := by
          exact congrArg (fun z : ℝ => v.weight x ^ 4 * z)
            (sum_weight_fourth_site v (fun i => ‖s.h t (v.site x) i‖ ^ 4))
    _ = v.weight x ^ 4 * s.fourthRow t Finset.univ (v.site x) := by
          simp [State.fourthRow, hmass]

theorem port_Q_conjTranspose_eq_transpose (v : PortMap P I) :
    v.Qᴴ = v.Qᵀ := by
  classical
  ext x i
  by_cases h : v.site i = x <;> simp [PortMap.Q, h]

set_option maxHeartbeats 1000000 in
theorem duplication_algebraic {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] (v : PortMap P I) (s : State I) (t : ℝ)
    (hmass : ∀ i, v.mass i = 1) (hfix : ∀ i, s.g i i = s.r i) :
    v.Qᴴ * v.Q = 1 ∧ (v.liftState s).K t = v.Q * s.K t * v.Qᵀ ∧
    ‖(v.liftState s).K t‖ = ‖s.K t‖ ∧
    (∀ x, (v.liftState s).fourthRow t Finset.univ x =
      v.weight x ^ 4 * s.fourthRow t Finset.univ (v.site x)) ∧
    (∀ f, qform ((v.liftState s).D t) f = qform (s.D t) (v.average f) +
      ∑ x, s.p (v.site x) ^ 2 * v.weight x ^ 4 *
        (f x - v.average f (v.site x)) ^ 2) := by
  refine ⟨port_Q_isometry v hmass, lift_K_matrix v s t, ?_, ?_, ?_⟩
  · rw [lift_K_matrix, ← port_Q_conjTranspose_eq_transpose]
    exact norm_isometric_conjugation (port_Q_isometry v hmass) (s.K t)
  · exact lift_fourthRow v s t hmass
  · intro f
    exact lift_qform_split v s t f hmass hfix

theorem port_deviation_dual_value {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] (v : PortMap P I) (s : State I)
    (y : P → ℝ) :
    (∑ x, y x *
        (y x / (s.p (v.site x) ^ 2 * v.weight x ^ 4) -
          v.sumCharge y (v.site x) / s.p (v.site x) ^ 2)) =
      (∑ x, y x ^ 2 /
        (v.weight x ^ 4 * s.p (v.site x) ^ 2)) -
        ∑ i, (v.sumCharge y i) ^ 2 / s.p i ^ 2 := by
  classical
  let c : P → ℝ := fun x =>
    y x / (s.p (v.site x) ^ 2 * v.weight x ^ 4) -
      v.sumCharge y (v.site x) / s.p (v.site x) ^ 2
  have hcross :
      (∑ x, y x * (v.sumCharge y (v.site x) / s.p (v.site x) ^ 2)) =
        ∑ i, (v.sumCharge y i) ^ 2 / s.p i ^ 2 := by
    calc
      _ = ∑ i, (∑ x, if v.site x = i then y x else 0) *
          (v.sumCharge y i / s.p i ^ 2) :=
            sum_portwise_site v y (fun i => v.sumCharge y i / s.p i ^ 2)
      _ = _ := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [PortMap.sumCharge]
            ring
  calc
    (∑ x, y x * c x) =
        ∑ x, (y x ^ 2 /
          (v.weight x ^ 4 * s.p (v.site x) ^ 2) -
          y x * (v.sumCharge y (v.site x) / s.p (v.site x) ^ 2)) := by
            apply Finset.sum_congr rfl
            intro x hx
            dsimp [c]
            ring
    _ = (∑ x, y x ^ 2 /
          (v.weight x ^ 4 * s.p (v.site x) ^ 2)) -
        ∑ x, y x * (v.sumCharge y (v.site x) / s.p (v.site x) ^ 2) := by
          rw [Finset.sum_sub_distrib]
    _ = _ := by rw [hcross]

theorem duplication_dual_identity {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] (v : PortMap P I) (s : State I) (t : ℝ)
    (hmass : ∀ i, v.mass i = 1) (hk : ∀ x, 0 < v.weight x)
    (hfix : ∀ i, s.g i i = s.r i) (hkernel : constantKernel (s.D t))
    (hp : ∀ i, 0 < s.p i) :
    ∀ y, neutral y →
      (v.liftState s).X t y = s.X t (v.sumCharge y) +
        (∑ x, y x ^ 2 / (v.weight x ^ 4 * s.p (v.site x) ^ 2)) -
          ∑ i, (v.sumCharge y i) ^ 2 / s.p i ^ 2 := by
  classical
  intro y hy
  by_cases hI : Nonempty I
  · letI := hI
    let Y : I → ℝ := v.sumCharge y
    obtain ⟨b, hb, hbneutral⟩ :=
      exists_solution_constantKernel hkernel Y (sumCharge_neutral v y hy)
    let c : P → ℝ := fun x =>
      y x / (s.p (v.site x) ^ 2 * v.weight x ^ 4) -
        Y (v.site x) / s.p (v.site x) ^ 2
    have hcmean : ∀ i,
        (∑ x, if v.site x = i then v.weight x ^ 4 * c x else 0) = 0 := by
      intro i
      calc
        _ = ∑ x, if v.site x = i then
              v.weight x ^ 4 *
                (y x / (s.p i ^ 2 * v.weight x ^ 4) -
                  v.sumCharge y i / s.p i ^ 2) else 0 := by
                apply Finset.sum_congr rfl
                intro x hx
                by_cases hs : v.site x = i <;> simp [c, Y, hs]
        _ = 0 := port_deviation_weighted_mean v s y hmass hk hp i
    have hcpoint (x : P) :
        v.weight x ^ 4 *
          (s.p (v.site x) ^ 2 * c x + Y (v.site x)) = y x := by
      dsimp [c]
      have hp2 : s.p (v.site x) ^ 2 ≠ 0 :=
        ne_of_gt (sq_pos_of_pos (hp (v.site x)))
      have hw4 : v.weight x ^ 4 ≠ 0 :=
        ne_of_gt (pow_pos (hk x) 4)
      field_simp [hp2, hw4]
      have hpne : s.p (v.site x) ≠ 0 := ne_of_gt (hp (v.site x))
      simp [hpne]
      rw [← mul_div_assoc]
      exact mul_div_cancel_left₀ (y x) hw4
    have hliftSolve :
        (v.liftState s).D t *ᵥ (fun x => b (v.site x) + c x) = y := by
      apply lift_D_mulVec_of_centered v s t hmass hfix c b y hcmean
      · simpa [Y] using hb
      · simpa [Y] using hcpoint
    have hliftSymm : (v.liftState s).D t |>.IsSymm :=
      lift_D_isSymm v s t hfix hkernel
    have hliftPos : ∀ f, 0 ≤ qform ((v.liftState s).D t) f := by
      intro f
      rw [lift_qform_split v s t f hmass hfix]
      apply add_nonneg (hkernel.2.1 (v.average f))
      apply Finset.sum_nonneg
      intro x hx
      positivity
    have hdualLift := dualForm_eq_of_solve
      (D := (v.liftState s).D t) hliftSymm hliftPos y
      (fun x => b (v.site x) + c x) hliftSolve
    have hdualBase := dualForm_eq_of_solve
      (D := s.D t) hkernel.1 hkernel.2.1 Y b (by simpa [Y] using hb)
    have hbasePair :
        (∑ x, y x * b (v.site x)) = ∑ i, Y i * b i := by
      simpa [Y, PortMap.sumCharge] using sum_portwise_site v y b
    have hpair :
        (∑ x, y x * (b (v.site x) + c x)) =
          (∑ i, Y i * b i) +
            ((∑ x, y x ^ 2 /
              (v.weight x ^ 4 * s.p (v.site x) ^ 2)) -
              ∑ i, Y i ^ 2 / s.p i ^ 2) := by
      calc
        _ = (∑ x, y x * b (v.site x)) + ∑ x, y x * c x := by
              calc
                _ = ∑ x, (y x * b (v.site x) + y x * c x) := by
                      apply Finset.sum_congr rfl
                      intro x hx
                      ring
                _ = _ := Finset.sum_add_distrib
        _ = _ := by
              rw [hbasePair]
              simpa [Y, c] using port_deviation_dual_value v s y
    change dualForm (qform ((v.liftState s).D t)) y =
      dualForm (qform (s.D t)) (v.sumCharge y) +
        (∑ x, y x ^ 2 / (v.weight x ^ 4 * s.p (v.site x) ^ 2)) -
          ∑ i, (v.sumCharge y i) ^ 2 / s.p i ^ 2
    rw [hdualLift, hdualBase, hpair]
    dsimp [Y]
    ring
  · have hIempty : IsEmpty I := ⟨fun i => hI ⟨i⟩⟩
    letI := hIempty
    have hPempty : IsEmpty P := ⟨fun x => hI ⟨v.site x⟩⟩
    letI := hPempty
    simp [State.X, dualForm, qform, PortMap.sumCharge]

theorem port_weighted_charge_bound {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] (v : PortMap P I) (s : State I)
    (hmass : ∀ i, v.mass i = 1) (hk : ∀ x, 0 < v.weight x)
    (hp : ∀ i, 0 < s.p i) (y : P → ℝ) :
    (∑ i, (v.sumCharge y i) ^ 2 / s.p i ^ 2) ≤
      ∑ x, y x ^ 2 / (v.weight x ^ 4 * s.p (v.site x) ^ 2) := by
  classical
  have hsite (i : I) :
      (v.sumCharge y i) ^ 2 / s.p i ^ 2 ≤
        ∑ x, if v.site x = i then
          y x ^ 2 / (v.weight x ^ 4 * s.p i ^ 2) else 0 := by
    let f : P → ℝ := fun x => y x / v.weight x ^ 4
    have havg : v.average f i = v.sumCharge y i := by
      change (∑ x, if v.site x = i then v.weight x ^ 4 *
          (y x / v.weight x ^ 4) else 0) =
        ∑ x, if v.site x = i then y x else 0
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hs : v.site x = i
      · simp [hs]
        rw [← mul_div_assoc]
        exact mul_div_cancel_left₀ (y x) (ne_of_gt (pow_pos (hk x) 4))
      · simp [hs]
    have hvarNonneg :
        0 ≤ ∑ x, if v.site x = i then
          v.weight x ^ 4 * (f x - v.average f i) ^ 2 else 0 := by
      apply Finset.sum_nonneg
      intro x hx
      by_cases hs : v.site x = i <;> simp [hs] <;> positivity
    have hvariance := weighted_site_variance v f hmass i
    rw [hvariance, havg] at hvarNonneg
    have hfiber :
        (v.sumCharge y i) ^ 2 ≤
          ∑ x, if v.site x = i then y x ^ 2 / v.weight x ^ 4 else 0 := by
      have hconvert :
          (∑ x, if v.site x = i then v.weight x ^ 4 * f x ^ 2 else 0) =
            ∑ x, if v.site x = i then y x ^ 2 / v.weight x ^ 4 else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hs : v.site x = i
        · simp [hs, f]
          field_simp [ne_of_gt (pow_pos (hk x) 4)] <;> ring
        · simp [hs]
      rw [← hconvert]
      linarith
    calc
      _ ≤ (∑ x, if v.site x = i then
            y x ^ 2 / v.weight x ^ 4 else 0) / s.p i ^ 2 :=
        div_le_div_of_nonneg_right hfiber (sq_nonneg _)
      _ = (∑ x, if v.site x = i then
            y x ^ 2 / v.weight x ^ 4 else 0) / s.p i ^ 2 := rfl
      _ = ∑ x, if v.site x = i then
            y x ^ 2 / (v.weight x ^ 4 * s.p i ^ 2) else 0 := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro x hx
            by_cases hs : v.site x = i
            · simp [hs, div_div]
            · simp [hs]
  have hsiteSum := Finset.sum_le_sum (s := Finset.univ) (fun i hi => hsite i)
  have hfiberEq (i : I) :
      (∑ x, if v.site x = i then
        y x ^ 2 / (v.weight x ^ 4 * s.p i ^ 2) else 0) =
      ∑ x, if v.site x = i then
        y x ^ 2 / (v.weight x ^ 4 * s.p (v.site x) ^ 2) else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : v.site x = i <;> simp [h]
  calc
    _ ≤ ∑ i, ∑ x, if v.site x = i then
          y x ^ 2 / (v.weight x ^ 4 * s.p i ^ 2) else 0 := hsiteSum
    _ = ∑ x, y x ^ 2 / (v.weight x ^ 4 * s.p (v.site x) ^ 2) := by
          calc
            _ = ∑ i, ∑ x, if v.site x = i then
                  y x ^ 2 / (v.weight x ^ 4 * s.p (v.site x) ^ 2) else 0 := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    exact hfiberEq i
            _ = _ := by
                  symm
                  simpa using sum_portwise_site v
                    (fun x => y x ^ 2 /
                      (v.weight x ^ 4 * s.p (v.site x) ^ 2))
                    (fun _ => 1)

theorem duplication_proof {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] (v : PortMap P I) (s : State I) (t : ℝ)
    (hmass : ∀ i, v.mass i = 1) (hk : ∀ x, 0 < v.weight x)
    (hfix : ∀ i, s.g i i = s.r i) (hkernel : constantKernel (s.D t))
    (hp : ∀ i, 0 < s.p i) :
    let s0 := v.liftState s
    v.Qᴴ * v.Q = 1 ∧ s0.K t = v.Q * s.K t * v.Qᵀ ∧
    ‖s0.K t‖ = ‖s.K t‖ ∧
    (∀ x, s0.fourthRow t Finset.univ x =
      v.weight x ^ 4 * s.fourthRow t Finset.univ (v.site x)) ∧
    (∀ f, qform (s0.D t) f = qform (s.D t) (v.average f) +
      ∑ x, s.p (v.site x)^2 * v.weight x^4 *
        (f x - v.average f (v.site x))^2) ∧
    (∀ y, neutral y → s0.X t y = s.X t (v.sumCharge y) +
      (∑ x, y x^2 / (v.weight x^4 * s.p (v.site x)^2)) -
      ∑ i, (v.sumCharge y i)^2 / s.p i^2) := by
  classical
  rcases duplication_algebraic v s t hmass hfix with
    ⟨hQ, hK, hnorm, hrow, hqform⟩
  refine ⟨hQ, hK, hnorm, hrow, hqform, ?_⟩
  intro y hy
  exact duplication_dual_identity v s t hmass hk hfix hkernel hp y hy

theorem duplication_sharp_proof {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] (v : PortMap P I) (s : State I) (t a c : ℝ)
    (Λplus : Form I) (ht : 0 < t) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hmass : ∀ i, v.mass i = 1) (hk : ∀ x, 0 < v.weight x)
    (hfix : ∀ i, s.g i i = s.r i) (hp : ∀ i, 0 < s.p i)
    (hkernel : constantKernel (s.D t))
    (hsharp : ∀ y, neutral y → s.X t y ≤
      (1 + a) * (∑ i, y i ^ 2 / s.p i ^ 2) + c * t * Λplus y) :
    ∀ y, neutral y → (v.liftState s).X t y ≤
      (1 + a) * (∑ x, y x ^ 2 / (v.liftState s).p x ^ 2) +
        c * t * Λplus (v.sumCharge y) := by
  classical
  intro y hy
  have hybase := sumCharge_neutral v y hy
  have hsharpY := hsharp (v.sumCharge y) hybase
  have hCauchy := port_weighted_charge_bound v s hmass hk hp y
  have hweight := mul_le_mul_of_nonneg_left hCauchy ha
  have hdual := duplication_dual_identity v s t hmass hk hfix hkernel hp y hy
  have hpLift (x : P) :
      (v.liftState s).p x ^ 2 = v.weight x ^ 4 * s.p (v.site x) ^ 2 := by
    rw [lift_p_entry]
    ring
  have hdiag :
      (∑ x, y x ^ 2 / (v.liftState s).p x ^ 2) =
        ∑ x, y x ^ 2 / (v.weight x ^ 4 * s.p (v.site x) ^ 2) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [hpLift x]
  have hnormed :
      (v.liftState s).X t y ≤
        s.X t (v.sumCharge y) +
          (∑ x, y x ^ 2 / (v.weight x ^ 4 * s.p (v.site x) ^ 2)) -
            ∑ i, (v.sumCharge y i) ^ 2 / s.p i ^ 2 := by
    rw [hdual]
  rw [hdiag]
  calc
    (v.liftState s).X t y ≤
        s.X t (v.sumCharge y) +
          (∑ x, y x ^ 2 / (v.weight x ^ 4 * s.p (v.site x) ^ 2)) -
            ∑ i, (v.sumCharge y i) ^ 2 / s.p i ^ 2 := hnormed
    _ ≤ ((1 + a) * (∑ i, (v.sumCharge y i) ^ 2 / s.p i ^ 2) +
          c * t * Λplus (v.sumCharge y)) +
          (∑ x, y x ^ 2 / (v.weight x ^ 4 * s.p (v.site x) ^ 2)) -
            ∑ i, (v.sumCharge y i) ^ 2 / s.p i ^ 2 := by
          gcongr
    _ ≤ (1 + a) *
          (∑ x, y x ^ 2 / (v.weight x ^ 4 * s.p (v.site x) ^ 2)) +
          c * t * Λplus (v.sumCharge y) := by
          nlinarith [hweight]

theorem physical_damped_matrix_isUnit {I : Type*} [Fintype I] [DecidableEq I]
    (M : RMat I) (t : ℝ) (r : I → ℂ) (d : I → ℝ)
    (ht : 0 < t) (hM : M.IsSymm) (hd : ∀ i, 0 < d i)
    (hr : ∀ i, 0 < (r i).im) :
    IsUnit (M.map (fun z : ℝ => (z : ℂ)) -
      diagonal (fun i => ((t * d i : ℝ) : ℂ) * r i)) := by
  classical
  let Mc : CMat I := M.map (fun z : ℝ => (z : ℂ))
  let dC : I → ℂ := fun i => ((t * d i : ℝ) : ℂ) * r i
  let A : CMat I := Mc - diagonal dC
  have hMc : Mc.IsHermitian := by
    have hM' : M.IsHermitian := by
      rw [Matrix.isHermitian_iff_isSymm]
      exact hM
    exact hM'.map Complex.ofReal (by intro z; simp)
  have hdiag (x : I → ℂ) :
      star x ⬝ᵥ diagonal dC *ᵥ x =
        ∑ i, dC i * (Complex.normSq (x i) : ℂ) := by
    calc
      star x ⬝ᵥ diagonal dC *ᵥ x =
          ∑ i, star (x i) * (dC i * x i) := by
            simp [dotProduct, Matrix.mulVec_diagonal]
      _ = _ := by
            apply Finset.sum_congr rfl
            intro i hi
            have hx : (Complex.normSq (x i) : ℂ) = star (x i) * x i := by
              simpa [Complex.star_def] using
                (Complex.normSq_eq_conj_mul_self (z := x i))
            rw [hx]
            ring
  have hquad (x : I → ℂ) :
      star x ⬝ᵥ A *ᵥ x =
        (star x ⬝ᵥ Mc *ᵥ x) -
          ∑ i, dC i * (Complex.normSq (x i) : ℂ) := by
    have hsub : (Mc - diagonal dC) *ᵥ x =
        Mc *ᵥ x - diagonal dC *ᵥ x := by
      ext i
      simp [Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]
    calc
      star x ⬝ᵥ A *ᵥ x = star x ⬝ᵥ (Mc - diagonal dC) *ᵥ x := by
        rfl
      _ = star x ⬝ᵥ (Mc *ᵥ x - diagonal dC *ᵥ x) := by rw [hsub]
      _ = _ := by rw [dotProduct_sub, hdiag]
  have hker : ∀ x, A *ᵥ x = 0 → x = 0 := by
    intro x hx
    have hq0 : star x ⬝ᵥ A *ᵥ x = 0 := by simp [hx]
    have hMcstar := hMc.star_dotProduct_mulVec_comm x x
    have hMcconj :
        star (star x ⬝ᵥ Mc *ᵥ x) = star x ⬝ᵥ Mc *ᵥ x := by
      simpa using hMcstar
    have hMcim : (star x ⬝ᵥ Mc *ᵥ x).im = 0 :=
      Complex.conj_eq_iff_im.mp (by simpa [Complex.star_def] using hMcconj)
    have hdCim :
        (∑ i, dC i * (Complex.normSq (x i) : ℂ)).im =
          ∑ i, (t * d i) * (r i).im * Complex.normSq (x i) := by
      rw [Complex.im_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp [dC, Complex.mul_im, Complex.im_ofReal_mul]
    have hsum0 :
        ∑ i, (t * d i) * (r i).im * Complex.normSq (x i) = 0 := by
      have hqIm := congrArg Complex.im hq0
      rw [hquad, Complex.sub_im, hMcim, hdCim] at hqIm
      simpa using hqIm.symm
    have hcoef (i : I) : 0 < (t * d i) * (r i).im :=
      mul_pos (mul_pos ht (hd i)) (hr i)
    have htermnonneg (i : I) :
        0 ≤ (t * d i) * (r i).im * Complex.normSq (x i) :=
      mul_nonneg (le_of_lt (hcoef i)) (Complex.normSq_nonneg _)
    have htermzero : ∀ i,
        (t * d i) * (r i).im * Complex.normSq (x i) = 0 := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => htermnonneg i)).mp hsum0
      intro i
      exact hz i (Finset.mem_univ i)
    ext i
    have hnormSq : Complex.normSq (x i) = 0 := by
      rcases mul_eq_zero.mp (htermzero i) with hzero | hzero
      · exact False.elim ((ne_of_gt (hcoef i)) hzero)
      · exact hzero
    exact Complex.normSq_eq_zero.mp hnormSq
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    have hz : A *ᵥ (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy]
      simp
    have hzero := hker (x - y) hz
    exact sub_eq_zero.mp hzero
  have hunit : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp hinj
  simpa [A, Mc, dC] using hunit

theorem physical_resolvent_ward {I : Type*} [Fintype I] [DecidableEq I]
    (M : RMat I) (t : ℝ) (r : I → ℂ) (d : I → ℝ)
    (ht : 0 < t) (hM : M.IsSymm) (hd : ∀ i, 0 < d i)
    (hr : ∀ i, 0 < (r i).im) :
    let A := M.map (fun z : ℝ => (z : ℂ)) -
      diagonal (fun i => ((t * d i : ℝ) : ℂ) * r i)
    let G := A⁻¹
    G * diagonal (fun i => ((t * d i * (r i).im : ℝ) : ℂ)) * Gᴴ =
      matrixIm G := by
  classical
  let Mc : CMat I := M.map (fun z : ℝ => (z : ℂ))
  let dC : I → ℂ := fun i => ((t * d i : ℝ) : ℂ) * r i
  let q : I → ℝ := fun i => t * d i * (r i).im
  let A : CMat I := Mc - diagonal dC
  let G : CMat I := A⁻¹
  have hMc : Mc.IsHermitian := by
    have hM' : M.IsHermitian := by
      rw [Matrix.isHermitian_iff_isSymm]
      exact hM
    exact hM'.map Complex.ofReal (by intro z; simp)
  have hMcSymm : Mc.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    have hij := congrFun (congrFun hM.eq i) j
    simpa [Mc] using congrArg Complex.ofReal hij
  have hAsymm : A.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    have hsym : Mc i j = Mc j i := by
      have hji := congrFun (congrFun hMcSymm.eq i) j
      simpa using hji.symm
    by_cases hij : i = j
    · subst j
      simp [A, Mc, dC, Matrix.diagonal]
    · simpa [A, Mc, dC, Matrix.diagonal, hij, eq_comm] using hsym.symm
  have hAadj : Aᴴ = Mc - diagonal (fun i => star (dC i)) := by
    change (Mc - diagonal dC)ᴴ = Mc - diagonal (fun i => star (dC i))
    rw [Matrix.conjTranspose_sub, hMc.eq]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.conjTranspose_apply, Matrix.diagonal]
    · simp [Matrix.conjTranspose_apply, Matrix.diagonal, hij, eq_comm]
  have hAadjDiff : Aᴴ - A = diagonal (fun i => dC i - star (dC i)) := by
    rw [hAadj]
    dsimp [A]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hij]
  have hDdiff (i : I) :
      dC i - star (dC i) = (2 * Complex.I) * ((q i : ℝ) : ℂ) := by
    change ((t * d i : ℝ) : ℂ) * r i -
      star (((t * d i : ℝ) : ℂ) * r i) =
        (2 * Complex.I) * (((t * d i * (r i).im : ℝ) : ℂ))
    calc
      _ = ((t * d i : ℝ) : ℂ) * (r i - star (r i)) := by
            rw [star_mul, Complex.star_def, Complex.conj_ofReal]
            ring
      _ = ((t * d i : ℝ) : ℂ) * ((2 * (r i).im : ℝ) * Complex.I) := by
            rw [Complex.star_def, Complex.sub_conj]
      _ = (2 * Complex.I) * ((t * d i * (r i).im : ℝ) : ℂ) := by
            push_cast
            ring
  have hAimag : Aᴴ - A =
      (2 * Complex.I) • diagonal (fun i => ((q i : ℝ) : ℂ)) := by
    rw [hAadjDiff]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal]
      exact hDdiff i
    · simp [Matrix.diagonal, hij]
  have hGsymm : G.IsSymm := by
    change Gᵀ = G
    dsimp [G]
    rw [Matrix.transpose_nonsing_inv, hAsymm.eq]
  have hGdiff : G - Gᴴ =
      (2 * Complex.I) • matrixIm G := by
    ext i j
    have hji : G j i = G i j := by
      have hij := congrFun (congrFun hGsymm.eq i) j
      simpa using hij
    simp only [Matrix.sub_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
      matrixIm]
    rw [hji, Complex.star_def, Complex.sub_conj]
    push_cast
    ring
  have hAunit : IsUnit A := by
    apply physical_damped_matrix_isUnit M t r d ht hM hd hr
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hAunit
  have hGA : G * A = 1 := by
    dsimp [G]
    exact Matrix.nonsing_inv_mul A hdet
  have hAadjGadj : Aᴴ * Gᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hGA]
    simp
  have hAlg : G * (Aᴴ - A) * Gᴴ = G - Gᴴ := by
    calc
      _ = G * (Aᴴ * Gᴴ) - (G * A) * Gᴴ := by noncomm_ring
      _ = G - Gᴴ := by rw [hAadjGadj, hGA]; simp
  have hscaled :
      (2 * Complex.I) •
          (G * diagonal (fun i => ((q i : ℝ) : ℂ)) * Gᴴ) =
        (2 * Complex.I) • matrixIm G := by
    calc
      _ = G * ((2 * Complex.I) •
          diagonal (fun i => ((q i : ℝ) : ℂ))) * Gᴴ := by
            simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = G * (Aᴴ - A) * Gᴴ := by rw [hAimag]
      _ = G - Gᴴ := hAlg
      _ = _ := hGdiff
  have hscalar : (2 * Complex.I : ℂ) ≠ 0 := by norm_num
  have hward0 :
      G * diagonal (fun i => ((q i : ℝ) : ℂ)) * Gᴴ = matrixIm G :=
    by
      apply Matrix.ext
      intro i j
      have hentry := congrArg (fun B : CMat I => B i j) hscaled
      have hmul :
          (2 * Complex.I) *
              (G * diagonal (fun i => ((q i : ℝ) : ℂ)) * Gᴴ) i j =
            (2 * Complex.I) * (matrixIm G i j) := by
        simpa [Matrix.smul_apply] using hentry
      exact mul_left_cancel₀ hscalar hmul
  simpa [q, A, G, Mc, dC] using hward0


end AndersonAC.AgentS45
