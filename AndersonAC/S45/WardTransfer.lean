import AndersonAC.S45.DuplicationProof
import AndersonAC.S45.WardNorm

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder
namespace AndersonAC.AgentS45

open AndersonAC.S45

theorem physical_damped_matrix_inverse_isSymm {I : Type*} [Fintype I]
    [DecidableEq I] (M : RMat I) (t : ℝ) (r : I → ℂ) (d : I → ℝ)
    (hM : M.IsSymm) :
    (M.map (fun z : ℝ => (z : ℂ)) -
      diagonal (fun i => ((t * d i : ℝ) : ℂ) * r i))⁻¹ |>.IsSymm := by
  classical
  let Mc : CMat I := M.map (fun z : ℝ => (z : ℂ))
  let dC : I → ℂ := fun i => ((t * d i : ℝ) : ℂ) * r i
  let A : CMat I := Mc - diagonal dC
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
  change A⁻¹ᵀ = A⁻¹
  rw [Matrix.transpose_nonsing_inv, hAsymm.eq]

theorem lift_g_isSymm {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] (v : PortMap P I) (s : State I)
    (hs : s.g.IsSymm) : (v.liftState s).g.IsSymm := by
  apply Matrix.IsSymm.ext
  intro x y
  have hxy : s.g (v.site x) (v.site y) = s.g (v.site y) (v.site x) := by
    have h := congrFun (congrFun hs.eq (v.site x)) (v.site y)
    simpa using h.symm
  simp [PortMap.liftState, hxy, mul_comm]

theorem sum_weight_fourth_site_complex {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] (v : PortMap P I) (b : I → ℂ) :
    (∑ x, (v.weight x ^ 4 : ℂ) * b (v.site x)) =
      ∑ i, (v.mass i : ℂ) * b i := by
  classical
  have hmass (i : I) :
      (∑ x, if v.site x = i then (v.weight x ^ 4 : ℂ) else 0) =
        (v.mass i : ℂ) := by
    calc
      _ = ∑ x, ((if v.site x = i then v.weight x ^ 4 else 0 : ℝ) : ℂ) := by
            apply Finset.sum_congr rfl
            intro x hx
            by_cases h : v.site x = i <;> simp [h]
      _ = ((∑ x, if v.site x = i then v.weight x ^ 4 else 0 : ℝ) : ℂ) := by
            rw [Complex.ofReal_sum]
      _ = _ := by simp [PortMap.mass]
  calc
    (∑ x, (v.weight x ^ 4 : ℂ) * b (v.site x)) =
        ∑ x, ∑ i, if v.site x = i then
          (v.weight x ^ 4 : ℂ) * b i else 0 := by
            apply Finset.sum_congr rfl
            intro x hx
            simp [← eq_comm]
    _ = ∑ i, ∑ x, if v.site x = i then
          (v.weight x ^ 4 : ℂ) * b i else 0 := by rw [Finset.sum_comm]
    _ = ∑ i, (∑ x, if v.site x = i then
          (v.weight x ^ 4 : ℂ) else 0) * b i := by
            apply Finset.sum_congr rfl
            intro i hi
            calc
              _ = ∑ x, (if v.site x = i then
                    (v.weight x ^ 4 : ℂ) else 0) * b i := by
                      apply Finset.sum_congr rfl
                      intro x hx
                      by_cases h : v.site x = i <;> simp [h]
              _ = _ := by
                    exact (Finset.sum_mul Finset.univ
                      (fun x => if v.site x = i then
                        (v.weight x ^ 4 : ℂ) else 0) (b i)).symm
    _ = ∑ i, (v.mass i : ℂ) * b i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hmass i]

theorem lift_mass_ward {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] (v : PortMap P I) (s : State I) (t : ℝ)
    (hward : s.h t *
      diagonal (fun i => ((v.mass i * s.p i : ℝ) : ℂ)) * (s.h t)ᴴ =
        matrixIm s.g) : (v.liftState s).ward t := by
  classical
  ext x z
  let i := v.site x
  let k := v.site z
  let b : I → ℂ := fun j => s.h t i j * (s.p j : ℂ) * star (s.h t k j)
  have hphys :
      (s.h t * diagonal (fun j => ((v.mass j * s.p j : ℝ) : ℂ)) *
        (s.h t)ᴴ) i k = ∑ j, (v.mass j : ℂ) * b j := by
    simp [b, Matrix.mul_apply, Matrix.diagonal, Matrix.conjTranspose_apply,
      mul_assoc, mul_comm, mul_left_comm]
  have hterm (y : P) :
      (v.liftState s).h t x y * ((v.liftState s).p y : ℂ) *
          star ((v.liftState s).h t z y) =
        (v.weight x : ℂ) * (v.weight z : ℂ) *
          (v.weight y ^ 4 : ℂ) * b (v.site y) := by
    rw [lift_h_entry, lift_p_entry, lift_h_entry]
    simp [b, i, k, Complex.star_def]
    ring
  have hmatrix :
      ((v.liftState s).h t *
        diagonal (fun y => ((v.liftState s).p y : ℂ)) *
        ((v.liftState s).h t)ᴴ) x z =
        ((v.liftState s).g x z).im := by
    simp only [Matrix.mul_apply]
    simp [Matrix.diagonal, Matrix.conjTranspose_apply]
    calc
      _ = ∑ y, (v.weight x : ℂ) * (v.weight z : ℂ) *
          (v.weight y ^ 4 : ℂ) * b (v.site y) := by
            apply Finset.sum_congr rfl
            intro y hy
            exact hterm y
      _ = (v.weight x : ℂ) * (v.weight z : ℂ) *
          ∑ y, (v.weight y ^ 4 : ℂ) * b (v.site y) := by
            calc
              _ = ∑ y, ((v.weight x : ℂ) * (v.weight z : ℂ)) *
                  ((v.weight y ^ 4 : ℂ) * b (v.site y)) := by
                    apply Finset.sum_congr rfl
                    intro y hy
                    ring
              _ = _ := (Finset.mul_sum Finset.univ
              (fun y => (v.weight y ^ 4 : ℂ) * b (v.site y))
              ((v.weight x : ℂ) * (v.weight z : ℂ))).symm
      _ = (v.weight x : ℂ) * (v.weight z : ℂ) *
          ∑ j, (v.mass j : ℂ) * b j := by
            rw [sum_weight_fourth_site_complex]
      _ = (v.weight x : ℂ) * (v.weight z : ℂ) *
          ((s.h t * diagonal (fun j =>
            ((v.mass j * s.p j : ℝ) : ℂ)) * (s.h t)ᴴ) i k) := by
            rw [hphys]
      _ = ((v.liftState s).g x z).im := by
            rw [hward]
            simp [i, k, PortMap.liftState, matrixIm,
              Complex.im_ofReal_mul, Complex.re_ofReal_mul]
  exact hmatrix

theorem port_ward_proof : ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0,
    ∀ (m n : ℕ) (t : ℝ) (M : RMat (Fin m)) (r : Fin m → ℂ)
      (v : PortMap (Fin n) (Fin m)),
      0 < t → M.IsSymm →
      (∀ i, 1 / C ≤ (r i).im ∧ (r i).im ≤ C ∧ 1 / C ≤ v.mass i) →
      (∀ x, 1 / C ≤ v.weight x ∧ v.weight x ≤ 1) →
      let s := v.liftState (physicalPrefix t M r v)
      s.ward t ∧ ‖s.h t‖ ≤ C' / Real.sqrt t := by
  intro C hC
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  refine ⟨C ^ 3, pow_pos hCpos 3, ?_⟩
  intro m n t M r v ht hM hbounds hweight
  let sp : State (Fin m) := physicalPrefix t M r v
  let s : State (Fin n) := v.liftState sp
  change s.ward t ∧ ‖s.h t‖ ≤ C ^ 3 / Real.sqrt t
  have hmassPos : ∀ i, 0 < v.mass i := by
    intro i
    exact lt_of_lt_of_le (one_div_pos.mpr hCpos) (hbounds i).2.2
  have hrPos : ∀ i, 0 < (r i).im := by
    intro i
    exact lt_of_lt_of_le (one_div_pos.mpr hCpos) (hbounds i).1
  have hphysWard :
      sp.h t * diagonal (fun i => ((v.mass i * sp.p i : ℝ) : ℂ)) * (sp.h t)ᴴ =
        matrixIm sp.g := by
    let D : CMat (Fin m) :=
      diagonal (fun i => ((v.mass i * sp.p i : ℝ) : ℂ))
    let Dt : CMat (Fin m) :=
      diagonal (fun i => ((t * v.mass i * sp.p i : ℝ) : ℂ))
    have hsqrtt : Real.sqrt t * Real.sqrt t = t := by
      simpa [pow_two] using Real.sq_sqrt ht.le
    have hscale :
        sp.h t * D * (sp.h t)ᴴ =
          (t : ℂ) • (sp.g * D * sp.gᴴ) := by
      simp [D, sp, State.h, physicalPrefix, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.conjTranspose_smul, Matrix.mul_assoc,
        Complex.star_def, smul_smul]
      rw [hsqrtt]
    have hdiagScale : (t : ℂ) • D = Dt := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [D, Dt, Matrix.diagonal, smul_eq_mul]
        ring
      · simp [D, Dt, Matrix.diagonal, hij]
    have hres := physical_resolvent_ward M t r v.mass ht hM hmassPos hrPos
    calc
      _ = (t : ℂ) • (sp.g * D * sp.gᴴ) := hscale
      _ = sp.g * ((t : ℂ) • D) * sp.gᴴ := by
            simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = sp.g * Dt * sp.gᴴ := by rw [hdiagScale]
      _ = matrixIm sp.g := by
            simpa [sp, physicalPrefix, State.p, Dt] using hres
  have hward : s.ward t := lift_mass_ward v sp t hphysWard
  have hspLower : ∀ i, 1 / C ≤ sp.p i := by
    intro i
    simpa [sp, physicalPrefix, State.p] using (hbounds i).1
  have hvirtLower : ∀ x, 1 / C ^ 3 ≤ s.p x := by
    intro x
    rw [show s = v.liftState sp by rfl, lift_p_entry]
    have hp := hspLower (v.site x)
    have hlow : 0 ≤ 1 / C := one_div_nonneg.mpr hCpos.le
    have hwpos : 0 ≤ v.weight x := le_trans hlow (hweight x).1
    have hw2 : (1 / C) ^ 2 ≤ v.weight x ^ 2 :=
      (sq_le_sq₀ hlow hwpos).2 (hweight x).1
    have hprod := mul_le_mul hw2 hp (by positivity) (sq_nonneg (v.weight x))
    calc
      1 / C ^ 3 = (1 / C) ^ 2 * (1 / C) := by
        field_simp [hCpos.ne']
      _ ≤ v.weight x ^ 2 * sp.p (v.site x) := hprod
  have hsymm : s.g.IsSymm := by
    have hspSymm : sp.g.IsSymm := by
      simpa [sp, physicalPrefix] using
        physical_damped_matrix_inverse_isSymm M t r v.mass hM
    exact lift_g_isSymm v sp hspSymm
  have hcpos : 0 < 1 / C ^ 3 := one_div_pos.mpr (pow_pos hCpos 3)
  have hnorm' := ward_l2_opNorm_bound (s.h t) s.g s.p t (1 / C ^ 3)
    ht hcpos hvirtLower hward hsymm rfl
  have hnorm : ‖s.h t‖ ≤ C ^ 3 / Real.sqrt t := by
    have heq : 1 / ((1 / C ^ 3) * Real.sqrt t) = C ^ 3 / Real.sqrt t := by
      field_simp [hCpos.ne', (Real.sqrt_pos.2 ht).ne']
    calc
      ‖s.h t‖ ≤ 1 / ((1 / C ^ 3) * Real.sqrt t) := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hnorm'
      _ = C ^ 3 / Real.sqrt t := heq
  exact ⟨hward, hnorm⟩

end AndersonAC.AgentS45
