import AndersonAC.S45.Definitions

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators

namespace AndersonAC.AgentS45

open AndersonAC.S45

private def coordinateSum {I : Type*} [Fintype I] : (I → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ i, v i
  map_add' v w := by simp [Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.mul_sum]

private def neutralSubspace (I : Type*) [Fintype I] : Submodule ℝ (I → ℝ) :=
  (coordinateSum (I := I)).ker

private theorem finrank_neutralSubspace {I : Type*} [Fintype I]
    (hI : Nonempty I) : Module.finrank ℝ (neutralSubspace I) + 1 = Fintype.card I := by
  have hsum : coordinateSum (I := I) ≠ 0 := by
    intro hz
    have h0 := congrArg (fun f : (I → ℝ) →ₗ[ℝ] ℝ => f (fun _ : I => (1 : ℝ))) hz
    have hcard : (Fintype.card I : ℝ) = 0 := by
      simpa [coordinateSum] using h0
    have hp : 0 < (Fintype.card I : ℝ) :=
      Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr hI)
    exact (ne_of_gt hp) hcard
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero hsum
  calc
    Module.finrank ℝ (neutralSubspace I) + 1 =
        Module.finrank ℝ (coordinateSum (I := I)).ker + 1 := by rfl
    _ = Module.finrank ℝ (I → ℝ) := h
    _ = Fintype.card I := by simpa using (Module.finrank_pi (R := ℝ) (ι := I))

private abbrev LocalPair {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] (Q : LocalCube P I) :=
  (Q.ports → ℝ) × neutralSubspace Q.outer

private def localPairInner {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] (Q : LocalCube P I) (b : ℝ)
    (x y : LocalPair Q) : ℝ :=
  dotProduct x.1 y.1 +
    dotProduct (laplacian Q.edge *ᵥ (x.2 : Q.outer → ℝ)) (y.2 : Q.outer → ℝ) / b

private theorem localPairInner_self {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] (Q : LocalCube P I) (b : ℝ)
    (x : LocalPair Q) :
    localPairInner Q b x x = Q.energy b x.1 (x.2 : Q.outer → ℝ) := by
  simp [localPairInner, LocalCube.energy, qform, l2sq, dotProduct, pow_two, mul_comm]

private noncomputable def localPair_core {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] (Q : LocalCube P I) (b : ℝ)
    (hb : 0 < b) (hI : Nonempty Q.outer)
    (he : constantKernel (laplacian Q.edge)) :
    InnerProductSpace.Core ℝ (LocalPair Q) := by
  classical
  letI : Inner ℝ (LocalPair Q) := ⟨localPairInner Q b⟩
  let pc : PreInnerProductSpace.Core ℝ (LocalPair Q) := by
    refine {
      inner := localPairInner Q b
      conj_inner_symm := ?_
      re_inner_nonneg := ?_
      add_left := ?_
      smul_left := ?_
    }
    · intro x y
      change localPairInner Q b y x = localPairInner Q b x y
      have hedge :
          dotProduct (laplacian Q.edge *ᵥ (y.2 : Q.outer → ℝ)) (x.2 : Q.outer → ℝ) =
            dotProduct (laplacian Q.edge *ᵥ (x.2 : Q.outer → ℝ)) (y.2 : Q.outer → ℝ) := by
        rw [dotProduct_comm, he.1.dotProduct_mulVec_comm, dotProduct_comm]
      simp [localPairInner, hedge, dotProduct_comm]
    · intro x
      change 0 ≤ localPairInner Q b x x
      rw [localPairInner_self]
      apply add_nonneg
      · exact Finset.sum_nonneg fun i _ => sq_nonneg ‖x.1 i‖
      · exact div_nonneg (he.2.1 (x.2 : Q.outer → ℝ)) hb.le
    · intro x y z
      simp [localPairInner, Matrix.mulVec_add, add_div, add_assoc, add_left_comm, add_comm]
    · intro x y r
      simp [localPairInner, Matrix.mulVec_smul, dotProduct_smul,
        Finset.smul_sum, mul_div_assoc, mul_add, mul_assoc]
  refine { pc with definite := ?_ }
  intro x hx
  change localPairInner Q b x x = 0 at hx
  have hx0 : localPairInner Q b x x = 0 := hx
  rw [localPairInner_self] at hx0
  rw [LocalCube.energy] at hx0
  have hαnonneg : 0 ≤ l2sq x.1 := Finset.sum_nonneg fun i _ => sq_nonneg ‖x.1 i‖
  have hvnonneg : 0 ≤ qform (laplacian Q.edge) (x.2 : Q.outer → ℝ) :=
    he.2.1 (x.2 : Q.outer → ℝ)
  have hαzero : l2sq x.1 = 0 := by
    have hdiv : 0 ≤ qform (laplacian Q.edge) (x.2 : Q.outer → ℝ) / b :=
      div_nonneg hvnonneg hb.le
    nlinarith
  have hvzero : qform (laplacian Q.edge) (x.2 : Q.outer → ℝ) = 0 := by
    have hdiv : 0 ≤ qform (laplacian Q.edge) (x.2 : Q.outer → ℝ) / b :=
      div_nonneg hvnonneg hb.le
    have hsum : l2sq x.1 + qform (laplacian Q.edge) (x.2 : Q.outer → ℝ) / b = 0 := hx0
    rw [hαzero, zero_add] at hsum
    exact (div_eq_zero_iff).mp hsum |>.resolve_right hb.ne'
  have hα : x.1 = 0 := by
    funext i
    have hterm : (x.1 i) ^ 2 ≤ l2sq x.1 := by
      rw [l2sq]
      calc
        (x.1 i) ^ 2 = ‖x.1 i‖ ^ 2 := by simp [Real.norm_eq_abs, sq_abs]
        _ ≤ ∑ j, ‖x.1 j‖ ^ 2 :=
          Finset.single_le_sum (fun j _ => sq_nonneg ‖x.1 j‖) (Finset.mem_univ i)
    have hsq : (x.1 i) ^ 2 = 0 := by nlinarith [hterm, hαzero]
    exact (sq_eq_zero_iff.mp hsq)
  obtain ⟨c, hc⟩ := (he.2.2 (x.2 : Q.outer → ℝ)).mp hvzero
  have hsum0 : ∑ i, (x.2 : Q.outer → ℝ) i = 0 := by
    have hp : coordinateSum (I := Q.outer) (x.2 : Q.outer → ℝ) = 0 := x.2.property
    simpa [coordinateSum] using hp
  have hcardc : (Fintype.card Q.outer : ℝ) * c = 0 := by
    calc
      (Fintype.card Q.outer : ℝ) * c = ∑ i : Q.outer, c := by simp
      _ = ∑ i, (x.2 : Q.outer → ℝ) i :=
        Finset.sum_congr rfl fun i _ => (hc i).symm
      _ = 0 := hsum0
  have hcardpos : 0 < (Fintype.card Q.outer : ℝ) :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr hI)
  have hc0 : c = 0 := (mul_eq_zero.mp hcardc).resolve_left (ne_of_gt hcardpos)
  have hv : (x.2 : Q.outer → ℝ) = 0 := by
    funext i
    rw [hc i, hc0]
    rfl
  apply Prod.ext
  · exact hα
  · exact Subtype.ext hv

set_option maxHeartbeats 500000 in
theorem local_coordinates_exist_proof {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] (Q : LocalCube P I) (b : ℝ)
    (hb : 0 < b) (hQ : Q.outer.Nonempty) (he : constantKernel (laplacian Q.edge)) :
    Nonempty (LocalCoordinates Q b (Q.ports.card + Q.outer.card - 1)) := by
  classical
  let V := LocalPair Q
  have hOuter : Nonempty Q.outer := ⟨⟨hQ.choose, hQ.choose_spec⟩⟩
  have hsub : Module.finrank ℝ (neutralSubspace Q.outer) + 1 = Q.outer.card := by
    simpa using finrank_neutralSubspace (I := Q.outer) hOuter
  have hsub' : Module.finrank ℝ (neutralSubspace Q.outer) = Q.outer.card - 1 := by omega
  have hdim : Module.finrank ℝ V = Q.ports.card + Q.outer.card - 1 := by
    rw [Module.finrank_prod, Module.finrank_pi, hsub']
    simp only [Fintype.card_coe]
    omega
  let core := localPair_core Q b hb hOuter he
  letI : InnerProductSpace.Core ℝ V := core
  let nscg : NormedAddCommGroup V := core.toNormedAddCommGroup
  letI : NormedAddCommGroup V := nscg
  letI : SeminormedAddCommGroup V := nscg.toSeminormedAddCommGroup
  letI : InnerProductSpace ℝ V :=
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ V)
  let basis : OrthonormalBasis (Fin (Q.ports.card + Q.outer.card - 1)) ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (finCongr hdim)
  let alpha : Matrix Q.ports (Fin (Q.ports.card + Q.outer.card - 1)) ℝ :=
    fun i j => (basis j).1 i
  let potential : Matrix Q.outer (Fin (Q.ports.card + Q.outer.card - 1)) ℝ :=
    fun i j => ((basis j).2 : Q.outer → ℝ) i
  let fstLin : V →ₗ[ℝ] (Q.ports → ℝ) := LinearMap.fst ℝ _ _
  let sndLin : V →ₗ[ℝ] (Q.outer → ℝ) :=
    (neutralSubspace Q.outer).subtype.comp (LinearMap.snd ℝ _ _)
  have hpotential (w : Fin (Q.ports.card + Q.outer.card - 1) → ℝ) :
      neutral (potential *ᵥ w) := by
    classical
    unfold neutral
    calc
      (∑ i : Q.outer, (potential *ᵥ w) i) =
          ∑ i : Q.outer, ∑ j, potential i j * w j := by
            simp [Matrix.mulVec, dotProduct]
      _ = ∑ j, ∑ i : Q.outer, potential i j * w j := Finset.sum_comm
      _ = ∑ j, w j * ∑ i : Q.outer, potential i j := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mul_sum]
            simp_rw [mul_comm (potential _ j) (w j)]
      _ = 0 := by
            apply Finset.sum_eq_zero
            intro j hj
            have hz : ∑ i : Q.outer, potential i j = 0 := by
              change coordinateSum (I := Q.outer) ((basis j).2 : Q.outer → ℝ) = 0
              exact (basis j).2.property
            rw [hz]
            simp
  let makePair (w : Fin (Q.ports.card + Q.outer.card - 1) → ℝ) : V :=
    (alpha *ᵥ w, ⟨potential *ᵥ w, hpotential w⟩)
  have hmake (w : Fin (Q.ports.card + Q.outer.card - 1) → ℝ) :
      makePair w = basis.repr.symm (WithLp.toLp 2 w) := by
    apply Prod.ext
    · funext i
      have hs := basis.sum_repr_symm (WithLp.toLp 2 w)
      have hi : ∑ j, w j • (basis j).1 =
          (basis.repr.symm (WithLp.toLp 2 w)).1 := by
        have h := congrArg fstLin hs
        rw [map_sum] at h
        change ∑ j, w j • (basis j).1 =
          (basis.repr.symm (WithLp.toLp 2 w)).1 at h
        exact h
      change ∑ j, (basis j).1 i * w j =
        (basis.repr.symm (WithLp.toLp 2 w)).1 i
      simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using congrFun hi i
    · apply Subtype.ext
      funext i
      have hs := basis.sum_repr_symm (WithLp.toLp 2 w)
      have hi : ∑ j, w j • ((basis j).2 : Q.outer → ℝ) =
          ((basis.repr.symm (WithLp.toLp 2 w)).2 : Q.outer → ℝ) := by
        have h := congrArg sndLin hs
        rw [map_sum] at h
        change ∑ j, w j • ((basis j).2 : Q.outer → ℝ) =
          ((basis.repr.symm (WithLp.toLp 2 w)).2 : Q.outer → ℝ) at h
        exact h
      change ∑ j, ((basis j).2 : Q.outer → ℝ) i * w j =
        ((basis.repr.symm (WithLp.toLp 2 w)).2 : Q.outer → ℝ) i
      simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using congrFun hi i
  have hcomplete (α : Q.ports → ℝ) (v : Q.outer → ℝ) (hv : neutral v) :
      ∃ w, alpha *ᵥ w = α ∧ potential *ᵥ w = v := by
    let x : V := (α, ⟨v, by
      change coordinateSum (I := Q.outer) v = 0
      exact hv⟩)
    let w : Fin (Q.ports.card + Q.outer.card - 1) → ℝ := basis.repr x
    refine ⟨w, ?_, ?_⟩
    · have hs := basis.sum_repr x
      have hi : ∑ j, w j • (basis j).1 = α := by
        have h := congrArg fstLin hs
        rw [map_sum] at h
        change ∑ j, w j • (basis j).1 = α at h
        exact h
      ext i
      change ∑ j, (basis j).1 i * w j = α i
      simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using congrFun hi i
    · have hs := basis.sum_repr x
      have hi : ∑ j, w j • ((basis j).2 : Q.outer → ℝ) = v := by
        have h := congrArg sndLin hs
        rw [map_sum] at h
        change ∑ j, w j • ((basis j).2 : Q.outer → ℝ) = v at h
        exact h
      ext i
      change ∑ j, ((basis j).2 : Q.outer → ℝ) i * w j = v i
      simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using congrFun hi i
  refine ⟨{
    alpha := alpha
    potential := potential
    neutral_potential := hpotential
    normalized := ?_
    complete := hcomplete
  }⟩
  intro w
  change Q.energy b (makePair w).1 (makePair w).2 = l2sq w
  rw [← localPairInner_self Q b (makePair w)]
  rw [hmake]
  have hinner : localPairInner Q b
      (basis.repr.symm (WithLp.toLp 2 w))
      (basis.repr.symm (WithLp.toLp 2 w)) = l2sq w := by
    have hmap : inner ℝ (basis.repr.symm (WithLp.toLp 2 w))
        (basis.repr.symm (WithLp.toLp 2 w)) =
        inner ℝ (WithLp.toLp 2 w) (WithLp.toLp 2 w) := by
      simpa only [LinearIsometryEquiv.apply_symm_apply] using (basis.repr.inner_map_map
        (basis.repr.symm (WithLp.toLp 2 w))
        (basis.repr.symm (WithLp.toLp 2 w))).symm
    change inner ℝ (basis.repr.symm (WithLp.toLp 2 w))
      (basis.repr.symm (WithLp.toLp 2 w)) = l2sq w
    rw [hmap, real_inner_self_eq_norm_sq]
    simpa [l2sq, Real.norm_eq_abs, sq_abs] using
      (PiLp.norm_sq_eq_of_L2 (fun _ : Fin (Q.ports.card + Q.outer.card - 1) => ℝ)
        (WithLp.toLp 2 w))
  exact hinner

private theorem dualForm_qform_of_solve {I : Type*} [Fintype I] [DecidableEq I]
    (A : RMat I) (y x : I → ℝ) (hA : A.IsSymm)
    (hpos : ∀ f, 0 ≤ qform A f) (hsolve : A *ᵥ x = y) :
    dualForm (qform A) y = qform A x := by
  classical
  let S : Set ℝ := {a | ∃ f : I → ℝ, a = 2 * dotProduct y f - qform A f}
  have hsymcross (f : I → ℝ) :
      dotProduct x (A *ᵥ f) = dotProduct f y := by
    calc
      dotProduct x (A *ᵥ f) = dotProduct f (A *ᵥ x) :=
        (hA.dotProduct_mulVec_comm).symm
      _ = dotProduct f y := by rw [hsolve]
  have hq : qform A x = dotProduct y x := by
    calc
      qform A x = dotProduct x (A *ᵥ x) := rfl
      _ = dotProduct x y := by rw [hsolve]
      _ = dotProduct y x := dotProduct_comm _ _
  have hcross (f : I → ℝ) :
      qform A (f - x) = qform A f + qform A x - 2 * dotProduct y f := by
    calc
      qform A (f - x) = dotProduct (f - x) (A *ᵥ (f - x)) := rfl
      _ = dotProduct f (A *ᵥ f) - dotProduct f (A *ᵥ x) -
          dotProduct x (A *ᵥ f) + dotProduct x (A *ᵥ x) := by
            simp only [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub]
            ring
      _ = qform A f + qform A x - 2 * dotProduct y f := by
            rw [hsolve, hsymcross, hq, dotProduct_comm y f]
            simp only [qform, dotProduct]
            have hsumxy : (∑ i, x i * y i) = ∑ i, y i * x i := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
            rw [hsumxy]
            ring
  have hbound (f : I → ℝ) :
      2 * dotProduct y f - qform A f ≤ qform A x := by
    have hp := hpos (f - x)
    rw [hcross] at hp
    nlinarith
  have hbdd : BddAbove S := by
    refine ⟨qform A x, ?_⟩
    rintro a ⟨f, rfl⟩
    exact hbound f
  have hmem : qform A x ∈ S := by
    refine ⟨x, ?_⟩
    rw [hq]
    ring
  have hs := le_antisymm
    (csSup_le ⟨qform A x, hmem⟩
      (by rintro a ⟨f, rfl⟩; exact hbound f))
    (le_csSup hbdd hmem)
  simpa [dualForm, S, dotProduct] using hs

private theorem constantKernel_solve {I : Type*} [Fintype I] [DecidableEq I]
    (A : RMat I) (y : I → ℝ) (hA : constantKernel A) (hy : neutral y) :
    ∃ x, A *ᵥ x = y := by
  classical
  by_cases hcard0 : Fintype.card I = 0
  · haveI : IsEmpty I := Fintype.card_eq_zero_iff.mp hcard0
    refine ⟨0, ?_⟩
    ext i
    exact isEmptyElim i
  · haveI : Nonempty I := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hcard0)
    let n : ℝ := Fintype.card I
    have hn : 0 < n := by dsimp [n]; exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcard0)
    let oneV : I → ℝ := fun _ => 1
    let J : RMat I := fun _ _ => n⁻¹
    let T : RMat I := A + J
    have hJmul (v : I → ℝ) (i : I) :
        (J *ᵥ v) i = (∑ j, v j) / n := by
      simp only [J, Matrix.mulVec, dotProduct, div_eq_mul_inv]
      calc
        (∑ j, n⁻¹ * v j) = ∑ j, v j * n⁻¹ := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = (∑ j, v j) * n⁻¹ := by rw [Finset.sum_mul]
        _ = (∑ j, v j) / n := by rw [div_eq_mul_inv]
    have hJquad (v : I → ℝ) :
        dotProduct v (J *ᵥ v) = (∑ i, v i) ^ 2 / n := by
      rw [show J *ᵥ v = fun _ => (∑ i, v i) / n by
        funext i; exact hJmul v i]
      simp only [dotProduct]
      rw [← Finset.sum_mul]
      ring
    have hJsymm : J.IsSymm := by
      apply Matrix.IsSymm.ext
      intro i j
      rfl
    have hTsymm : T.IsSymm := hA.1.add hJsymm
    have hTpos : T.PosDef := by
      rw [Matrix.posDef_iff_dotProduct_mulVec]
      constructor
      · simpa [Matrix.isHermitian_iff_isSymm] using hTsymm
      · intro v hv
        have hqA : 0 ≤ qform A v := hA.2.1 v
        have hqJ : 0 ≤ (∑ i, v i) ^ 2 / n := div_nonneg (sq_nonneg _) hn.le
        have hdecomp : dotProduct v (T *ᵥ v) = qform A v + (∑ i, v i) ^ 2 / n := by
          calc
            dotProduct v (T *ᵥ v) =
                dotProduct v (A *ᵥ v) + dotProduct v (J *ᵥ v) := by
                  simp [T, Matrix.add_mulVec, dotProduct_add]
            _ = qform A v + (∑ i, v i) ^ 2 / n := by
                  rw [← hJquad]
                  simp [qform, dotProduct]
        by_cases hq0 : qform A v = 0
        · obtain ⟨c, hc⟩ := (hA.2.2 v).mp hq0
          have hcne : c ≠ 0 := by
            intro hc0
            apply hv
            funext i
            rw [hc i, hc0]
            rfl
          have hsum : (∑ i, v i) = n * c := by
            calc
              (∑ i, v i) = ∑ i, c := Finset.sum_congr rfl (fun i _ => hc i)
              _ = n * c := by simp [n]
          have hsumne : (∑ i, v i) ≠ 0 := by
            rw [hsum]
            exact mul_ne_zero (ne_of_gt hn) hcne
          change 0 < dotProduct v (T *ᵥ v)
          rw [hdecomp, hq0, zero_add]
          exact div_pos (sq_pos_of_ne_zero hsumne) hn
        · have hqpos : 0 < qform A v := lt_of_le_of_ne hqA (Ne.symm hq0)
          change 0 < dotProduct v (T *ᵥ v)
          rw [hdecomp]
          exact add_pos_of_pos_of_nonneg hqpos hqJ
    have hTunit : IsUnit T := hTpos.isUnit
    have hTdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hTunit
    let z : I → ℝ := T⁻¹ *ᵥ y
    have hz : T *ᵥ z = y := by
      calc
        T *ᵥ z = T *ᵥ (T⁻¹ *ᵥ y) := rfl
        _ = (T * T⁻¹) *ᵥ y := by rw [← Matrix.mulVec_mulVec]
        _ = (1 : RMat I) *ᵥ y := by rw [T.mul_nonsing_inv hTdet]
        _ = y := Matrix.one_mulVec _
    have hAone : A *ᵥ oneV = 0 := by
      have hq0 : qform A oneV = 0 :=
        (hA.2.2 oneV).2 ⟨1, fun _ => rfl⟩
      have hPSD : A.PosSemidef := by
        rw [Matrix.posSemidef_iff_dotProduct_mulVec]
        exact ⟨by simpa [Matrix.isHermitian_iff_isSymm] using hA.1,
          fun v => by simpa only [qform, dotProduct, star_trivial] using hA.2.1 v⟩
      have hdot : dotProduct oneV (A *ᵥ oneV) = 0 := by
        have hq0' : ∑ i, (A *ᵥ oneV) i = 0 := by simpa [qform, oneV] using hq0
        simpa [dotProduct, oneV] using hq0'
      exact (hPSD.dotProduct_mulVec_zero_iff).mp (by simpa [oneV] using hdot)
    have hsumA : ∑ i, (A *ᵥ z) i = 0 := by
      calc
        (∑ i, (A *ᵥ z) i) = dotProduct oneV (A *ᵥ z) := by simp [dotProduct, oneV]
        _ = dotProduct z (A *ᵥ oneV) := hA.1.dotProduct_mulVec_comm
        _ = 0 := by rw [hAone]; simp [dotProduct]
    have hsumY : ∑ i, y i = 0 := by simpa [neutral] using hy
    have hsumJ : ∑ i, (J *ᵥ z) i = ∑ i, z i := by
      rw [show J *ᵥ z = fun _ => (∑ i, z i) / n by
        funext i; exact hJmul z i]
      simp [n, div_eq_mul_inv]
      field_simp [ne_of_gt hn]
    have hsumZ : ∑ i, z i = 0 := by
      have hzadd : A *ᵥ z + J *ᵥ z = y := by
        simpa [T, Matrix.add_mulVec] using hz
      have hsumEq := congrArg (fun v : I → ℝ => ∑ i, v i) hzadd
      simp only [Pi.add_apply] at hsumEq
      rw [Finset.sum_add_distrib, hsumA, zero_add, hsumJ, hsumY] at hsumEq
      exact hsumEq
    have hJz : J *ᵥ z = 0 := by
      funext i
      rw [hJmul z i, hsumZ]
      simp
    have hsolve : A *ᵥ z = y := by
      have h := hz
      simpa [T, Matrix.add_mulVec, hJz] using h
    exact ⟨z, hsolve⟩

private theorem qform_sub_of_solve {I : Type*} [Fintype I]
    (A : RMat I) (y x f : I → ℝ) (hA : A.IsSymm)
    (hsolve : A *ᵥ x = y) :
    qform A (f - x) = qform A f + qform A x - 2 * dotProduct y f := by
  have hcross : dotProduct x (A *ᵥ f) = dotProduct f y := by
    calc
      dotProduct x (A *ᵥ f) = dotProduct f (A *ᵥ x) :=
        (hA.dotProduct_mulVec_comm).symm
      _ = dotProduct f y := by rw [hsolve]
  have hq : qform A x = dotProduct y x := by
    calc
      qform A x = dotProduct x (A *ᵥ x) := rfl
      _ = dotProduct x y := by rw [hsolve]
      _ = dotProduct y x := dotProduct_comm _ _
  calc
    qform A (f - x) = qform A f - dotProduct f (A *ᵥ x) -
        dotProduct x (A *ᵥ f) + qform A x := by
          calc
            qform A (f - x) =
                ∑ i, (f i - x i) * ((A *ᵥ f) i - (A *ᵥ x) i) := by
                  simp [qform, Matrix.mulVec_sub]
            _ = ∑ i, (f i * (A *ᵥ f) i - f i * (A *ᵥ x) i -
                x i * (A *ᵥ f) i + x i * (A *ᵥ x) i) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
            _ = qform A f - dotProduct f (A *ᵥ x) -
                dotProduct x (A *ᵥ f) + qform A x := by
                  simp [qform, dotProduct, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = qform A f + qform A x - 2 * dotProduct y f := by
          rw [hsolve, hcross, hq, dotProduct_comm y f]
          ring

private theorem qform_smul_sq {I : Type*} [Fintype I] (A : RMat I)
    (r : ℝ) (v : I → ℝ) : qform A (r • v) = r ^ 2 * qform A v := by
  simp only [qform, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem qform_add {I : Type*} [Fintype I] (A B : RMat I) (f : I → ℝ) :
    qform (A + B) f = qform A f + qform B f := by
  calc
    qform (A + B) f = dotProduct f ((A + B) *ᵥ f) := rfl
    _ = dotProduct f (A *ᵥ f + B *ᵥ f) := by rw [Matrix.add_mulVec]
    _ = dotProduct f (A *ᵥ f) + dotProduct f (B *ᵥ f) := dotProduct_add _ _ _
    _ = qform A f + qform B f := rfl

private theorem qform_variational_bound {I : Type*} [Fintype I]
    (A : RMat I) (y x f : I → ℝ) (hA : A.IsSymm)
    (hpos : ∀ v, 0 ≤ qform A v) (hsolve : A *ᵥ x = y) :
    2 * dotProduct y f - qform A f ≤ qform A x := by
  have h := hpos (f - x)
  rw [qform_sub_of_solve A y x f hA hsolve] at h
  nlinarith

private def pushSite {P I : Type*} [Fintype P] [DecidableEq I]
    (site : P → I) (y : P → ℝ) : I → ℝ :=
  fun i => ∑ x, if site x = i then y x else 0

private theorem pushSite_neutral {P I : Type*} [Fintype P] [Fintype I] [DecidableEq I]
    (site : P → I) (y : P → ℝ) (hy : neutral y) : neutral (pushSite site y) := by
  classical
  unfold neutral pushSite
  calc
    (∑ i, ∑ x, if site x = i then y x else 0) =
        ∑ x, ∑ i, if site x = i then y x else 0 := Finset.sum_comm
    _ = ∑ x, y x := by
        apply Finset.sum_congr rfl
        intro x hx
        simp
    _ = 0 := by simpa [neutral] using hy

private theorem pushSite_dot {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq I]
    (site : P → I) (y : P → ℝ) (v : I → ℝ) :
    dotProduct y (fun x => v (site x)) = dotProduct (pushSite site y) v := by
  classical
  unfold pushSite
  simp only [dotProduct]
  calc
    (∑ x, y x * v (site x)) =
        ∑ x, ∑ i, (if site x = i then y x else 0) * v i := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [Finset.sum_ite_eq', eq_comm]
    _ = ∑ i, ∑ x, (if site x = i then y x else 0) * v i := Finset.sum_comm
    _ = ∑ i, (∑ x, if site x = i then y x else 0) * v i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul]
    _ = dotProduct (fun i => ∑ x, if site x = i then y x else 0) v := rfl

private theorem l2sq_sub_formula {P : Type*} [Fintype P] (x y : P → ℝ) :
    l2sq (x - y) = l2sq x - 2 * dotProduct x y + l2sq y := by
  calc
    l2sq (x - y) = ∑ i, (x i - y i) ^ 2 := by
      simp [l2sq, Real.norm_eq_abs, sq_abs]
    _ = ∑ i, (x i ^ 2 - 2 * x i * y i + y i ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i, x i ^ 2) - 2 * (∑ i, x i * y i) + ∑ i, y i ^ 2 := by
      simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      ring
    _ = l2sq x - 2 * dotProduct x y + l2sq y := by
      simp [l2sq, dotProduct, Real.norm_eq_abs, sq_abs]

private theorem l2sq_smul_sq {P : Type*} [Fintype P] (r : ℝ) (v : P → ℝ) :
    l2sq (r • v) = r ^ 2 * l2sq v := by
  simp only [l2sq, Pi.smul_apply, smul_eq_mul, norm_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_abs r, sq_abs (v i)]

private theorem spatialDual_bddAbove {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq I] (site : P → I) (b : ℝ) (hb : 0 < b) (A : RMat I)
    (hA : constantKernel A) (y : P → ℝ) (hy : neutral y) :
    BddAbove {a : ℝ | ∃ f : P → ℝ,
      a = 2 * dotProduct y f - spatialEnergy site b (qform A) f} := by
  classical
  let c := pushSite site y
  have hc : neutral c := pushSite_neutral site y hy
  obtain ⟨z, hz⟩ := constantKernel_solve A c hA hc
  have hdual := dualForm_qform_of_solve A c z hA.1 hA.2.1 hz
  let K := l2sq y + b * dualForm (qform A) c
  have hV (v : I → ℝ) :
      2 * dotProduct c v - qform A v / b ≤ b * dualForm (qform A) c := by
    have hscaled : A *ᵥ (b • z) = b • c := by
      simp [Matrix.mulVec_smul, hz]
    have h := qform_variational_bound A (b • c) (b • z) v hA.1 hA.2.1 hscaled
    have hdot : dotProduct (b • c) v = b * dotProduct c v := by
      simp [smul_dotProduct, smul_eq_mul]
    rw [hdot, qform_smul_sq] at h
    rw [hdual]
    apply le_of_mul_le_mul_left ?_ hb
    calc
      b * (2 * dotProduct c v - qform A v / b) =
          2 * (b * dotProduct c v) - qform A v := by field_simp [hb.ne']
      _ ≤ b ^ 2 * qform A z := h
      _ = b * (b * qform A z) := by ring
  have hspatial (f : P → ℝ) :
      2 * dotProduct y f - K ≤ spatialEnergy site b (qform A) f := by
    let E : Set ℝ := {a | ∃ α : P → ℝ, ∃ v : I → ℝ,
      (∀ x, f x = α x + v (site x)) ∧ a = l2sq α + qform A v / b}
    have hEne : E.Nonempty := by
      refine ⟨l2sq f, f, 0, ?_, ?_⟩
      · intro x
        simp
      · simp [qform]
    have hlow : ∀ a ∈ E, 2 * dotProduct y f - K ≤ a := by
      rintro a ⟨α, v, hf, rfl⟩
      have hpair : dotProduct y f = dotProduct y α + dotProduct c v := by
        have hf' : f = α + (fun x => v (site x)) := funext hf
        calc
          dotProduct y f = dotProduct y (α + (fun x => v (site x))) := by rw [hf']
          _ = dotProduct y α + dotProduct y (fun x => v (site x)) :=
            dotProduct_add y α (fun x => v (site x))
          _ = dotProduct y α + dotProduct c v := by
            rw [pushSite_dot site y v]
      have hα : 2 * dotProduct y α - l2sq α ≤ l2sq y := by
        have hnonneg : 0 ≤ l2sq (α - y) := by
          exact Finset.sum_nonneg fun i _ => sq_nonneg ‖(α - y) i‖
        rw [l2sq_sub_formula] at hnonneg
        rw [dotProduct_comm α y] at hnonneg
        nlinarith
      have hv := hV v
      have hsum :
          2 * dotProduct y α + 2 * dotProduct c v -
            (l2sq α + qform A v / b) ≤ K := by
        dsimp [K]
        linarith
      nlinarith [hpair, hsum]
    change 2 * dotProduct y f - K ≤ sInf E
    exact le_csInf hEne hlow
  refine ⟨K, ?_⟩
  rintro a ⟨f, rfl⟩
  have hf := hspatial f
  dsimp [K]
  linarith

theorem local_pullback_proof {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] (Q : LocalCube P I) (b C : ℝ) (Λ : Form I)
    (Wstar : Form P) (h : ℕ) (a : LocalCoordinates Q b h) (hC : 0 ≤ C)
    (hb : 0 < b) (hΛ : ∃ A : RMat I, Λ = qform A ∧ constantKernel A)
    (hcutoff : ∀ α v, spatialEnergy Q.site b Λ (Q.extend α v) ≤ C * Q.energy b α v)
    (hduality : Wstar = dualForm (spatialEnergy Q.site b Λ)) :
    (∀ v, spatialEnergy Q.site b Λ (a.B *ᵥ v) ≤ C * l2sq v) ∧
    (∀ y, neutral y → l2sq (a.Bᵀ *ᵥ y) ≤ C * Wstar y) := by
  classical
  obtain ⟨A, rfl, hA⟩ := hΛ
  have hcol (j : Fin h) : ∑ i : Q.outer, a.potential i j = 0 := by
    have hn := a.neutral_potential (Pi.single j 1)
    have hv : a.potential *ᵥ Pi.single j 1 = a.potential.col j :=
      Matrix.mulVec_single_one a.potential j
    unfold neutral at hn
    rw [hv] at hn
    simpa [Matrix.col_apply] using hn
  have hpot0 (v : Fin h → ℝ) : ∑ i : Q.outer, (a.potential *ᵥ v) i = 0 := by
    have hn := a.neutral_potential v
    simpa [neutral] using hn
  have hBext (v : Fin h → ℝ) :
      a.B *ᵥ v = Q.extend (a.alpha *ᵥ v) (a.potential *ᵥ v) := by
    funext x
    change (∑ j, Q.extend (fun i => a.alpha i j) (fun i => a.potential i j) x * v j) =
      Q.extend (a.alpha *ᵥ v) (a.potential *ᵥ v) x
    by_cases hx : x ∈ Q.ports
    · simp only [LocalCube.extend]
      simp_rw [dif_pos hx]
      change (∑ j, Q.cutoff (Q.site x) *
          (a.alpha ⟨x, hx⟩ j + a.potential ⟨Q.site x, (Finset.mem_filter.mp hx).2⟩ j -
            (∑ i : Q.outer, a.potential i j) / Q.outer.card) * v j) =
        Q.cutoff (Q.site x) *
          ((a.alpha *ᵥ v) ⟨x, hx⟩ +
            (a.potential *ᵥ v) ⟨Q.site x, (Finset.mem_filter.mp hx).2⟩ -
            (∑ i : Q.outer, (a.potential *ᵥ v) i) / Q.outer.card)
      rw [hpot0 v]
      simp only [Matrix.mulVec, dotProduct]
      simp_rw [hcol]
      simp only [zero_div, sub_zero]
      calc
        _ = ∑ j,
              (Q.cutoff (Q.site x) * a.alpha ⟨x, hx⟩ j * v j +
                Q.cutoff (Q.site x) * a.potential ⟨Q.site x, (Finset.mem_filter.mp hx).2⟩ j * v j) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
        _ = (∑ j, Q.cutoff (Q.site x) * a.alpha ⟨x, hx⟩ j * v j) +
              ∑ j, Q.cutoff (Q.site x) * a.potential ⟨Q.site x, (Finset.mem_filter.mp hx).2⟩ j * v j :=
              Finset.sum_add_distrib
        _ = Q.cutoff (Q.site x) * (∑ j, a.alpha ⟨x, hx⟩ j * v j) +
              Q.cutoff (Q.site x) * (∑ j, a.potential ⟨Q.site x, (Finset.mem_filter.mp hx).2⟩ j * v j) := by
              have hα :
                  (∑ j, Q.cutoff (Q.site x) * a.alpha ⟨x, hx⟩ j * v j) =
                    Q.cutoff (Q.site x) * ∑ j, a.alpha ⟨x, hx⟩ j * v j := by
                calc
                  _ = ∑ j, Q.cutoff (Q.site x) * (a.alpha ⟨x, hx⟩ j * v j) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
                  _ = _ := by rw [Finset.mul_sum]
              have hp :
                  (∑ j, Q.cutoff (Q.site x) * a.potential ⟨Q.site x, (Finset.mem_filter.mp hx).2⟩ j * v j) =
                    Q.cutoff (Q.site x) * ∑ j, a.potential ⟨Q.site x, (Finset.mem_filter.mp hx).2⟩ j * v j := by
                calc
                  _ = ∑ j, Q.cutoff (Q.site x) *
                      (a.potential ⟨Q.site x, (Finset.mem_filter.mp hx).2⟩ j * v j) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
                  _ = _ := by rw [Finset.mul_sum]
              rw [hα, hp]
        _ = Q.cutoff (Q.site x) *
              ((∑ j, a.alpha ⟨x, hx⟩ j * v j) +
                ∑ j, a.potential ⟨Q.site x, (Finset.mem_filter.mp hx).2⟩ j * v j) := by ring
    · simp [LocalCube.extend, hx]
  have hfirst : ∀ v : Fin h → ℝ,
      spatialEnergy Q.site b (qform A) (a.B *ᵥ v) ≤ C * l2sq v := by
    intro v
    rw [hBext]
    calc
      spatialEnergy Q.site b (qform A) (Q.extend (a.alpha *ᵥ v) (a.potential *ᵥ v)) ≤
          C * Q.energy b (a.alpha *ᵥ v) (a.potential *ᵥ v) := hcutoff _ _
      _ = C * l2sq v := by rw [a.normalized]
  have hsecond : ∀ y, neutral y → l2sq (a.Bᵀ *ᵥ y) ≤ C * Wstar y := by
    intro y hy
    have hbd := spatialDual_bddAbove Q.site b hb A hA y hy
    have htest (v : Fin h → ℝ) :
        2 * dotProduct (a.Bᵀ *ᵥ y) v - C * l2sq v ≤ Wstar y := by
      let f := a.B *ᵥ v
      have hval : 2 * dotProduct y f -
          spatialEnergy Q.site b (qform A) f ≤ dualForm (spatialEnergy Q.site b (qform A)) y :=
        le_csSup hbd ⟨f, rfl⟩
      have hdot : dotProduct y f = dotProduct (a.Bᵀ *ᵥ y) v := by
        calc
          dotProduct y f = dotProduct v (a.Bᵀ *ᵥ y) :=
            (Matrix.dotProduct_transpose_mulVec a.B v y).symm
          _ = dotProduct (a.Bᵀ *ᵥ y) v := dotProduct_comm _ _
      rw [hduality]
      have hw := hfirst v
      dsimp [f] at hval hw
      nlinarith [hdot]
    let q := a.Bᵀ *ᵥ y
    have hsq : 0 ≤ l2sq q := Finset.sum_nonneg fun i _ => sq_nonneg ‖q i‖
    have hdotself : dotProduct q q = l2sq q := by
      calc
        dotProduct q q = ∑ i, q i ^ 2 := by simp [dotProduct, pow_two]
        _ = l2sq q := by simp [l2sq, Real.norm_eq_abs, sq_abs]
    have htestS (s : ℝ) : 2 * s * l2sq q - C * s ^ 2 * l2sq q ≤ Wstar y := by
      have ht := htest (s • q)
      rw [show dotProduct q (s • q) = s * l2sq q by
        simp [dotProduct_smul, hdotself], l2sq_smul_sq] at ht
      nlinarith
    by_cases hCpos : 0 < C
    · have ht := htestS (C⁻¹)
      have hinv : 0 < C⁻¹ := inv_pos.mpr hCpos
      have hcoeff : 2 * C⁻¹ - C * (C⁻¹) ^ 2 = C⁻¹ := by field_simp [hCpos.ne']; ring
      have hbound : C⁻¹ * l2sq q ≤ Wstar y := by nlinarith [ht, hcoeff]
      calc
        l2sq q = C * (C⁻¹ * l2sq q) := by field_simp [hCpos.ne']
        _ ≤ C * Wstar y := mul_le_mul_of_nonneg_left hbound hC
    · have hC0 : C = 0 := le_antisymm (not_lt.mp hCpos) hC
      by_cases hqpos : 0 < l2sq q
      · have ht := htestS ((Wstar y + 1) / (2 * l2sq q))
        rw [hC0] at ht
        have heq : 2 * ((Wstar y + 1) / (2 * l2sq q)) * l2sq q = Wstar y + 1 := by
          field_simp [ne_of_gt hqpos]
        rw [heq] at ht
        linarith
      · have hq0 : l2sq q = 0 := le_antisymm (not_lt.mp hqpos) hsq
        rw [hC0, hq0]
        simp
  exact ⟨hfirst, hsecond⟩

private noncomputable def finsetPartitionEquiv {P : Type*} [DecidableEq P]
    [Fintype P]
    (E : Finset P) : (↑E : Type _) ⊕ (↑(Eᶜ) : Type _) ≃ P := by
  classical
  refine {
    toFun := Sum.elim Subtype.val Subtype.val
    invFun := fun x => if hx : x ∈ E then Sum.inl ⟨x, hx⟩ else
      Sum.inr ⟨x, by simp [hx]⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro s
    cases s with
    | inl x => simp
    | inr x =>
        have hx : (x : P) ∉ E := Finset.mem_compl.mp x.property
        simp [hx]
  · intro x
    by_cases hx : x ∈ E <;> simp [hx]

private def schurCross {P : Type*} [Fintype P] [DecidableEq P]
    (A : RMat P) (E : Finset P) :
    Matrix (↑(Eᶜ) : Type _) (↑E : Type _) ℝ :=
  fun i j => A i.val j.val

private theorem schur_reindex_blocks {P : Type*} [Fintype P] [DecidableEq P]
    (A : RMat P) (E : Finset P) (hA : A.IsSymm) :
    Matrix.reindex (finsetPartitionEquiv E).symm (finsetPartitionEquiv E).symm A =
      Matrix.fromBlocks (restrict A E) (schurCross A E)ᵀ
        (schurCross A E) (restrict A Eᶜ) := by
  classical
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j => rfl
      | inr j =>
          simpa [finsetPartitionEquiv, schurCross, restrict, Matrix.reindex,
            Matrix.transpose_apply] using hA.apply j.val i.val
  | inr i =>
      cases j with
      | inl j => rfl
      | inr j => rfl

private theorem qform_reindex_partition {P : Type*} [Fintype P] [DecidableEq P]
    (A : RMat P) (E : Finset P) (u : (↑E : Type _) → ℝ)
    (v : (↑(Eᶜ) : Type _) → ℝ) :
    qform A (fun x => Sum.elim u v ((finsetPartitionEquiv E).symm x)) =
      qform (Matrix.reindex (finsetPartitionEquiv E).symm
        (finsetPartitionEquiv E).symm A) (Sum.elim u v) := by
  classical
  let e := finsetPartitionEquiv E
  let g : (↑E : Type _) ⊕ (↑(Eᶜ) : Type _) → ℝ := Sum.elim u v
  let f : P → ℝ := fun x => g (e.symm x)
  have hmul : Matrix.reindex e.symm e.symm A *ᵥ g =
      (A *ᵥ (g ∘ e.symm)) ∘ e := by
    change A.submatrix e e *ᵥ g = (A *ᵥ (g ∘ e.symm)) ∘ e
    exact Matrix.submatrix_mulVec_equiv A g e e
  change qform A f = qform (Matrix.reindex e.symm e.symm A) g
  calc
    qform A f = ∑ x, f x * (A *ᵥ f) x := rfl
    _ = ∑ s, f (e s) * (A *ᵥ f) (e s) := by
          exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
    _ = ∑ s, g s * (Matrix.reindex e.symm e.symm A *ᵥ g) s := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [show f (e s) = g s by simp [f]]
          have hmulS := congrFun hmul s
          change (Matrix.reindex e.symm e.symm A *ᵥ g) s = (A *ᵥ f) (e s) at hmulS
          rw [hmulS]
    _ = qform (Matrix.reindex e.symm e.symm A) g := rfl

private theorem qform_vecMul {I : Type*} [Fintype I] (A : RMat I) (x : I → ℝ) :
    qform A x = (star x) ᵥ* A ⬝ᵥ x := by
  calc
    qform A x = dotProduct x (A *ᵥ x) := rfl
    _ = x ᵥ* A ⬝ᵥ x := Matrix.dotProduct_mulVec x A x
    _ = (star x) ᵥ* A ⬝ᵥ x := by simp [star_trivial]

set_option maxHeartbeats 500000 in
private theorem schur_energy_completion {P : Type*} [Fintype P] [DecidableEq P]
    (A : RMat P) (E : Finset P) (hA : A.IsSymm)
    (hunit : IsUnit (restrict A E)) (u : (↑E : Type _) → ℝ)
    (v : (↑(Eᶜ) : Type _) → ℝ) :
    let f : P → ℝ := fun x => Sum.elim u v ((finsetPartitionEquiv E).symm x)
    qform A f =
      qform (restrict A E)
        (u + ((restrict A E)⁻¹ * (schurCross A E)ᵀ) *ᵥ v) +
        qform (schur A E) v := by
  classical
  let e := finsetPartitionEquiv E
  let g : (↑E : Type _) ⊕ (↑(Eᶜ) : Type _) → ℝ := Sum.elim u v
  let f : P → ℝ := fun x => g (e.symm x)
  let B := schurCross A E
  let D := restrict A Eᶜ
  let T := restrict A E
  letI : Invertible T := hunit.invertible
  have hTsymm : T.IsHermitian := by
    have hs : T.IsSymm := hA.submatrix Subtype.val
    simpa [Matrix.isHermitian_iff_isSymm] using hs
  have hblock : Matrix.reindex e.symm e.symm A = Matrix.fromBlocks T Bᵀ B D :=
    schur_reindex_blocks A E hA
  have hcrossR :
      A.submatrix (fun i : (↑E : Type _) => i.val)
        (fun i : (↑(Eᶜ) : Type _) => i.val) = Bᵀ := by
    ext i j
    change A i.val j.val = A j.val i.val
    exact (hA.apply i.val j.val).symm
  have hschur : schur A E = D - B * T⁻¹ * Bᵀ := by
    change restrict A Eᶜ -
      A.submatrix (fun i : (↑(Eᶜ) : Type _) => i.val) (fun i : E => i.val) *
        (restrict A E)⁻¹ * A.submatrix (fun i : E => i.val)
          (fun i : (↑(Eᶜ) : Type _) => i.val) = D - B * T⁻¹ * Bᵀ
    rw [hcrossR]
    rfl
  have hBstar : Bᵀᴴ = B := by
    ext i j
    simp [Matrix.conjTranspose, Matrix.transpose_apply, star_trivial, B, schurCross]
  have hmat := Matrix.schur_complement_eq₁₁ Bᵀ D u v hTsymm
  have hmat0 := hmat
  rw [hBstar] at hmat0
  have hmat' : (star g) ᵥ* (Matrix.fromBlocks T Bᵀ B D) ⬝ᵥ g =
      (star (u + (T⁻¹ * Bᵀ) *ᵥ v)) ᵥ* T ⬝ᵥ
          (u + (T⁻¹ * Bᵀ) *ᵥ v) + (star v) ᵥ* (D - B * T⁻¹ * Bᵀ) ⬝ᵥ v := by
    simpa [g, star_trivial] using hmat0
  have henergy : qform (Matrix.fromBlocks T Bᵀ B D) g =
      qform T (u + (T⁻¹ * Bᵀ) *ᵥ v) + qform (D - B * T⁻¹ * Bᵀ) v := by
    calc
      _ = (star g) ᵥ* (Matrix.fromBlocks T Bᵀ B D) ⬝ᵥ g := qform_vecMul _ _
      _ = _ := hmat'
      _ = _ := by rw [← qform_vecMul T, ← qform_vecMul (D - B * T⁻¹ * Bᵀ)]
  calc
    qform A f = qform (Matrix.reindex e.symm e.symm A) g := by
      simpa [e, f, g] using qform_reindex_partition A E u v
    _ = qform (Matrix.fromBlocks T Bᵀ B D) g := by rw [hblock]
    _ = qform T (u + (T⁻¹ * Bᵀ) *ᵥ v) + qform (schur A E) v := by
      rw [henergy, hschur]

private theorem constantKernel_restrict_posDef {P : Type*} [Fintype P] [DecidableEq P]
    (A : RMat P) (E : Finset P) (hA : constantKernel A)
    (hS : (Eᶜ).Nonempty) : (restrict A E).PosDef := by
  classical
  letI : Fintype (↑E : Type _) := Subtype.fintype (fun i : P => i ∈ E)
  letI : Fintype (↑(Eᶜ) : Type _) := Subtype.fintype (fun i : P => i ∈ Eᶜ)
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · have hs : (restrict A E).IsSymm := hA.1.submatrix Subtype.val
    simpa [Matrix.isHermitian_iff_isSymm] using hs
  · intro x hx
    let pad : P → ℝ := fun i => if hi : i ∈ E then x ⟨i, hi⟩ else 0
    have hrow (i : (↑E : Type _)) :
        (restrict A E *ᵥ x) i = (A *ᵥ pad) i.val := by
      have hsum :
          (∑ j : (↑E : Type _), A i.val j.val * x j) =
            ∑ j : P, A i.val j * pad j := by
        have hs := Fintype.sum_subtype_add_sum_subtype (fun j : P => j ∈ E)
          (fun j : P => A i.val j * pad j)
        have hcomp : ∑ j : {j : P // j ∉ E}, A i.val j.val * pad j.val = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          simp [pad, j.property]
        rw [hcomp, add_zero] at hs
        calc
          (∑ j : (↑E : Type _), A i.val j.val * x j) =
              ∑ j : (↑E : Type _), A i.val j.val * pad j.val := by
                apply Finset.sum_congr rfl
                intro j hj
                simp [pad, j.property]
          _ = ∑ j : P, A i.val j * pad j := hs
      simpa [restrict, Matrix.mulVec, dotProduct] using hsum
    have hqeq : qform (restrict A E) x = qform A pad := by
      have hsum : (∑ i : (↑E : Type _), pad i * (A *ᵥ pad) i.val) =
          ∑ i : P, pad i * (A *ᵥ pad) i := by
        have hs := Fintype.sum_subtype_add_sum_subtype (fun i : P => i ∈ E)
          (fun i : P => pad i * (A *ᵥ pad) i)
        have hcomp : ∑ i : {i : P // i ∉ E}, pad i.val * (A *ᵥ pad) i.val = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          simp [pad, i.property]
        rw [hcomp, add_zero] at hs
        exact hs
      calc
        qform (restrict A E) x = ∑ i : (↑E : Type _), x i * (restrict A E *ᵥ x) i := rfl
        _ = ∑ i : (↑E : Type _), pad i * (A *ᵥ pad) i := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi' : pad i = x i := by simp [pad, i.property]
          rw [hi', hrow i]
        _ = ∑ i : P, pad i * (A *ᵥ pad) i := hsum
        _ = qform A pad := rfl
    have hnonneg : 0 ≤ qform A pad := hA.2.1 pad
    have hqne : qform A pad ≠ 0 := by
      intro hq0
      obtain ⟨c, hc⟩ := (hA.2.2 pad).mp hq0
      let j0 : (↑(Eᶜ) : Type _) := ⟨hS.choose, hS.choose_spec⟩
      have hnot : (j0 : P) ∉ E := Finset.mem_compl.mp j0.property
      have hczero : c = 0 := by
        have hf0 : pad j0 = 0 := by simp [pad, hnot]
        rw [hc j0] at hf0
        exact hf0
      apply hx
      funext i
      have hfi : pad i.val = x i := by simp [pad, i.property]
      rw [hc i.val, hczero] at hfi
      exact hfi.symm
    have hqpos : 0 < qform A pad := lt_of_le_of_ne hnonneg (Ne.symm hqne)
    have hqpos' : 0 < qform (restrict A E) x := by rwa [hqeq]
    simpa [qform, dotProduct, star_trivial] using hqpos'

private theorem constantKernel_add_error {P : Type*} [Fintype P] [DecidableEq P]
    (D L : RMat P) (ε : ℝ) (hε : 0 ≤ ε ∧ ε < 1)
    (hD : constantKernel D) (hL : L.IsSymm)
    (hcap : formAbsLe (qform L) (qform D) ε) : constantKernel (D + L) := by
  constructor
  · exact hD.1.add hL
  constructor
  · intro f
    have hqD : 0 ≤ qform D f := hD.2.1 f
    have habs := abs_le.mp (hcap f)
    have hqsum : qform (D + L) f = qform D f + qform L f := qform_add D L f
    rw [hqsum]
    nlinarith [mul_nonneg hε.1 hqD]
  · intro f
    constructor
    · intro hzero
      have hqD : 0 ≤ qform D f := hD.2.1 f
      have habs := abs_le.mp (hcap f)
      have hqsum : qform (D + L) f = qform D f + qform L f := qform_add D L f
      have hDzero : qform D f = 0 := by
        rw [hqsum] at hzero
        nlinarith
      exact (hD.2.2 f).mp hDzero
    · rintro ⟨c, hc⟩
      have hDzero : qform D f = 0 := (hD.2.2 f).mpr ⟨c, hc⟩
      have hLzero : qform L f = 0 := by
        have habs0 : |qform L f| ≤ 0 := by simpa [hDzero] using hcap f
        exact abs_eq_zero.mp (le_antisymm habs0 (abs_nonneg _))
      rw [qform_add, hDzero, hLzero]
      simp

private theorem schur_block_eq {P : Type*} [Fintype P] [DecidableEq P]
    (A : RMat P) (E : Finset P) (hA : A.IsSymm) :
    schur A E = restrict A Eᶜ - schurCross A E * (restrict A E)⁻¹ * (schurCross A E)ᵀ := by
  classical
  have hcrossR : A.submatrix (fun i : (↑E : Type _) => i.val)
      (fun i : (↑(Eᶜ) : Type _) => i.val) = (schurCross A E)ᵀ := by
    ext i j
    change A i.val j.val = A j.val i.val
    exact (hA.apply i.val j.val).symm
  change restrict A Eᶜ -
    A.submatrix (fun i : (↑(Eᶜ) : Type _) => i.val) (fun i : E => i.val) *
      (restrict A E)⁻¹ * A.submatrix (fun i : E => i.val)
        (fun i : (↑(Eᶜ) : Type _) => i.val) = _
  rw [hcrossR]
  rfl

private theorem schur_constantKernel {P : Type*} [Fintype P] [DecidableEq P]
    (A : RMat P) (E : Finset P) (hA : constantKernel A)
    (hS : (Eᶜ).Nonempty) : constantKernel (schur A E) := by
  classical
  let e := finsetPartitionEquiv E
  let T := restrict A E
  let B := schurCross A E
  have hTpos := constantKernel_restrict_posDef A E hA hS
  have hTunit : IsUnit T := by simpa [T] using hTpos.isUnit
  have hTsym : T.IsSymm := hA.1.submatrix Subtype.val
  have hTinvSymm : (T⁻¹).IsSymm := hTsym.inv
  have hschur := schur_block_eq A E hA.1
  have hSymm : (schur A E).IsSymm := by
    rw [hschur]
    apply Matrix.IsSymm.sub
    · exact hA.1.submatrix (fun i : (↑(Eᶜ) : Type _) => i.val)
    · change (B * T⁻¹ * Bᵀ)ᵀ = B * T⁻¹ * Bᵀ
      simp [Matrix.transpose_mul, Matrix.transpose_transpose, hTinvSymm.eq,
        Matrix.mul_assoc]
  have hSchurNonneg : ∀ v, 0 ≤ qform (schur A E) v := by
    intro v
    let u : (↑E : Type _) → ℝ := -((T⁻¹ * Bᵀ) *ᵥ v)
    have hc := schur_energy_completion A E hA.1 hTunit u v
    have hu : u + (T⁻¹ * Bᵀ) *ᵥ v = 0 := by simp [u]
    let f : P → ℝ := fun x => Sum.elim u v (e.symm x)
    have hApos : 0 ≤ qform A f := hA.2.1 f
    have hcomp : qform A f = qform T 0 + qform (schur A E) v := by
      simpa [e, f, finsetPartitionEquiv, T, B, hu] using hc
    rw [hcomp] at hApos
    simpa [qform] using hApos
  constructor
  · exact hSymm
  constructor
  · exact hSchurNonneg
  · intro v
    constructor
    · intro hzero
      let u : (↑E : Type _) → ℝ := -((T⁻¹ * Bᵀ) *ᵥ v)
      have hc := schur_energy_completion A E hA.1 hTunit u v
      let f : P → ℝ := fun x => Sum.elim u v (e.symm x)
      have hAzero : qform A f = 0 := by
        have hu : u + (T⁻¹ * Bᵀ) *ᵥ v = 0 := by simp [u]
        have hcomp : qform A f = qform T 0 + qform (schur A E) v := by
          simpa [e, f, finsetPartitionEquiv, T, B, hu] using hc
        rw [hcomp, hzero]
        simp [qform]
      obtain ⟨c, hc0⟩ := (hA.2.2 f).mp hAzero
      refine ⟨c, ?_⟩
      intro i
      have hi : e.symm i.val = Sum.inr i := by
        apply e.injective
        simp [e, finsetPartitionEquiv, Finset.mem_compl.mp i.property]
      simpa [f, hi] using hc0 i.val
    · rintro ⟨c, hc⟩
      let u : (↑E : Type _) → ℝ := fun _ => c
      let f : P → ℝ := fun x => Sum.elim u (fun _ => c) (e.symm x)
      have hAzero : qform A f = 0 := by
        apply (hA.2.2 f).2
        exact ⟨c, by intro x; simp [f, u, finsetPartitionEquiv]⟩
      have hcenergy := schur_energy_completion A E hA.1 hTunit u (fun _ => c)
      have hTnonneg : 0 ≤ qform T
          (u + (T⁻¹ * Bᵀ) *ᵥ (fun _ => c)) :=
        by simpa [qform, dotProduct, star_trivial] using
          (hTpos.posSemidef.dotProduct_mulVec_nonneg
            (u + (T⁻¹ * Bᵀ) *ᵥ (fun _ => c)))
      have hSnonneg : 0 ≤ qform (schur A E) (fun _ => c) := hSchurNonneg _
      have hsum :
          qform T (u + (T⁻¹ * Bᵀ) *ᵥ (fun _ => c)) +
            qform (schur A E) (fun _ => c) = 0 := by
        have hcomp : qform A f =
            qform T (u + (T⁻¹ * Bᵀ) *ᵥ (fun _ => c)) +
              qform (schur A E) (fun _ => c) := by
          simpa [f, e, finsetPartitionEquiv] using hcenergy
        rw [← hcomp]
        exact hAzero
      have hQzero : qform (schur A E) (fun _ => c) = 0 := by nlinarith
      have hv : v = fun _ => c := funext hc
      rw [hv]
      exact hQzero

private def supportedCharge {P : Type*} [Fintype P] [DecidableEq P]
    (E : Finset P) (y : (↑(Eᶜ) : Type _) → ℝ) : P → ℝ :=
  fun i => if hi : i ∈ Eᶜ then y ⟨i, hi⟩ else 0

private theorem schur_supported_dual_eq {P : Type*} [Fintype P] [DecidableEq P]
    (A : RMat P) (E : Finset P) (hA : constantKernel A) (hS : (Eᶜ).Nonempty)
    (y : (↑(Eᶜ) : Type _) → ℝ) (hy : neutral y) :
    dualForm (qform (schur A E)) y =
      dualForm (qform A) (supportedCharge E y) := by
  classical
  let e := finsetPartitionEquiv E
  let yFull := supportedCharge E y
  have hycomp : yFull ∘ e = Sum.elim (fun _ => 0) y := by
    funext s
    cases s with
    | inl i => simp [yFull, supportedCharge, e, finsetPartitionEquiv]
    | inr i => simp [yFull, supportedCharge, e, finsetPartitionEquiv]
  have hyFull : neutral yFull := by
    unfold neutral
    calc
      (∑ x : P, yFull x) = ∑ s, yFull (e s) := by
        exact (Fintype.sum_equiv e (fun s => yFull (e s)) yFull (fun _ => rfl)).symm
      _ = ∑ s, (Sum.elim (fun _ => 0) y) s := by rw [← hycomp]; rfl
      _ = 0 := by simpa [Fintype.sum_sum_type, neutral] using hy
  obtain ⟨z, hz⟩ := constantKernel_solve A yFull hA hyFull
  let zE : (↑E : Type _) → ℝ := fun i => z i.1
  let zS : (↑(Eᶜ) : Type _) → ℝ := fun i => z i.1
  let g : (↑E : Type _) ⊕ (↑(Eᶜ) : Type _) → ℝ := fun s => z (e s)
  have hg : g ∘ e.symm = z := by
    funext x
    simp [g]
  have hmul : Matrix.reindex e.symm e.symm A *ᵥ g =
      (A *ᵥ z) ∘ e := by
    calc
      Matrix.reindex e.symm e.symm A *ᵥ g = A.submatrix e e *ᵥ g := rfl
      _ = (A *ᵥ (g ∘ e.symm)) ∘ e := Matrix.submatrix_mulVec_equiv A g e e
      _ = (A *ᵥ z) ∘ e := by rw [hg]
  have hblock : Matrix.reindex e.symm e.symm A =
      Matrix.fromBlocks (restrict A E) (schurCross A E)ᵀ
        (schurCross A E) (restrict A Eᶜ) := schur_reindex_blocks A E hA.1
  have hblocks :
      Matrix.fromBlocks (restrict A E) (schurCross A E)ᵀ
        (schurCross A E) (restrict A Eᶜ) *ᵥ g = Sum.elim (fun _ => 0) y := by
    calc
      _ = Matrix.reindex e.symm e.symm A *ᵥ g := by rw [hblock]
      _ = (A *ᵥ z) ∘ e := hmul
      _ = yFull ∘ e := by rw [hz]
      _ = Sum.elim (fun _ => 0) y := hycomp
  rw [Matrix.fromBlocks_mulVec] at hblocks
  have hgleft : g ∘ Sum.inl = zE := by
    funext i
    simp [g, zE, e, finsetPartitionEquiv]
  have hgright : g ∘ Sum.inr = zS := by
    funext i
    simp [g, zS, e, finsetPartitionEquiv]
  simp only [hgleft, hgright] at hblocks
  have htop : restrict A E *ᵥ zE + (schurCross A E)ᵀ *ᵥ zS = 0 := by
    funext i
    have hi := congrFun hblocks (Sum.inl i)
    simpa [zE, zS] using hi
  have hbottom : schurCross A E *ᵥ zE + restrict A Eᶜ *ᵥ zS = y := by
    funext i
    have hi := congrFun hblocks (Sum.inr i)
    simpa [zE, zS] using hi
  have hTpos := constantKernel_restrict_posDef A E hA hS
  have hTunit : IsUnit (restrict A E) := hTpos.isUnit
  have hTdet : IsUnit (restrict A E).det :=
    (Matrix.isUnit_iff_isUnit_det (restrict A E)).mp hTunit
  have hrel : zE + ((restrict A E)⁻¹ * (schurCross A E)ᵀ) *ᵥ zS = 0 := by
    have hi := congrArg (fun w => (restrict A E)⁻¹ *ᵥ w) htop
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul (restrict A E) hTdet, Matrix.one_mulVec] at hi
    simpa using hi
  have hzE : zE = -(((restrict A E)⁻¹ * (schurCross A E)ᵀ) *ᵥ zS) := by
    funext i
    have hi := congrFun hrel i
    exact add_eq_zero_iff_eq_neg.mp hi
  have hbottom' :
      restrict A Eᶜ *ᵥ zS - (schurCross A E *
        ((restrict A E)⁻¹ * (schurCross A E)ᵀ)) *ᵥ zS = y := by
    have h := hbottom
    rw [hzE, Matrix.mulVec_neg] at h
    simpa [sub_eq_add_neg, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      add_comm, add_left_comm, add_assoc] using h
  have hsolveSchur : schur A E *ᵥ zS = y := by
    rw [schur_block_eq A E hA.1, Matrix.sub_mulVec]
    simpa [Matrix.mulVec_mulVec, Matrix.mul_assoc] using hbottom'
  have hSchurK := schur_constantKernel A E hA hS
  have hdualA := dualForm_qform_of_solve A yFull z hA.1 hA.2.1 hz
  have hdualS := dualForm_qform_of_solve (schur A E) y zS hSchurK.1
    hSchurK.2.1 hsolveSchur
  have hdot : dotProduct z yFull = dotProduct zS y := by
    have hs :
        (∑ s : (↑E : Type _) ⊕ (↑(Eᶜ) : Type _), g s * (Sum.elim (fun _ => 0) y) s) =
          ∑ x : P, z x * yFull x := by
      refine Fintype.sum_equiv e _ _ ?_
      intro s
      cases s with
      | inl i => simp [g, yFull, supportedCharge, e, finsetPartitionEquiv, i.property]
      | inr i => simp [g, yFull, supportedCharge, e, finsetPartitionEquiv,
          Finset.mem_compl.mp i.property]
    calc
      dotProduct z yFull = ∑ x : P, z x * yFull x := rfl
      _ = ∑ s, g s * (Sum.elim (fun _ => 0) y) s := hs.symm
      _ = dotProduct zS y := by
        rw [Fintype.sum_sum_type]
        simp [dotProduct, g, zS, e, finsetPartitionEquiv]
  have hvalue : qform A z = qform (schur A E) zS := by
    calc
      qform A z = dotProduct z yFull := by rw [qform, hz]; rfl
      _ = dotProduct zS y := hdot
      _ = qform (schur A E) zS := by rw [qform, hsolveSchur]; rfl
  rw [hdualA, hdualS, hvalue]

theorem increment_pullback_proof {P H : Type*} [Fintype P] [Fintype H]
    [DecidableEq P] [DecidableEq H] (S : Finset P) (L : P → RMat P)
    (B : Matrix P H ℝ) (D : RMat P) (W Wstar : Form P) (C σ : ℝ)
    (hC : 0 ≤ C) (hσ : 0 ≤ σ) (hL : ∀ x ∈ S, (L x).IsSymm)
    (hneutral : ∀ x ∈ S, ∀ f, neutral (L x *ᵥ f))
    (hD : ∀ f, qform D f ≤ C * W f)
    (hB : ∀ v, W (B *ᵥ v) ≤ C * l2sq v)
    (hdual : ∀ y, neutral y → l2sq (Bᵀ *ᵥ y) ≤ C * Wstar y)
    (hstack : ∀ f, (∑ x ∈ S, Wstar (L x *ᵥ f)) ≤ σ * qform D f) :
    (∑ x ∈ S, (pullback B (L x))^2) ≤ (C^3 * σ) • (1 : RMat H) := by
  let X : P → RMat H := fun x => pullback B (L x)
  have hXsym (x : P) (hx : x ∈ S) : (X x).IsSymm := by
    simp only [X, pullback, Matrix.IsSymm]
    simp [Matrix.transpose_mul, Matrix.transpose_transpose, (hL x hx).eq,
      Matrix.mul_assoc]
  have hstack' (v : H → ℝ) :
      (∑ x ∈ S, l2sq (X x *ᵥ v)) ≤ (C^3 * σ) * l2sq v := by
    have hdualsum :
        (∑ x ∈ S, l2sq (X x *ᵥ v)) ≤ C * ∑ x ∈ S, Wstar (L x *ᵥ (B *ᵥ v)) := by
      calc
        (∑ x ∈ S, l2sq (X x *ᵥ v)) =
            ∑ x ∈ S, l2sq (Bᵀ *ᵥ (L x *ᵥ (B *ᵥ v))) := by
              apply Finset.sum_congr rfl
              intro x hx
              simp [X, pullback, Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ ≤ ∑ x ∈ S, C * Wstar (L x *ᵥ (B *ᵥ v)) := by
              apply Finset.sum_le_sum
              intro x hx
              apply hdual
              exact hneutral x hx (B *ᵥ v)
        _ = C * ∑ x ∈ S, Wstar (L x *ᵥ (B *ᵥ v)) := by rw [Finset.mul_sum]
    calc
      _ ≤ C * ∑ x ∈ S, Wstar (L x *ᵥ (B *ᵥ v)) := hdualsum
      _ ≤ C * (σ * qform D (B *ᵥ v)) := by
          exact mul_le_mul_of_nonneg_left (hstack (B *ᵥ v)) hC
      _ ≤ C * (σ * (C * W (B *ᵥ v))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hD (B *ᵥ v)) hσ) hC
      _ = (C * σ * C) * W (B *ᵥ v) := by ring
      _ ≤ (C * σ * C) * (C * l2sq v) :=
          mul_le_mul_of_nonneg_left (hB v) (mul_nonneg (mul_nonneg hC hσ) hC)
      _ = (C^3 * σ) * l2sq v := by ring
  apply Matrix.le_iff.mpr
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · -- symmetry of the proposed difference
    have hs : (∑ x ∈ S, X x ^ 2).IsSymm := by
      classical
      apply Matrix.IsSymm.ext
      intro i j
      simp only [Matrix.sum_apply]
      apply Finset.sum_congr rfl
      intro x hx
      exact ((hXsym x hx).pow 2).apply i j
    have hI : ((C^3 * σ) • (1 : RMat H)).IsSymm :=
      (Matrix.isSymm_one (n := H)).smul _
    simpa using (Matrix.isHermitian_iff_isSymm).2 (hI.sub hs)
  · intro v
    have hv := hstack' v
    have hquad (x : P) (hx : x ∈ S) :
        dotProduct v ((X x ^ 2) *ᵥ v) = l2sq (X x *ᵥ v) := by
      rw [pow_two, ← Matrix.mulVec_mulVec]
      rw [(hXsym x hx).dotProduct_mulVec_comm]
      simp [l2sq, dotProduct, pow_two]
    have hsum :
        dotProduct v ((∑ x ∈ S, X x ^ 2) *ᵥ v) =
          ∑ x ∈ S, l2sq (X x *ᵥ v) := by
      simp only [Matrix.sum_mulVec, dotProduct_sum]
      apply Finset.sum_congr rfl
      intro x hx
      exact hquad x hx
    have hmatrix :
        dotProduct v (((C^3 * σ) • (1 : RMat H) - ∑ x ∈ S, X x ^ 2) *ᵥ v) =
          (C^3 * σ) * l2sq v - ∑ x ∈ S, l2sq (X x *ᵥ v) := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul, hsum]
      simp [l2sq, dotProduct, pow_two]
    change 0 ≤ dotProduct v (((C^3 * σ) • (1 : RMat H) -
      ∑ x ∈ S, X x ^ 2) *ᵥ v)
    rw [hmatrix]
    linarith

private theorem supportedCharge_neutral {P : Type*} [Fintype P] [DecidableEq P]
    (E : Finset P) (y : (↑(Eᶜ) : Type _) → ℝ) (hy : neutral y) :
    neutral (supportedCharge E y) := by
  classical
  let e := finsetPartitionEquiv E
  let yFull := supportedCharge E y
  have hycomp : yFull ∘ e = Sum.elim (fun _ => 0) y := by
    funext s
    cases s with
    | inl i => simp [yFull, supportedCharge, e, finsetPartitionEquiv]
    | inr i => simp [yFull, supportedCharge, e, finsetPartitionEquiv]
  unfold neutral
  calc
    (∑ x : P, yFull x) = ∑ s, yFull (e s) := by
      exact (Fintype.sum_equiv e (fun s => yFull (e s)) yFull (fun _ => rfl)).symm
    _ = ∑ s, (Sum.elim (fun _ => 0) y) s := by rw [← hycomp]; rfl
    _ = 0 := by simpa [Fintype.sum_sum_type, neutral] using hy

private theorem dualForm_qform_div_le {P : Type*} [Fintype P] [DecidableEq P]
    (A B : RMat P) (y : P → ℝ) (c : ℝ) (hc : 0 < c)
    (hA : constantKernel A) (hB : constantKernel B) (hy : neutral y)
    (hle : ∀ f, qform A f ≤ c * qform B f) :
    dualForm (qform B) y / c ≤ dualForm (qform A) y := by
  obtain ⟨xA, hxA⟩ := constantKernel_solve A y hA hy
  obtain ⟨xB, hxB⟩ := constantKernel_solve B y hB hy
  have hdualA := dualForm_qform_of_solve A y xA hA.1 hA.2.1 hxA
  have hdualB := dualForm_qform_of_solve B y xB hB.1 hB.2.1 hxB
  have hvar := qform_variational_bound A y xA (c⁻¹ • xB) hA.1 hA.2.1 hxA
  have hdotB : dotProduct y xB = qform B xB := by
    calc
      dotProduct y xB = dotProduct xB y := dotProduct_comm _ _
      _ = dotProduct xB (B *ᵥ xB) := by rw [hxB]
      _ = qform B xB := rfl
  have hdot : dotProduct y (c⁻¹ • xB) = c⁻¹ * qform B xB := by
    rw [dotProduct_smul, smul_eq_mul, hdotB]
  have hqle : qform A (c⁻¹ • xB) ≤ c⁻¹ * qform B xB := by
    calc
      qform A (c⁻¹ • xB) ≤ c * qform B (c⁻¹ • xB) := hle (c⁻¹ • xB)
      _ = c * (c⁻¹ ^ 2 * qform B xB) := by rw [qform_smul_sq B]
      _ = c⁻¹ * qform B xB := by field_simp [hc.ne']
  rw [hdualA, hdualB, div_eq_mul_inv, mul_comm (qform B xB) c⁻¹]
  rw [hdot] at hvar
  linarith

private theorem dualForm_qform_le_div {P : Type*} [Fintype P] [DecidableEq P]
    (A B : RMat P) (y : P → ℝ) (c : ℝ) (hc : 0 < c)
    (hA : constantKernel A) (hB : constantKernel B) (hy : neutral y)
    (hle : ∀ f, c * qform B f ≤ qform A f) :
    dualForm (qform A) y ≤ dualForm (qform B) y / c := by
  have hle' : ∀ f, qform B f ≤ c⁻¹ * qform A f := by
    intro f
    have h1 := mul_le_mul_of_nonneg_left (hle f) (inv_pos.mpr hc).le
    rwa [inv_mul_cancel_left₀ hc.ne'] at h1
  have hdiv := dualForm_qform_div_le B A y c⁻¹ (inv_pos.mpr hc) hB hA hy hle'
  rw [div_inv_eq_mul] at hdiv
  exact (le_div_iff₀ hc).mpr hdiv

theorem schur_dual_transport_proof {P : Type*} [Fintype P] [DecidableEq P]
    (D L : RMat P) (E : Finset P) (ε : ℝ) (hε : 0 ≤ ε ∧ ε < 1)
    (hD : constantKernel D) (hL : L.IsSymm)
    (hLzero : L *ᵥ (fun _ => 1) = 0) (hcap : formAbsLe (qform L) (qform D) ε)
    (hproper : E ≠ Finset.univ) :
    constantKernel (schur (D + L) E) ∧
    ∀ y : (↑(Eᶜ) : Type _) → ℝ, neutral y →
      dualForm (qform D) (fun i => if hi : i ∈ Eᶜ then y ⟨i, hi⟩ else 0) / (1 + ε) ≤
        dualForm (qform (schur (D + L) E)) y ∧
      dualForm (qform (schur (D + L) E)) y ≤
        dualForm (qform D) (fun i => if hi : i ∈ Eᶜ then y ⟨i, hi⟩ else 0) / (1 - ε) := by
  have _ := hLzero
  have hS : (Eᶜ).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    apply hproper
    ext x
    simp [Finset.ext_iff] at hemp
    simpa using hemp x
  have hDL : constantKernel (D + L) := constantKernel_add_error D L ε hε hD hL hcap
  refine ⟨schur_constantKernel (D + L) E hDL hS, ?_⟩
  intro y hy
  have hschur_eq : dualForm (qform (schur (D + L) E)) y =
      dualForm (qform (D + L)) (supportedCharge E y) :=
    schur_supported_dual_eq (D + L) E hDL hS y hy
  have hyFull : neutral (supportedCharge E y) := supportedCharge_neutral E y hy
  have hupper : ∀ f, qform (D + L) f ≤ (1 + ε) * qform D f := by
    intro f
    have habs := (abs_le.mp (hcap f)).2
    rw [qform_add]
    linarith
  have hlower : ∀ f, (1 - ε) * qform D f ≤ qform (D + L) f := by
    intro f
    have habs := (abs_le.mp (hcap f)).1
    rw [qform_add]
    linarith
  have h1 := dualForm_qform_div_le (D + L) D (supportedCharge E y) (1 + ε)
    (by linarith [hε.1]) hDL hD hyFull hupper
  have h2 := dualForm_qform_le_div (D + L) D (supportedCharge E y) (1 - ε)
    (by linarith [hε.2]) hDL hD hyFull hlower
  rw [hschur_eq]
  exact ⟨h1, h2⟩

end AndersonAC.AgentS45
