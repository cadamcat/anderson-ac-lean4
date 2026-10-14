import AndersonAC.S45.Definitions

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace AndersonAC.AgentS45

open AndersonAC.S45

private def euclideanVec {P : Type*} [Fintype P] (x : P → ℂ) : EuclideanSpace ℂ P :=
  (EuclideanSpace.equiv P ℂ).symm x

private def patchVector {P : Type*} [Fintype P] [DecidableEq P] (E : Finset P)
    (y : (↑E : Type _) → ℂ) (x : (↑(Eᶜ) : Type _) → ℂ) (i : P) : ℂ :=
  if hi : i ∈ E then y ⟨i, hi⟩ else x ⟨i, by simpa using hi⟩

private theorem euclideanVec_norm_sq {P : Type*} [Fintype P] (x : P → ℂ) :
    ‖euclideanVec x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  rw [euclideanVec, EuclideanSpace.norm_sq_eq]
  simp

private theorem subtype_complement_sum {P : Type*} [Fintype P] [DecidableEq P]
    {M : Type*} [AddCommMonoid M] (E : Finset P) (f : P → M) :
    (∑ i : (↑E : Type _), f i.val) +
      ∑ i : (↑(Eᶜ) : Type _), f i.val = ∑ i, f i := by
  classical
  rw [← Finset.sum_subtype E (by intro i; rfl) f,
    ← Finset.sum_subtype Eᶜ (by intro i; rfl) f]
  exact Finset.sum_add_sum_compl E f

private theorem sum_sq_subtype_le {P : Type*} [Fintype P] [DecidableEq P]
    (E : Finset P) (x : P → ℂ) :
    (∑ i : (↑E : Type _), ‖x i.val‖ ^ 2) ≤ ∑ i, ‖x i‖ ^ 2 := by
  classical
  have hs := subtype_complement_sum E (fun i => ‖x i‖ ^ 2)
  have hn : 0 ≤ ∑ i : (↑(Eᶜ) : Type _), ‖x i.val‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg ‖x i.val‖
  linarith

private theorem patchVector_norm_sq {P : Type*} [Fintype P] [DecidableEq P]
    (E : Finset P) (y : (↑E : Type _) → ℂ) (x : (↑(Eᶜ) : Type _) → ℂ) :
    (∑ i, ‖patchVector E y x i‖ ^ 2) =
      (∑ i : (↑E : Type _), ‖y i‖ ^ 2) +
        (∑ i : (↑(Eᶜ) : Type _), ‖x i‖ ^ 2) := by
  classical
  calc
    ∑ i, ‖patchVector E y x i‖ ^ 2 =
        (∑ i : (↑E : Type _), ‖patchVector E y x i.val‖ ^ 2) +
          ∑ i : (↑(Eᶜ) : Type _), ‖patchVector E y x i.val‖ ^ 2 :=
            (subtype_complement_sum E (fun i => ‖patchVector E y x i‖ ^ 2)).symm
    _ = (∑ i : (↑E : Type _), ‖y i‖ ^ 2) +
          ∑ i : (↑(Eᶜ) : Type _), ‖x i‖ ^ 2 := by
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        simp [patchVector, i.property]
      · apply Finset.sum_congr rfl
        intro i hi
        have hnot : i.val ∉ E := Finset.mem_compl.mp i.property
        simp [patchVector, hnot]

private theorem matrix_action_sq_le {P : Type*} [Fintype P] [DecidableEq P]
    (B : CMat P) (ρ : ℝ) (hρ : 0 ≤ ρ) (hB : ‖B‖ ≤ ρ) (x : P → ℂ) :
    (∑ i, ‖(B *ᵥ x) i‖ ^ 2) ≤ ρ ^ 2 * ∑ i, ‖x i‖ ^ 2 := by
  have hnorm : ‖euclideanVec (B *ᵥ x)‖ ≤ ρ * ‖euclideanVec x‖ := by
    calc
      ‖euclideanVec (B *ᵥ x)‖ =
          ‖(EuclideanSpace.equiv P ℂ).symm (B *ᵥ euclideanVec x)‖ := by
            simp [euclideanVec]
      _ ≤ ‖B‖ * ‖euclideanVec x‖ := Matrix.l2_opNorm_mulVec B (euclideanVec x)
      _ ≤ ρ * ‖euclideanVec x‖ := mul_le_mul_of_nonneg_right hB (norm_nonneg _)
  calc
    ∑ i, ‖(B *ᵥ x) i‖ ^ 2 = ‖euclideanVec (B *ᵥ x)‖ ^ 2 :=
      (euclideanVec_norm_sq _).symm
    _ ≤ (ρ * ‖euclideanVec x‖) ^ 2 := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hρ (norm_nonneg _))).2 hnorm
    _ = ρ ^ 2 * ∑ i, ‖x i‖ ^ 2 := by rw [mul_pow, euclideanVec_norm_sq]

private theorem mulVec_patchVector {P : Type*} [Fintype P] [DecidableEq P]
    (B : CMat P) (E : Finset P) (y : (↑E : Type _) → ℂ)
    (x : (↑(Eᶜ) : Type _) → ℂ) (i : P) :
    (B *ᵥ patchVector E y x) i =
      (∑ j : (↑E : Type _), B i j.val * y j) +
        ∑ j : (↑(Eᶜ) : Type _), B i j.val * x j := by
  classical
  rw [Matrix.mulVec_apply_eq_sum]
  rw [← subtype_complement_sum E (fun j => B i j * patchVector E y x j)]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    simp [patchVector, j.property]
  · apply Finset.sum_congr rfl
    intro j hj
    have hnot : j.val ∉ E := Finset.mem_compl.mp j.property
    simp [patchVector, hnot]

private theorem single_mul_mul_single_self {I : Type*} [Fintype I] [DecidableEq I]
    (i : I) (v : ℂ) (G : CMat I) :
    Matrix.single i i v * G * Matrix.single i i v = (v * G i i) • Matrix.single i i v := by
  rw [Matrix.single_mul_mul_single, Matrix.smul_single, smul_eq_mul]

private theorem diagonal_pi_single_eq_single {I : Type*} [Fintype I] [DecidableEq I]
    (i : I) (v : ℂ) : diagonal (Pi.single i v) = Matrix.single i i v := by
  ext j k
  by_cases hjk : j = k
  · subst k
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji, Ne.symm hji, Matrix.single]
  · simp [Matrix.single, hjk]
    intro h1 h2
    exact absurd (h1.symm.trans h2) hjk

theorem schur_add_supported_proof {P : Type*} [Fintype P] [DecidableEq P]
    {𝕜 : Type*} [RCLike 𝕜] (A : Matrix P P 𝕜) (E : Finset P)
    (B : Matrix (↑(Eᶜ) : Type _) (↑(Eᶜ) : Type _) 𝕜) :
    schur (A + pad Eᶜ B) E = schur A E + B := by
  classical
  have hEE : restrict (A + pad Eᶜ B) E = restrict A E := by
    ext i j
    simp [restrict, pad, i.property, j.property]
  have hEC : (A + pad Eᶜ B).submatrix (fun i : (↑(Eᶜ) : Type _) => i.val)
      (fun i : E => i.val) = A.submatrix (fun i : (↑(Eᶜ) : Type _) => i.val)
      (fun i : E => i.val) := by
    ext i j
    simp [pad, j.property]
  have hCE : (A + pad Eᶜ B).submatrix (fun i : E => i.val)
      (fun i : (↑(Eᶜ) : Type _) => i.val) = A.submatrix (fun i : E => i.val)
      (fun i : (↑(Eᶜ) : Type _) => i.val) := by
    ext i j
    simp [pad, i.property]
  have hCC : restrict (A + pad Eᶜ B) Eᶜ = restrict A Eᶜ + B := by
    ext i j
    simp [restrict, pad, i.property, j.property]
  simp only [schur]
  rw [hCC, hEE, hCE, hEC]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

theorem schur_contraction_proof {P : Type*} [Fintype P] [DecidableEq P]
    (B : CMat P) (E : Finset P) (ρ : ℝ) (hρ : 0 ≤ ρ ∧ ρ < 1) (hB : ‖B‖ ≤ ρ) :
    IsUnit (restrict (1 - B) E) ∧ ‖1 - schur (1 - B) E‖ ≤ ρ := by
  classical
  let C : Type _ := (↑(Eᶜ) : Type _)
  let H : Matrix (↑E : Type _) (↑E : Type _) ℂ := restrict (1 - B) E
  let BEE : Matrix (↑E : Type _) (↑E : Type _) ℂ := restrict B E
  let BEC : Matrix (↑E : Type _) C ℂ :=
    B.submatrix (fun i : (↑E : Type _) => i.val) (fun i : C => i.val)
  let BCE : Matrix C (↑E : Type _) ℂ :=
    B.submatrix (fun i : C => i.val) (fun i : (↑E : Type _) => i.val)
  let BCC : Matrix C C ℂ := restrict B Eᶜ
  have hH : H = 1 - BEE := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [H, BEE, restrict]
    · have hval : i.val ≠ j.val := fun h => hij (Subtype.ext h)
      simp [H, BEE, restrict, hij, hval]
  have hker : ∀ u : (↑E : Type _) → ℂ, H *ᵥ u = 0 → u = 0 := by
    intro u hu
    have hrel : BEE *ᵥ u = u := by
      have hsub : u - BEE *ᵥ u = 0 := by
        simpa [hH, Matrix.sub_mulVec, Matrix.one_mulVec] using hu
      exact (sub_eq_zero.mp hsub).symm
    let w : P → ℂ := patchVector E u (fun _ => 0)
    have hrow : ∀ a : (↑E : Type _), (B *ᵥ w) a.val = u a := by
      intro a
      calc
        (B *ᵥ w) a.val =
            (∑ b : (↑E : Type _), B a.val b.val * u b) + 0 := by
              simpa [w] using mulVec_patchVector B E u (fun _ => 0) a.val
        _ = (BEE *ᵥ u) a := by simp [BEE, restrict, Matrix.mulVec_apply_eq_sum]
        _ = u a := congrFun hrel a
    let S : ℝ := ∑ a : (↑E : Type _), ‖u a‖ ^ 2
    have hsmall : S ≤ ∑ i, ‖(B *ᵥ w) i‖ ^ 2 := by
      dsimp [S]
      calc
        ∑ a : (↑E : Type _), ‖u a‖ ^ 2 =
            ∑ a : (↑E : Type _), ‖(B *ᵥ w) a.val‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [hrow]
        _ ≤ ∑ i, ‖(B *ᵥ w) i‖ ^ 2 := sum_sq_subtype_le E (B *ᵥ w)
    have hfull := matrix_action_sq_le B ρ hρ.1 hB w
    have hinput : (∑ i, ‖w i‖ ^ 2) = S := by
      calc
        ∑ i, ‖w i‖ ^ 2 =
            (∑ a : (↑E : Type _), ‖u a‖ ^ 2) +
              ∑ c : (↑(Eᶜ) : Type _), ‖(0 : (↑(Eᶜ) : Type _) → ℂ) c‖ ^ 2 := by
                simpa [w] using patchVector_norm_sq E u (fun _ => 0)
        _ = S := by simp [S]
    have hSle : S ≤ ρ ^ 2 * S := by
      calc
        S ≤ ∑ i, ‖(B *ᵥ w) i‖ ^ 2 := hsmall
        _ ≤ ρ ^ 2 * ∑ i, ‖w i‖ ^ 2 := hfull
        _ = ρ ^ 2 * S := by rw [hinput]
    have hSnonneg : 0 ≤ S := by
      dsimp [S]
      exact Finset.sum_nonneg fun a _ => sq_nonneg ‖u a‖
    have hρsq : ρ ^ 2 < 1 := by nlinarith [hρ.1, hρ.2]
    have hSzero : S = 0 := by
      by_contra hSne
      have hSpos : 0 < S := lt_of_le_of_ne hSnonneg (Ne.symm hSne)
      have hmul : ρ ^ 2 * S < S := by
        calc
          ρ ^ 2 * S < 1 * S := mul_lt_mul_of_pos_right hρsq hSpos
          _ = S := by ring
      exact (not_lt_of_ge hSle) hmul
    funext a
    have hterm : ‖u a‖ ^ 2 ≤ S := by
      dsimp [S]
      exact Finset.single_le_sum (fun b _ => sq_nonneg ‖u b‖) (Finset.mem_univ a)
    have hnorm : ‖u a‖ = 0 := by nlinarith [sq_nonneg ‖u a‖, hSzero, hterm]
    exact norm_eq_zero.mp hnorm
  have hinj : Function.Injective H.mulVec := by
    intro x y hxy
    have hsub : H *ᵥ (x - y) = 0 := by
      calc
        H *ᵥ (x - y) = H *ᵥ x - H *ᵥ y := Matrix.mulVec_sub H x y
        _ = 0 := by rw [hxy]; simp
    exact sub_eq_zero.mp (hker (x - y) hsub)
  have hunit : IsUnit H := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hdetH : IsUnit H.det := H.isUnit_iff_isUnit_det.mp hunit
  constructor
  · simpa [H] using hunit
  · let T : Matrix C C ℂ := 1 - schur (1 - B) E
    have hCC : restrict (1 - B) Eᶜ = 1 - BCC := by
      ext c d
      by_cases hcd : c = d
      · subst d
        simp [BCC, restrict]
      · have hval : c.val ≠ d.val := fun h => hcd (Subtype.ext h)
        simp [BCC, restrict, hcd, hval]
    have hCE : (1 - B).submatrix (fun c : C => c.val)
        (fun e : (↑E : Type _) => e.val) = -BCE := by
      ext c e
      have hne : c.val ≠ e.val := by
        intro h
        have hc : c.val ∉ E := Finset.mem_compl.mp c.property
        exact hc (h ▸ e.property)
      simp [BCE, Matrix.submatrix_apply, hne]
    have hEC : (1 - B).submatrix (fun e : (↑E : Type _) => e.val)
        (fun c : C => c.val) = -BEC := by
      ext e c
      have hne : e.val ≠ c.val := by
        intro h
        have hc : c.val ∉ E := Finset.mem_compl.mp c.property
        exact hc (h.symm ▸ e.property)
      simp [BEC, Matrix.submatrix_apply, hne]
    have hschur : schur (1 - B) E = (1 - BCC) - BCE * H⁻¹ * BEC := by
      unfold schur
      rw [hCC, hCE, hEC]
      simp [H, Matrix.mul_assoc]
    have hT : T = BCC + BCE * H⁻¹ * BEC := by
      dsimp [T]
      rw [hschur]
      abel
    have henergy : ∀ x : C → ℂ,
        (∑ c : C, ‖(T *ᵥ x) c‖ ^ 2) ≤ ρ ^ 2 * ∑ c : C, ‖x c‖ ^ 2 := by
      intro x
      let y : (↑E : Type _) → ℂ := H⁻¹ *ᵥ (BEC *ᵥ x)
      have hsolve : (1 - BEE) *ᵥ y = BEC *ᵥ x := by
        rw [← hH]
        calc
          H *ᵥ y = (H * H⁻¹) *ᵥ (BEC *ᵥ x) := by
            dsimp [y]
            rw [← Matrix.mulVec_mulVec]
          _ = BEC *ᵥ x := by rw [Matrix.mul_nonsing_inv H hdetH]; simp
      have hTaction : T *ᵥ x = BCC *ᵥ x + BCE *ᵥ y := by
        rw [hT]
        simp [Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, y]
      let w : P → ℂ := patchVector E y x
      have hfullE : ∀ a : (↑E : Type _), (B *ᵥ w) a.val = y a := by
        intro a
        calc
          (B *ᵥ w) a.val =
              (∑ b : (↑E : Type _), B a.val b.val * y b) +
                ∑ c : C, B a.val c.val * x c := by
                  exact mulVec_patchVector B E y x a.val
          _ = (BEE *ᵥ y) a + (BEC *ᵥ x) a := by
            simp [BEE, BEC, restrict, Matrix.mulVec_apply_eq_sum]
          _ = y a := by
            have hcoord := congrFun hsolve a
            have hcoord' : y a - (BEE *ᵥ y) a = (BEC *ᵥ x) a := by
              simpa [Matrix.sub_mulVec, Matrix.one_mulVec] using hcoord
            linear_combination -hcoord'
      have hfullC : ∀ c : C, (B *ᵥ w) c.val = (T *ᵥ x) c := by
        intro c
        calc
          (B *ᵥ w) c.val =
              (∑ a : (↑E : Type _), B c.val a.val * y a) +
                ∑ d : C, B c.val d.val * x d := by
                  exact mulVec_patchVector B E y x c.val
          _ = (BCE *ᵥ y) c + (BCC *ᵥ x) c := by
            simp [BCE, BCC, restrict, Matrix.mulVec_apply_eq_sum]
          _ = (T *ᵥ x) c := by simpa [add_comm] using (congrFun hTaction c).symm
      let Sy : ℝ := ∑ a : (↑E : Type _), ‖y a‖ ^ 2
      let Sx : ℝ := ∑ c : C, ‖x c‖ ^ 2
      let So : ℝ := ∑ c : C, ‖(T *ᵥ x) c‖ ^ 2
      have hsplitOut : (∑ i, ‖(B *ᵥ w) i‖ ^ 2) = Sy + So := by
        calc
          ∑ i, ‖(B *ᵥ w) i‖ ^ 2 =
              (∑ a : (↑E : Type _), ‖(B *ᵥ w) a.val‖ ^ 2) +
                ∑ c : C, ‖(B *ᵥ w) c.val‖ ^ 2 :=
                  (subtype_complement_sum E (fun i => ‖(B *ᵥ w) i‖ ^ 2)).symm
          _ = Sy + So := by
            dsimp [Sy, So]
            congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> simp [hfullE, hfullC]
      have hinput : (∑ i, ‖w i‖ ^ 2) = Sy + Sx := by
        simpa [w, C, Sy, Sx] using patchVector_norm_sq E y x
      have hnormSq : So ≤ ρ ^ 2 * Sx := by
        have hfull := matrix_action_sq_le B ρ hρ.1 hB w
        have hsum : Sy + So ≤ ρ ^ 2 * (Sy + Sx) := by
          calc
            Sy + So = ∑ i, ‖(B *ᵥ w) i‖ ^ 2 := hsplitOut.symm
            _ ≤ ρ ^ 2 * ∑ i, ‖w i‖ ^ 2 := hfull
            _ = ρ ^ 2 * (Sy + Sx) := by rw [hinput]
        have hSy : 0 ≤ Sy := by
          dsimp [Sy]
          exact Finset.sum_nonneg fun a _ => sq_nonneg ‖y a‖
        have hρsq : ρ ^ 2 ≤ 1 := by nlinarith [hρ.1, hρ.2]
        have hdelta : 0 ≤ 1 - ρ ^ 2 := by linarith
        have hprod : 0 ≤ (1 - ρ ^ 2) * Sy := mul_nonneg hdelta hSy
        nlinarith [hprod]
      exact hnormSq
    have hTop : ‖T‖ ≤ ρ := by
      rw [← Matrix.l2_opNorm_toEuclideanCLM]
      refine ContinuousLinearMap.opNorm_le_bound _ hρ.1 ?_
      intro u
      have hsq' : ‖(Matrix.toEuclideanCLM (n := C) (𝕜 := ℂ) T) u‖ ^ 2 ≤
          (ρ * ‖u‖) ^ 2 := by
        calc
          ‖(Matrix.toEuclideanCLM (n := C) (𝕜 := ℂ) T) u‖ ^ 2 ≤ ρ ^ 2 * ‖u‖ ^ 2 := by
            have hs := henergy (u : C → ℂ)
            simpa [EuclideanSpace.norm_sq_eq, Matrix.ofLp_toEuclideanCLM] using hs
          _ = (ρ * ‖u‖) ^ 2 := by rw [mul_pow]
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hρ.1 (norm_nonneg _))).1 hsq'
    simpa [T] using hTop

theorem physical_rank_one_proof {I : Type*} [Fintype I] [DecidableEq I]
    (A : CMat I) (i : I) (a : ℂ) (hA : IsUnit A)
    (hden : 1 + a * A⁻¹ i i ≠ 0) :
    IsUnit (A + diagonal (Pi.single i a)) ∧
    ∀ j k, (A + diagonal (Pi.single i a))⁻¹ j k =
      A⁻¹ j k - a * A⁻¹ j i * A⁻¹ i k / (1 + a * A⁻¹ i i) := by
  classical
  let G : CMat I := A⁻¹
  let s : ℂ := 1 + a * G i i
  let E : CMat I := Matrix.single i i a
  have hdiag : diagonal (Pi.single i a) = E := by
    dsimp [E]
    exact diagonal_pi_single_eq_single i a
  have hs : s ≠ 0 := by
    simpa [s, G] using hden
  have hcoef : (1 : ℂ) - s⁻¹ - s⁻¹ * (a * G i i) = 0 := by
    have hinv : s⁻¹ * s = 1 := inv_mul_cancel₀ hs
    dsimp [s] at hinv ⊢
    linear_combination -hinv
  have hdet : IsUnit A.det := A.isUnit_iff_isUnit_det.mp hA
  have hAG₁ : A * G = 1 := by
    dsimp [G]
    exact Matrix.mul_nonsing_inv A hdet
  have hAG₂ : G * A = 1 := by
    dsimp [G]
    exact Matrix.nonsing_inv_mul A hdet
  have hEGE : E * G * E = (a * G i i) • E := by
    dsimp [E, G]
    exact single_mul_mul_single_self i a A⁻¹
  have hentry : (G * E * G) = fun j k => G j i * a * G i k := by
    ext j k
    dsimp [E]
    have hmul : (G * Matrix.single i i a * G) j k = G j i * a * G i k := by
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [Matrix.mul_single_apply_same]
      · intro b _ hbi
        rw [Matrix.mul_single_apply_of_ne (hbj := hbi), zero_mul]
      · simp
    exact hmul
  let H : CMat I := G - s⁻¹ • (G * E * G)
  have hleft : (A + E) * H = 1 := by
    dsimp [H]
    calc (A + E) * (G - s⁻¹ • (G * E * G))
        = A * G + E * G - s⁻¹ • (A * G * E * G) -
            s⁻¹ • (E * G * E * G) := by
          simp only [add_mul, mul_sub, Matrix.mul_smul, Matrix.mul_assoc]
          abel
      _ = 1 + E * G - s⁻¹ • (E * G) - s⁻¹ • ((a * G i i) • (E * G)) := by
          rw [hAG₁, hEGE, Matrix.one_mul, Matrix.smul_mul]
      _ = 1 + ((1 : ℂ) - s⁻¹ - s⁻¹ * (a * G i i)) • (E * G) := by
          rw [smul_smul, sub_smul, sub_smul, one_smul]
          abel
      _ = 1 := by rw [hcoef, zero_smul, add_zero]
  have hnew : IsUnit (A + E) := by
    apply (A + E).isUnit_iff_isUnit_det.mpr
    exact Matrix.isUnit_det_of_right_inverse hleft
  have hInvEq : (A + E)⁻¹ = H := by
    calc
      (A + E)⁻¹ = (A + E)⁻¹ * ((A + E) * H) := by rw [hleft, Matrix.mul_one]
      _ = ((A + E)⁻¹ * (A + E)) * H := by rw [Matrix.mul_assoc]
      _ = H := by
        rw [Matrix.nonsing_inv_mul (A + E) ((A + E).isUnit_iff_isUnit_det.mp hnew),
          Matrix.one_mul]
  constructor
  · simpa [hdiag] using hnew
  · intro j k
    rw [hdiag]
    rw [hInvEq]
    change G j k - s⁻¹ * ((G * E * G) j k) = _
    rw [hentry]
    dsimp [s, G]
    rw [div_eq_mul_inv]
    ring

end AndersonAC.AgentS45
