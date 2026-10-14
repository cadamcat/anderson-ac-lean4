import AndersonAC.S78.VariationalInputs

open scoped BigOperators
noncomputable section
set_option autoImplicit false

namespace AndersonAC.SolS78
open AndersonAC.S78

private def activeVector {ι : Type} (A : Finset ι) (f : ι → ℝ) : A → ℝ :=
  fun i => f i.val

private def qForm {ι : Type} [Fintype ι] (Q : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  dotProduct x (Q.mulVec x)

private abbrev Removed {ι : Type} (A B : Finset ι) := {i : A // i.val ∉ B}

private noncomputable def splitEquiv {ι : Type} (A B : Finset ι) (hBA : B ⊆ A) :
    Removed A B ⊕ B ≃ A := by
  classical
  refine
    { toFun := Sum.elim Subtype.val (fun i : B => ⟨i.val, hBA i.property⟩)
      invFun := fun i => if hi : i.val ∈ B then Sum.inr ⟨i.val, hi⟩ else Sum.inl ⟨i, hi⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro s
    cases s with
    | inl i => simp [i.property]
    | inr i => simp [i.property]
  · intro i
    by_cases hi : i.val ∈ B <;> simp [hi]

private def deletedBlock {ι : Type} {A B : Finset ι} (hBA : B ⊆ A)
    (Q : Matrix A A ℝ) : Matrix (Removed A B) (Removed A B) ℝ :=
  Q.submatrix (fun i => (splitEquiv A B hBA (Sum.inl i)))
    (fun i => (splitEquiv A B hBA (Sum.inl i)))

private def crossBlock {ι : Type} {A B : Finset ι} (hBA : B ⊆ A)
    (Q : Matrix A A ℝ) : Matrix (Removed A B) B ℝ :=
  Q.submatrix (fun i => (splitEquiv A B hBA (Sum.inl i)))
    (fun i => (splitEquiv A B hBA (Sum.inr i)))

private def retainedBlock {ι : Type} {A B : Finset ι} (hBA : B ⊆ A)
    (Q : Matrix A A ℝ) : Matrix B B ℝ :=
  Q.submatrix (fun i => (splitEquiv A B hBA (Sum.inr i)))
    (fun i => (splitEquiv A B hBA (Sum.inr i)))

private theorem splitBlockMatrix {ι : Type} {A B : Finset ι} (hBA : B ⊆ A)
    (Q : Matrix A A ℝ) (hQ : Q.IsSymm) :
    Q.submatrix (splitEquiv A B hBA) (splitEquiv A B hBA) =
      Matrix.fromBlocks (deletedBlock hBA Q) (crossBlock hBA Q)
        ((crossBlock hBA Q).transpose) (retainedBlock hBA Q) := by
  let e := splitEquiv A B hBA
  let Qs := Q.submatrix e e
  have hQs : Qs.IsSymm := hQ.submatrix e
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => rfl
    | inr j => rfl
  | inr i =>
    cases j with
    | inl j =>
      change Qs (Sum.inr i) (Sum.inl j) = Qs (Sum.inl j) (Sum.inr i)
      exact (hQs.apply (Sum.inr i) (Sum.inl j)).symm
    | inr j => rfl

private noncomputable def padVector {ι : Type} (A : Finset ι) (x : A → ℝ) : ι → ℝ := by
  classical
  exact fun i => if hi : i ∈ A then x ⟨i, hi⟩ else 0

private theorem active_padVector {ι : Type} (A : Finset ι) (x : A → ℝ) :
    activeVector A (padVector A x) = x := by
  classical
  funext i
  simp [activeVector, padVector]

private theorem realForm_eq_dotProduct {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) (Q : Matrix A A ℝ) (f : ι → ℝ) :
    realForm A Q f = dotProduct (activeVector A f) (Q.mulVec (activeVector A f)) := by
  simp [realForm, activeVector, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem qForm_submatrix_equiv {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (Q : Matrix β β ℝ) (x : β → ℝ) :
    qForm (Q.submatrix e e) (x ∘ e) = qForm Q x := by
  simp only [qForm, Matrix.submatrix_mulVec_equiv]
  have hcomp : (x ∘ e) ∘ e.symm = x := by
    funext i
    simp
  rw [hcomp]
  exact Fintype.sum_equiv e _ _ (by intro i; rfl)

private theorem deletedBlock_posDef {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Finset ι) (hBA : B ⊆ A) (Q : Matrix A A ℝ) (hQps : Q.PosSemidef)
    (hkerQ : ∀ x, qForm Q x = 0 ↔ ∃ c : ℝ, ∀ i, x i = c)
    (hB : B.Nonempty) : (deletedBlock hBA Q).PosDef := by
  classical
  let e := splitEquiv A B hBA
  let Qs := Q.submatrix e e
  let Del := deletedBlock hBA Q
  let Cr := crossBlock hBA Q
  let Ret := retainedBlock hBA Q
  have hQsps : Qs.PosSemidef := hQps.submatrix e
  have hDelps : Del.PosSemidef := hQsps.submatrix Sum.inl
  have hDelherm : Del.IsHermitian := hQsps.isHermitian.submatrix Sum.inl
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hDelherm
  intro x hx
  by_contra hnot
  have hDelnonneg : 0 ≤ dotProduct x (Del.mulVec x) := by
    simpa [star_trivial] using hDelps.dotProduct_mulVec_nonneg x
  have hDelnot : ¬ 0 < dotProduct x (Del.mulVec x) := by
    simpa [star_trivial] using hnot
  have hDelzero : dotProduct x (Del.mulVec x) = 0 :=
    le_antisymm (le_of_not_gt hDelnot) hDelnonneg
  let w : Removed A B ⊕ B → ℝ := Sum.elim x (fun _ => 0)
  have hblocks : Qs = Matrix.fromBlocks Del Cr Cr.transpose Ret := by
    simpa [Qs, Del, Cr, Ret, e] using splitBlockMatrix hBA Q (by
      change Q.transpose = Q
      exact hQps.isHermitian.isSymm)
  have hblockEnergy : qForm Qs w = dotProduct x (Del.mulVec x) := by
    rw [hblocks]
    simp [qForm, w, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Del, Cr, Ret,
      deletedBlock]
  let wfull : A → ℝ := w ∘ e.symm
  have hcomp : wfull ∘ e = w := by
    funext s
    simp [wfull]
  have hQenergy : qForm Q wfull = dotProduct x (Del.mulVec x) := by
    have hq := qForm_submatrix_equiv e Q wfull
    rw [hcomp] at hq
    calc
      qForm Q wfull = qForm Qs w := hq.symm
      _ = dotProduct x (Del.mulVec x) := hblockEnergy
  have hQzero : qForm Q wfull = 0 := by rw [hQenergy, hDelzero]
  obtain ⟨c, hc⟩ := (hkerQ wfull).mp hQzero
  obtain ⟨b, hb⟩ := hB
  let b' : B := ⟨b, hb⟩
  have hcZero : c = 0 := by
    have hz := hc (e (Sum.inr b'))
    simpa [wfull, w] using hz.symm
  apply hx
  funext d
  have hd := hc (e (Sum.inl d))
  simpa [wfull, w, hcZero] using hd

private theorem splitQuadratic {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (M : Matrix (α ⊕ β) (α ⊕ β) ℝ) (A : Matrix α α ℝ) (B : Matrix α β ℝ)
    (E : Matrix β β ℝ) (hM : M = Matrix.fromBlocks A B B.transpose E)
    (hA : A.IsHermitian) [Invertible A] (x : α → ℝ) (y : β → ℝ) :
    qForm M (Sum.elim x y) =
      qForm A (x + (A⁻¹ * B).mulVec y) + qForm (E - B.transpose * A⁻¹ * B) y := by
  rw [hM]
  have h := Matrix.schur_complement_eq₁₁ B E x y hA
  have hBstar : B.conjTranspose = B.transpose := by
    ext i j
    simp [Matrix.conjTranspose, star_trivial]
  rw [hBstar] at h
  simpa [qForm, Matrix.dotProduct_mulVec, Matrix.conjTranspose, star_trivial] using h

private theorem realMatrix_hermitian {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQ : Q.transpose = Q) : Q.IsHermitian := by
  ext i j
  have h := congrFun (congrFun hQ i) j
  simpa [Matrix.IsHermitian, Matrix.conjTranspose, Matrix.transpose] using h

private theorem matrix_posSemidef_of_form {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) (Q : Matrix A A ℝ) (hQ : Q.transpose = Q)
    (D : (ι → ℝ) → ℝ) (hform : ∀ f, D f = realForm A Q f)
    (hD : ∀ f, 0 ≤ D f) : Q.PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨realMatrix_hermitian Q hQ, ?_⟩
  intro x
  have h := hD (padVector A x)
  rw [hform] at h
  rw [realForm_eq_dotProduct] at h
  simpa only [active_padVector, star_trivial] using h

private theorem matrix_form_zero_iff_constant {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (D : (ι → ℝ) → ℝ)
    (hform : ∀ f, D f = dotProduct f (Q.mulVec f))
    (hker : constantKernel Finset.univ D) (x : ι → ℝ) :
    dotProduct x (Q.mulVec x) = 0 ↔ ∃ c : ℝ, ∀ i, x i = c := by
  constructor
  · intro hx
    have hDx : D x = 0 := by rw [hform]; exact hx
    obtain ⟨c, hc⟩ := (hker x).mp hDx
    refine ⟨c, ?_⟩
    intro i
    exact hc i (Finset.mem_univ i)
  · rintro ⟨c, hc⟩
    have hDx : D x = 0 := (hker x).mpr ⟨c, by
      intro i hi
      exact hc i⟩
    rw [hform] at hDx
    exact hDx

private theorem euclidean_mulVec_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (x : ι → ℝ) :
    Q.toEuclideanLin ((EuclideanSpace.equiv ι ℝ).symm x) =
      (EuclideanSpace.equiv ι ℝ).symm (Q.mulVec x) := by
  apply (EuclideanSpace.equiv ι ℝ).injective
  simp [Matrix.toEuclideanLin, Matrix.toLpLin, Matrix.toLin'_apply]

private theorem matrix_neutral_has_solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQ : Q.transpose = Q)
    (D : (ι → ℝ) → ℝ) (hform : ∀ f, D f = dotProduct f (Q.mulVec f))
    (hker : constantKernel Finset.univ D) (y : ι → ℝ)
    (hy : ∑ i, y i = 0) :
    ∃ z : ι → ℝ, Q.mulVec z = y := by
  classical
  let T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι := Q.toEuclideanLin
  have hQherm : Q.IsHermitian := realMatrix_hermitian Q hQ
  have hTsym : T.IsSymmetric := by
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hQherm
  have hyOrth : (EuclideanSpace.equiv ι ℝ).symm y ∈ T.kerᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    have hzker : T z = 0 := by simpa [LinearMap.mem_ker] using hz
    let zf := EuclideanSpace.equiv ι ℝ z
    have hzmul : Q.mulVec zf = 0 := by
      have hzero : (EuclideanSpace.equiv ι ℝ).symm (Q.mulVec zf) = 0 := by
        rw [← euclidean_mulVec_eq Q zf]
        simpa [T, zf] using hzker
      have hh := congrArg (EuclideanSpace.equiv ι ℝ) hzero
      simpa using hh
    obtain ⟨c, hc⟩ := (matrix_form_zero_iff_constant Q D hform hker zf).mp
      (by simp [hzmul])
    have hdot : dotProduct y zf = 0 := by
      calc
        dotProduct y zf = ∑ i, y i * c := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hc i]
        _ = (∑ i, y i) * c := by rw [Finset.sum_mul]
        _ = 0 := by rw [hy]; simp
    change inner ℝ z ((EuclideanSpace.equiv ι ℝ).symm y) = 0
    have hdot' : dotProduct y z.ofLp = 0 := by
      simpa [zf, EuclideanSpace.equiv, PiLp.continuousLinearEquiv,
        PiLp.coe_continuousLinearEquiv] using hdot
    simpa [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm] using hdot'
  have hyRange : (EuclideanSpace.equiv ι ℝ).symm y ∈ T.range := by
    rw [← hTsym.adjoint_eq, ← LinearMap.orthogonal_ker]
    exact hyOrth
  obtain ⟨z, hz⟩ := hyRange
  refine ⟨EuclideanSpace.equiv ι ℝ z, ?_⟩
  have hz' : (EuclideanSpace.equiv ι ℝ).symm
      (Q.mulVec (EuclideanSpace.equiv ι ℝ z)) = (EuclideanSpace.equiv ι ℝ).symm y := by
    rw [← euclidean_mulVec_eq Q (EuclideanSpace.equiv ι ℝ z)]
    simpa [T] using hz
  have hz'' := congrArg (EuclideanSpace.equiv ι ℝ) hz'
  simpa using hz''

private theorem neutral_dual_bdd {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) (D : (ι → ℝ) → ℝ) (Q : Matrix A A ℝ)
    (hQ : Q.transpose = Q) (hform : ∀ f, D f = realForm A Q f)
    (hD : ∀ f, 0 ≤ D f) (hker : constantKernel A D)
    (y : ι → ℝ) (hy : neutral A y) :
    BddAbove (Set.range fun f : ι → ℝ =>
      2 * (∑ i ∈ A, y i * f i) - D f) := by
  classical
  let Dact : (A → ℝ) → ℝ := fun x => D (padVector A x)
  let yact : A → ℝ := activeVector A y
  have hQps : Q.PosSemidef := matrix_posSemidef_of_form A Q hQ D hform hD
  have hformAct : ∀ x, Dact x = dotProduct x (Q.mulVec x) := by
    intro x
    calc
      Dact x = D (padVector A x) := rfl
      _ = realForm A Q (padVector A x) := hform _
      _ = dotProduct x (Q.mulVec x) := by
        rw [realForm_eq_dotProduct, active_padVector]
  have hkerAct : constantKernel Finset.univ Dact := by
    intro x
    constructor
    · intro hx
      have hDx : D (padVector A x) = 0 := hx
      obtain ⟨c, hc⟩ := (hker (padVector A x)).mp hDx
      refine ⟨c, ?_⟩
      intro i hi
      simpa [padVector, i.property] using hc i.val i.property
    · rintro ⟨c, hc⟩
      apply (hker (padVector A x)).mpr
      refine ⟨c, ?_⟩
      intro i hi
      simpa [padVector, hi] using hc ⟨i, hi⟩ (Finset.mem_univ _)
  have hySum : ∑ i : A, yact i = 0 := by
    change (∑ i ∈ A.attach, y i.val) = 0
    rw [Finset.sum_attach A]
    exact hy.2
  obtain ⟨z, hz⟩ := matrix_neutral_has_solution Q hQ Dact hformAct hkerAct yact hySum
  refine ⟨dotProduct z (Q.mulVec z), ?_⟩
  rintro value ⟨f, rfl⟩
  let x := activeVector A f
  have hPair : (∑ i ∈ A, y i * f i) = dotProduct yact x := by
    rw [← Finset.sum_attach A]
    simp [x, yact, activeVector, dotProduct]
  have hEnergy : D f = dotProduct x (Q.mulVec x) := by
    calc
      D f = realForm A Q f := hform f
      _ = dotProduct x (Q.mulVec x) := by rw [realForm_eq_dotProduct]
  have hcross : dotProduct x (Q.mulVec z) = dotProduct z (Q.mulVec x) := by
    simpa [star_trivial] using (realMatrix_hermitian Q hQ).star_dotProduct_mulVec_comm x z
  have hidentity : 2 * dotProduct yact x - dotProduct x (Q.mulVec x) =
      dotProduct z (Q.mulVec z) - dotProduct (x - z) (Q.mulVec (x - z)) := by
    rw [← hz]
    rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub]
    rw [dotProduct_comm (Q.mulVec z) x, hcross]
    ring
  have hnonneg : 0 ≤ dotProduct (x - z) (Q.mulVec (x - z)) := by
    simpa [star_trivial] using hQps.dotProduct_mulVec_nonneg (x - z)
  have hbound : 2 * dotProduct yact x - dotProduct x (Q.mulVec x) ≤
      dotProduct z (Q.mulVec z) := by
    rw [hidentity]
    linarith
  change 2 * (∑ i ∈ A, y i * f i) - D f ≤ dotProduct z (Q.mulVec z)
  rw [hPair, hEnergy]
  exact hbound

private theorem retained_schur_result {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Finset ι) (hBA : B ⊆ A) (D : (ι → ℝ) → ℝ)
    (Q : Matrix A A ℝ) (hQ : Q.transpose = Q) (hform : ∀ f, D f = realForm A Q f)
    (hD : ∀ f, 0 ≤ D f) (hker : constantKernel A D) (hB : B.Nonempty) :
    constantKernel B (schurEnergy B D) ∧
      FiniteRealForm B (schurEnergy B D) ∧
      ∀ f : ι → ℝ, ∃ F : ι → ℝ, (∀ i ∈ B, F i = f i) ∧
        D F = schurEnergy B D f := by
  classical
  let e := splitEquiv A B hBA
  let Qs := Q.submatrix e e
  let Del := deletedBlock hBA Q
  let Cr := crossBlock hBA Q
  let Ret := retainedBlock hBA Q
  let Dact : (A → ℝ) → ℝ := fun x => D (padVector A x)
  have hQps : Q.PosSemidef := matrix_posSemidef_of_form A Q hQ D hform hD
  have hformAct : ∀ x, Dact x = dotProduct x (Q.mulVec x) := by
    intro x
    calc
      Dact x = D (padVector A x) := rfl
      _ = realForm A Q (padVector A x) := hform _
      _ = dotProduct x (Q.mulVec x) := by
        rw [realForm_eq_dotProduct, active_padVector]
  have hkerAct : constantKernel Finset.univ Dact := by
    intro x
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := (hker (padVector A x)).mp hx
      refine ⟨c, ?_⟩
      intro i hi
      simpa [padVector, i.property] using hc i.val i.property
    · rintro ⟨c, hc⟩
      apply (hker (padVector A x)).mpr
      refine ⟨c, ?_⟩
      intro i hi
      simpa [padVector, hi] using hc ⟨i, hi⟩ (Finset.mem_univ _)
  have hkerQ : ∀ x, qForm Q x = 0 ↔ ∃ c : ℝ, ∀ i, x i = c := by
    intro x
    exact matrix_form_zero_iff_constant Q Dact hformAct hkerAct x
  have hQsplit : Qs.PosSemidef := hQps.submatrix e
  have hDel : Del.PosDef := deletedBlock_posDef A B hBA Q hQps hkerQ hB
  letI : Invertible Del := hDel.isUnit.invertible
  have hCrStar : Cr.conjTranspose = Cr.transpose := by
    ext i j
    simp [Matrix.conjTranspose]
  have hblocksTranspose : Qs = Matrix.fromBlocks Del Cr Cr.transpose Ret := by
    simpa [Qs, Del, Cr, Ret, e] using splitBlockMatrix hBA Q hQ
  have hblocks : Qs = Matrix.fromBlocks Del Cr Cr.conjTranspose Ret := by
    simpa [hCrStar] using hblocksTranspose
  have hblockps : (Matrix.fromBlocks Del Cr Cr.conjTranspose Ret).PosSemidef := by
    rw [← hblocks]
    exact hQsplit
  have hSstar : (Ret - Cr.conjTranspose * Del⁻¹ * Cr).PosSemidef :=
    (Matrix.PosDef.fromBlocks₁₁ Cr Ret hDel).mp hblockps
  let S : Matrix B B ℝ := Ret - Cr.transpose * Del⁻¹ * Cr
  have hSps : S.PosSemidef := by
    simpa [S, hCrStar] using hSstar
  have hSconj : S.conjTranspose = S.transpose := by
    ext i j
    simp [Matrix.conjTranspose]
  have hSsym : S.transpose = S := by
    calc
      S.transpose = S.conjTranspose := hSconj.symm
      _ = S := hSps.isHermitian
  have hmin : ∀ f : ι → ℝ,
      ∃ F : ι → ℝ, (∀ i ∈ B, F i = f i) ∧
        D F = qForm S (activeVector B f) ∧
        ∀ F' : ι → ℝ, (∀ i ∈ B, F' i = f i) → D F ≤ D F' := by
    intro f
    let y := activeVector B f
    let x₀ := -((Del⁻¹ * Cr).mulVec y)
    let g := Sum.elim x₀ y
    let u := g ∘ e.symm
    let F := padVector A u
    have heR (b : B) : e (Sum.inr b) = ⟨b.val, hBA b.property⟩ := by
      simp [e, splitEquiv]
    have heRinv (b : B) : e.symm ⟨b.val, hBA b.property⟩ = Sum.inr b := by
      apply e.injective
      simp [heR]
    have hrestrict : ∀ i ∈ B, F i = f i := by
      intro i hi
      have hval : u ⟨i, hBA hi⟩ = f i := by
        dsimp [u, g, y]
        rw [heRinv ⟨i, hi⟩]
        rfl
      simp [F, padVector, hBA hi, hval]
    have hcomp : u ∘ e = g := by
      funext s
      simp [u]
    have hqReindex : qForm Qs g = qForm Q u := by
      have hq := qForm_submatrix_equiv e Q u
      rw [hcomp] at hq
      exact hq
    have hsplitMin := splitQuadratic Qs Del Cr Ret hblocksTranspose hDel.isHermitian x₀ y
    have hqMin : qForm Qs g = qForm S y := by
      calc
        qForm Qs g = qForm Del (x₀ + (Del⁻¹ * Cr).mulVec y) +
            qForm S y := by
          simpa [S] using hsplitMin
        _ = qForm S y := by simp [x₀, qForm]
    have hDF : D F = qForm Q u := by
      calc
        D F = realForm A Q F := hform F
        _ = qForm Q (activeVector A F) := by rw [realForm_eq_dotProduct]; rfl
        _ = qForm Q u := by
          rw [show activeVector A F = u from by
            dsimp [F]
            exact active_padVector A u]
    refine ⟨F, hrestrict, ?_, ?_⟩
    · calc
        D F = qForm Q u := hDF
        _ = qForm Qs g := hqReindex.symm
        _ = qForm S y := hqMin
    · intro F' hF'
      let v := activeVector A F' ∘ e
      let xl := v ∘ Sum.inl
      have hright : v ∘ Sum.inr = y := by
        funext b
        change F' (e (Sum.inr b)).val = f b.val
        rw [heR b]
        exact hF' b.val b.property
      have hv : v = Sum.elim xl y := by
        funext s
        cases s with
        | inl d => rfl
        | inr b => exact congrFun hright b
      have hqReindex' : qForm Qs v = qForm Q (activeVector A F') := by
        have hq := qForm_submatrix_equiv e Q (activeVector A F')
        change qForm Qs v = qForm Q (activeVector A F')
        exact hq
      have hsplit := splitQuadratic Qs Del Cr Ret hblocksTranspose hDel.isHermitian xl y
      have hsplitV : qForm Qs v =
          qForm Del (xl + (Del⁻¹ * Cr).mulVec y) + qForm S y := by
        rw [hv]
        exact hsplit
      have hnonneg : 0 ≤ qForm Del (xl + (Del⁻¹ * Cr).mulVec y) := by
        simpa [qForm, star_trivial] using
          hDel.posSemidef.dotProduct_mulVec_nonneg (xl + (Del⁻¹ * Cr).mulVec y)
      have hstep : qForm S y ≤ qForm Qs v := by
        rw [hsplitV]
        linarith
      have hDF' : qForm Q (activeVector A F') = D F' := by
        calc
          qForm Q (activeVector A F') = realForm A Q F' :=
            (realForm_eq_dotProduct A Q F').symm
          _ = D F' := (hform F').symm
      calc
        D F = qForm S y := hDF.trans (hqReindex.symm.trans hqMin)
        _ ≤ qForm Qs v := hstep
        _ = qForm Q (activeVector A F') := hqReindex'
        _ = D F' := hDF'
  have hschurQ : ∀ f : ι → ℝ,
      schurEnergy B D f = qForm S (activeVector B f) := by
    intro f
    obtain ⟨F, hF, hEq, hminF⟩ := hmin f
    let values := D '' {G : ι → ℝ | ∀ i ∈ B, G i = f i}
    have hbelow : BddBelow values := ⟨0, by
      rintro x ⟨G, hG, rfl⟩
      exact hD G⟩
    have hne : values.Nonempty := by
      exact ⟨D f, ⟨f, (by intro i hi; rfl), rfl⟩⟩
    unfold schurEnergy
    change sInf values = qForm S (activeVector B f)
    apply le_antisymm
    · calc
        sInf values ≤ D F := csInf_le hbelow ⟨F, hF, rfl⟩
        _ = qForm S (activeVector B f) := hEq
    · apply le_csInf hne
      rintro x ⟨G, hG, rfl⟩
      rw [← hEq]
      exact hminF G hG
  have hschur : ∀ f : ι → ℝ, schurEnergy B D f = realForm B S f := by
    intro f
    calc
      schurEnergy B D f = qForm S (activeVector B f) := hschurQ f
      _ = realForm B S f := (realForm_eq_dotProduct B S f).symm
  have hkernelSchur : constantKernel B (schurEnergy B D) := by
    intro f
    constructor
    · intro hz
      have hqzero : qForm S (activeVector B f) = 0 := by rw [← hschurQ f]; exact hz
      obtain ⟨F, hF, hEq, _⟩ := hmin f
      have hDFzero : D F = 0 := by rw [hEq, hqzero]
      obtain ⟨c, hc⟩ := (hker F).mp hDFzero
      refine ⟨c, ?_⟩
      intro i hi
      calc
        f i = F i := (hF i hi).symm
        _ = c := hc i (hBA hi)
    · rintro ⟨c, hf⟩
      obtain ⟨F, hF, hEq, hminF⟩ := hmin f
      let Fconst : ι → ℝ := fun _ => c
      have hFconst : ∀ i ∈ B, Fconst i = f i := by
        intro i hi
        exact (hf i hi).symm
      have hDconst : D Fconst = 0 := (hker Fconst).mpr ⟨c, by
        intro i hi
        rfl⟩
      have hle : D F ≤ 0 := by
        rw [← hDconst]
        exact hminF Fconst hFconst
      have hDFzero : D F = 0 := le_antisymm (by linarith) (hD F)
      have hqzero : qForm S (activeVector B f) = 0 := by rw [← hEq]; exact hDFzero
      rw [hschurQ f]
      exact hqzero
  have hfiniteSchur : FiniteRealForm B (schurEnergy B D) := by
    refine ⟨S, hSsym, hschur⟩
  have hattain : ∀ f : ι → ℝ, ∃ F : ι → ℝ, (∀ i ∈ B, F i = f i) ∧
      D F = schurEnergy B D f := by
    intro f
    obtain ⟨F, hF, hEq, _⟩ := hmin f
    refine ⟨F, hF, ?_⟩
    calc
      D F = qForm S (activeVector B f) := hEq
      _ = schurEnergy B D f := (hschurQ f).symm
  exact ⟨hkernelSchur, hfiniteSchur, hattain⟩

theorem finiteFormInput_proof : FiniteFormInput := by
  classical
  intro ι hι hdec A D hfinite hD hker
  rcases hfinite with ⟨Q, hQ, hform⟩
  refine ⟨?_, ?_⟩
  · intro y hy
    exact neutral_dual_bdd A D Q hQ hform hD hker y hy
  · intro B hBA hB
    exact retained_schur_result A B hBA D Q hQ hform hD hker hB

end AndersonAC.SolS78
