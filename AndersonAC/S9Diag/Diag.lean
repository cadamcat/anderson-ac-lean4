import AndersonAC.S9Fin.HelperStatements

noncomputable section

open MeasureTheory OAI.Anderson
open Filter

namespace AndersonAC.SolS9

instance uniformSite_nullSingleton : NullSingletonClass uniformSite where
  measure_singleton := by
    intro x
    have hmap := uniformSite_map_val
    have hmeas : Measurable (fun v : SingleSite => (v : ℝ)) :=
      measurable_subtype_coe
    have hpre : (fun v : SingleSite => (v : ℝ)) ⁻¹' ({((x : ℝ))} : Set ℝ) = {x} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_singleton_iff]
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        rw [h]
    have h1 : uniformSite {x} =
        (uniformSite.map (fun v : SingleSite => (v : ℝ))) ({((x : ℝ))} : Set ℝ) := by
      rw [Measure.map_apply hmeas (measurableSet_singleton _), hpre]
    rw [h1, hmap]
    rw [Measure.smul_apply, smul_eq_mul]
    have hzero : (volume.restrict (Set.Icc (-1 : ℝ) 1)) ({((x : ℝ))} : Set ℝ) = 0 :=
      measure_singleton _
    rw [hzero, mul_zero]

/-- The random matrix. -/
def matOf {n : Type} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ) (coupling : ℝ) (ω : n → SingleSite) : Matrix n n ℂ :=
  K + (coupling : ℂ) • Matrix.diagonal (fun i => (((ω i : ℝ)) : ℂ))

lemma matOf_isUnit_iff_det_ne_zero {n : Type} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ) (coupling : ℝ) (ω : n → SingleSite) :
    IsUnit (matOf K coupling ω) ↔ (matOf K coupling ω).det ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

lemma continuous_matOf {n : Type} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ) (coupling : ℝ) :
    Continuous (fun ω : n → SingleSite => matOf K coupling ω) := by
  apply continuous_matrix
  intro i j
  unfold matOf
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · simp only [h, ite_true]
    fun_prop
  · simp only [h, ite_false]
    fun_prop

lemma measurable_detOf {n : Type} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ) (coupling : ℝ) :
    Measurable (fun ω : n → SingleSite => (matOf K coupling ω).det) :=
  (Continuous.matrix_det (continuous_matOf K coupling)).measurable

lemma measurableSet_isUnit_set {n : Type} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ) (coupling : ℝ) :
    MeasurableSet {ω : n → SingleSite | IsUnit (matOf K coupling ω)} := by
  have h : {ω : n → SingleSite | IsUnit (matOf K coupling ω)} =
      (fun ω : n → SingleSite => (matOf K coupling ω).det) ⁻¹' ({0}ᶜ : Set ℂ) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff, matOf_isUnit_iff_det_ne_zero]
  rw [h]
  exact (measurable_detOf K coupling) ((measurableSet_singleton 0).compl)

/-- Fixed base point with real value 0. -/
def s0 : SingleSite := ⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩

lemma s0_coe : (((s0 : ℝ)) : ℂ) = 0 := by
  simp [s0]

/-- Splitting equivalence at index 0. -/
def splitEquiv (k : ℕ) :
    (Fin (k + 1) → SingleSite) ≃ᵐ (SingleSite × (Fin k → SingleSite)) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => SingleSite) 0

lemma splitEquiv_symm_zero (k : ℕ) (s : SingleSite) (tail : Fin k → SingleSite) :
    (splitEquiv k).symm (s, tail) 0 = s := by
  rfl

lemma splitEquiv_symm_succAbove (k : ℕ) (s : SingleSite) (tail : Fin k → SingleSite)
    (j : Fin k) :
    (splitEquiv k).symm (s, tail) ((0 : Fin (k + 1)).succAbove j) = tail j := by
  rfl

lemma splitEquiv_symm_zero' (k : ℕ) (p : SingleSite × (Fin k → SingleSite)) :
    (splitEquiv k).symm p 0 = p.1 := by
  cases p with
  | mk s tail => rfl

lemma splitEquiv_symm_succAbove' (k : ℕ)
    (p : SingleSite × (Fin k → SingleSite)) (j : Fin k) :
    (splitEquiv k).symm p ((0 : Fin (k + 1)).succAbove j) = p.2 j := by
  cases p with
  | mk s tail => rfl

lemma mp_splitEquiv (k : ℕ) :
    MeasurePreserving (splitEquiv k)
      (Measure.pi (fun _ : Fin (k + 1) => uniformSite))
      (uniformSite.prod (Measure.pi (fun _ : Fin k => uniformSite))) := by
  unfold splitEquiv
  exact MeasureTheory.measurePreserving_piFinSuccAbove _ 0

lemma continuous_jointMat (k : ℕ) (K : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (coupling : ℝ) :
    Continuous (fun p : SingleSite × (Fin k → SingleSite) =>
      matOf K coupling ((splitEquiv k).symm p)) := by
  apply continuous_matrix
  intro i j
  unfold matOf
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true]
    by_cases hi0 : i = 0
    · subst hi0
      have heq : ∀ p : SingleSite × (Fin k → SingleSite),
          (splitEquiv k).symm p 0 = p.1 :=
        fun p => splitEquiv_symm_zero' k p
      simp only [heq]
      fun_prop
    · obtain ⟨jj, hjj⟩ := Fin.exists_succAbove_eq hi0
      have heq : ∀ p : SingleSite × (Fin k → SingleSite),
          (splitEquiv k).symm p i = p.2 jj := by
        intro p
        have h2 : (splitEquiv k).symm p ((0 : Fin (k + 1)).succAbove jj) = p.2 jj :=
          splitEquiv_symm_succAbove' k p jj
        rw [hjj] at h2
        exact h2
      simp only [heq]
      fun_prop
  · simp only [hij, ite_false]
    fun_prop

lemma measurableSet_jointIsUnit (k : ℕ) (K : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (coupling : ℝ) :
    MeasurableSet {p : SingleSite × (Fin k → SingleSite) |
      IsUnit (matOf K coupling ((splitEquiv k).symm p))} := by
  have h : {p : SingleSite × (Fin k → SingleSite) |
        IsUnit (matOf K coupling ((splitEquiv k).symm p))} =
      (fun p : SingleSite × (Fin k → SingleSite) =>
        (matOf K coupling ((splitEquiv k).symm p)).det) ⁻¹' ({0}ᶜ : Set ℂ) := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff, matOf_isUnit_iff_det_ne_zero]
  rw [h]
  exact (Continuous.matrix_det (continuous_jointMat k K coupling)).measurable
    ((measurableSet_singleton 0).compl)

/-- Standard basis row vector at 0. -/
def e0Vec (k : ℕ) : Fin (k + 1) → ℂ := fun j => if j = 0 then 1 else 0

lemma e0Vec_zero (k : ℕ) : e0Vec k 0 = 1 := by
  simp [e0Vec]

lemma e0Vec_ne (k : ℕ) {j : Fin (k + 1)} (hj : j ≠ 0) : e0Vec k j = 0 := by
  simp [e0Vec, hj]

/-- Base matrix with row 0 replaced by K's row; independent of head coordinate. -/
def Cmat (k : ℕ) (K : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (coupling : ℝ)
    (tail : Fin k → SingleSite) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  (matOf K coupling ((splitEquiv k).symm (s0, tail))).updateRow 0 (K 0)

def bDet (k : ℕ) (K : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (coupling : ℝ)
    (tail : Fin k → SingleSite) : ℂ :=
  (Cmat k K coupling tail).det

def aDet (k : ℕ) (K : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (coupling : ℝ)
    (tail : Fin k → SingleSite) : ℂ :=
  ((Cmat k K coupling tail).updateRow 0 (e0Vec k)).det

def Kminor (k : ℕ) (K : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Matrix (Fin k) (Fin k) ℂ :=
  K.submatrix Fin.succ Fin.succ

/-- Other rows do not see the head coordinate. -/
lemma matOf_otherRow_eq (k : ℕ) (K : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (coupling : ℝ) (s s' : SingleSite) (tail : Fin k → SingleSite)
    (i : Fin (k + 1)) (hi : i ≠ 0) (j : Fin (k + 1)) :
    (matOf K coupling ((splitEquiv k).symm (s, tail))) i j =
      (matOf K coupling ((splitEquiv k).symm (s', tail))) i j := by
  unfold matOf
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    -- need omega i equal
    obtain ⟨jj, hjj⟩ := Fin.exists_succAbove_eq hi
    have h1 : (splitEquiv k).symm (s, tail) i = tail jj := by
      have h2 : (splitEquiv k).symm (s, tail) ((0 : Fin (k + 1)).succAbove jj) =
          tail jj :=
        splitEquiv_symm_succAbove k s tail jj
      rw [hjj] at h2
      exact h2
    have h2 : (splitEquiv k).symm (s', tail) i = tail jj := by
      have h3 : (splitEquiv k).symm (s', tail) ((0 : Fin (k + 1)).succAbove jj) =
          tail jj :=
        splitEquiv_symm_succAbove k s' tail jj
      rw [hjj] at h3
      exact h3
    rw [h1, h2]
  · simp only [hij, ite_false]

/-- The full matrix is the base matrix with affine row 0. -/
lemma matOf_eq_Cmat_updateRow (k : ℕ) (K : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (coupling : ℝ) (s : SingleSite) (tail : Fin k → SingleSite) :
    matOf K coupling ((splitEquiv k).symm (s, tail)) =
      (Cmat k K coupling tail).updateRow 0
        (K 0 + ((coupling : ℂ) * (((s : ℝ)) : ℂ)) • e0Vec k) := by
  unfold Cmat
  apply Matrix.ext
  intro i j
  by_cases hi0 : i = 0
  · subst hi0
    -- row 0: both sides equal K 0 j + cc*s*(e0 j)
    rw [Matrix.updateRow_self]
    have h0 : (splitEquiv k).symm (s, tail) 0 = s :=
      splitEquiv_symm_zero k s tail
    have hL : (matOf K coupling ((splitEquiv k).symm (s, tail))) 0 j =
        K 0 j + (coupling : ℂ) * (if (0 : Fin (k + 1)) = j then ((((s : ℝ))) : ℂ) else 0) := by
      have hL0 : (matOf K coupling ((splitEquiv k).symm (s, tail))) 0 j =
          K 0 j + (coupling : ℂ) *
            (if (0 : Fin (k + 1)) = j then
              ((((splitEquiv k).symm (s, tail) 0 : ℝ)) : ℂ) else 0) := by
        unfold matOf
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply,
          smul_eq_mul]
      rw [h0] at hL0
      exact hL0
    have hR : ((K 0 + ((coupling : ℂ) * (((s : ℝ)) : ℂ)) • e0Vec k)) j =
        K 0 j + (coupling : ℂ) * ((((s : ℝ))) : ℂ) * (e0Vec k j) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [hL, hR]
    by_cases hj0 : (0 : Fin (k + 1)) = j
    · subst hj0
      simp only [ite_true, e0Vec_zero, mul_one]
    · simp only [hj0, ite_false, e0Vec_ne k (Ne.symm hj0), mul_zero, add_zero]
  · -- i ≠ 0: RHS is C i j = M(s0) i j = M(s) i j
    rw [Matrix.updateRow_ne hi0]
    rw [Matrix.updateRow_ne hi0]
    exact matOf_otherRow_eq k K coupling s s0 tail i hi0 j

/-- Determinant is affine in the head coordinate. -/
lemma det_affine (k : ℕ) (K : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (coupling : ℝ) (s : SingleSite) (tail : Fin k → SingleSite) :
    (matOf K coupling ((splitEquiv k).symm (s, tail))).det =
      bDet k K coupling tail +
        ((coupling : ℂ) * (((s : ℝ)) : ℂ)) * aDet k K coupling tail := by
  have hmat := matOf_eq_Cmat_updateRow k K coupling s tail
  unfold bDet aDet
  -- C's row 0 is K 0
  have hCrow : (Cmat k K coupling tail) 0 = K 0 := by
    unfold Cmat
    rw [Matrix.updateRow_self]
  have hCeq : (Cmat k K coupling tail).updateRow 0 (K 0) = Cmat k K coupling tail := by
    conv_lhs => rw [← hCrow]
    exact Matrix.updateRow_eq_self _ _
  rw [hmat]
  rw [Matrix.det_updateRow_add _ 0 (K 0)
    (((coupling : ℂ) * (((s : ℝ)) : ℂ)) • e0Vec k)]
  rw [hCeq, Matrix.det_updateRow_smul]

/-- The slope is the minor determinant. -/
lemma aDet_eq_minorDet (k : ℕ) (K : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (coupling : ℝ) (tail : Fin k → SingleSite) :
    aDet k K coupling tail = (matOf (Kminor k K) coupling tail).det := by
  unfold aDet Cmat Kminor matOf
  -- Let U be the matrix with row 0 = e0
  set U : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
    ((K + (coupling : ℂ) • Matrix.diagonal
      (fun i => ((((splitEquiv k).symm (s0, tail) i : ℝ)) : ℂ))).updateRow 0 (K 0)).updateRow 0
      (e0Vec k) with hU
  have hU0 : U 0 = e0Vec k := Matrix.updateRow_self
  have hdet : U.det = ∑ j : Fin (k + 1),
      (-1 : ℂ) ^ (j : ℕ) * U 0 j * (U.submatrix Fin.succ j.succAbove).det :=
    Matrix.det_succ_row_zero U
  -- Each term: U 0 j = e0Vec k j
  have hterm : ∀ j : Fin (k + 1),
      (-1 : ℂ) ^ (j : ℕ) * U 0 j * (U.submatrix Fin.succ j.succAbove).det =
        (if j = 0 then (U.submatrix Fin.succ (0 : Fin (k + 1)).succAbove).det else 0) := by
    intro j
    have h0j : U 0 j = e0Vec k j := by rw [hU0]
    simp only [e0Vec] at h0j
    by_cases hj0 : j = 0
    · subst hj0
      simp only [ite_true] at h0j ⊢
      rw [h0j]
      simp
    · simp only [hj0, ite_false] at h0j ⊢
      rw [h0j]
      ring
  rw [hdet]
  simp only [hterm]
  rw [Finset.sum_ite_eq' _ _ (fun _ => (U.submatrix Fin.succ (0 : Fin (k + 1)).succAbove).det)]
  simp only [Finset.mem_univ, ite_true]
  -- Now show minor equals matOf Kminor tail
  have hsucc : ((0 : Fin (k + 1)).succAbove) = Fin.succ := Fin.succAbove_zero
  rw [hsucc]
  congr 1
  apply Matrix.ext
  intro i' j'
  have hne : Fin.succ i' ≠ (0 : Fin (k + 1)) := Fin.succ_ne_zero _
  have hUij : U (Fin.succ i') (Fin.succ j') =
      K (Fin.succ i') (Fin.succ j') +
        (coupling : ℂ) *
          (if i' = j' then ((((tail i' : ℝ))) : ℂ) else 0) := by
    have h1 : U (Fin.succ i') (Fin.succ j') =
        (((K + (coupling : ℂ) • Matrix.diagonal
          (fun i => ((((splitEquiv k).symm (s0, tail) i : ℝ)) : ℂ))).updateRow 0 (K 0)))
          (Fin.succ i') (Fin.succ j') := by
      unfold U
      rw [Matrix.updateRow_ne hne]
    rw [h1]
    have h2 : (((K + (coupling : ℂ) • Matrix.diagonal
          (fun i => ((((splitEquiv k).symm (s0, tail) i : ℝ)) : ℂ))).updateRow 0 (K 0)))
          (Fin.succ i') (Fin.succ j') =
        K (Fin.succ i') (Fin.succ j') +
          (coupling : ℂ) *
            (if i' = j' then ((((tail i' : ℝ))) : ℂ) else 0) := by
      rw [Matrix.updateRow_ne hne]
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply,
        smul_eq_mul]
      by_cases hij : Fin.succ i' = Fin.succ j'
      · have hij' : i' = j' := Fin.succ_inj.mp hij
        subst hij'
        simp only [ite_true]
        have htail : (splitEquiv k).symm (s0, tail) (Fin.succ i') = tail i' := by
          have h1 : (splitEquiv k).symm (s0, tail)
              ((0 : Fin (k + 1)).succAbove i') = tail i' :=
            splitEquiv_symm_succAbove k s0 tail i'
          rw [hsucc] at h1
          exact h1
        rw [htail]
      · have hij' : i' ≠ j' := fun h => hij (congrArg Fin.succ h)
        simp only [hij, ite_false, hij', ite_false, mul_zero, add_zero]
    exact h2
  have hR : ((K.submatrix Fin.succ Fin.succ +
      (coupling : ℂ) • Matrix.diagonal (fun i => ((((tail i : ℝ))) : ℂ)))) i' j' =
      K (Fin.succ i') (Fin.succ j') +
        (coupling : ℂ) *
          (if i' = j' then ((((tail i' : ℝ))) : ℂ) else 0) := by
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply,
      Matrix.submatrix_apply, smul_eq_mul]
  have hsub : (U.submatrix Fin.succ Fin.succ) i' j' = U (Fin.succ i') (Fin.succ j') := by
    simp only [Matrix.submatrix_apply]
  rw [hsub, hUij, hR]

/-- For a good tail, almost every head gives invertibility. -/
lemma perTail_ae (k : ℕ) (K : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (coupling : ℝ) (hc : 0 < coupling) (tail : Fin k → SingleSite)
    (ha : aDet k K coupling tail ≠ 0) :
    ∀ᵐ s ∂uniformSite,
      IsUnit (matOf K coupling ((splitEquiv k).symm (s, tail))) := by
  have hcc : (coupling : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hc)
  -- Zero set is subsingleton
  set S : Set SingleSite :=
    {s : SingleSite | (matOf K coupling ((splitEquiv k).symm (s, tail))).det = 0} with hS
  have hsub : S.Subsingleton := by
    intro s1 hs1 s2 hs2
    simp only [hS, Set.mem_ofPred_eq] at hs1 hs2
    have h1 := det_affine k K coupling s1 tail
    have h2 := det_affine k K coupling s2 tail
    rw [hs1] at h1
    rw [hs2] at h2
    -- h1 : 0 = b + (cc*s1)*a, h2 : 0 = b + (cc*s2)*a
    -- So (cc*s1)*a = (cc*s2)*a
    have hXY : ((coupling : ℂ) * ((((s1 : ℝ))) : ℂ)) * aDet k K coupling tail =
        ((coupling : ℂ) * ((((s2 : ℝ))) : ℂ)) * aDet k K coupling tail := by
      have heq : bDet k K coupling tail +
          ((coupling : ℂ) * ((((s1 : ℝ))) : ℂ)) * aDet k K coupling tail =
          bDet k K coupling tail +
          ((coupling : ℂ) * ((((s2 : ℝ))) : ℂ)) * aDet k K coupling tail := by
        rw [← h1, ← h2]
      exact add_left_cancel_iff.mp heq
    have e1 : ((coupling : ℂ) * ((((s1 : ℝ))) : ℂ)) * aDet k K coupling tail =
        ((coupling : ℂ) * aDet k K coupling tail) * ((((s1 : ℝ))) : ℂ) := by ring
    have e2 : ((coupling : ℂ) * ((((s2 : ℝ))) : ℂ)) * aDet k K coupling tail =
        ((coupling : ℂ) * aDet k K coupling tail) * ((((s2 : ℝ))) : ℂ) := by ring
    rw [e1, e2] at hXY
    have hca : (coupling : ℂ) * aDet k K coupling tail ≠ 0 :=
      mul_ne_zero hcc ha
    have hz : ((((s1 : ℝ))) : ℂ) = ((((s2 : ℝ))) : ℂ) :=
      mul_left_cancel₀ hca hXY
    have hr : (s1 : ℝ) = (s2 : ℝ) := Complex.ofReal_injective hz
    exact Subtype.ext hr
  have hae : ∀ᵐ s ∂uniformSite, s ∉ S := by
    by_cases hne : S.Nonempty
    · obtain ⟨s0', hs0'⟩ := hne
      have hae_ne : ∀ᵐ s ∂uniformSite, s ≠ s0' := Measure.ae_ne _ s0'
      exact hae_ne.mono (fun s hs hsS => hs (hsub hsS hs0'))
    · have hempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have hall : ∀ s : SingleSite, s ∉ S := by
        rw [hempty]
        exact fun s => Set.notMem_empty s
      exact Filter.Eventually.of_forall hall
  -- Convert det≠0 to IsUnit
  have hdet : ∀ᵐ s ∂uniformSite,
      (matOf K coupling ((splitEquiv k).symm (s, tail))).det ≠ 0 := by
    -- s ∉ S means det ≠ 0
    exact hae.mono (fun s hs => by
      simp only [hS, Set.mem_ofPred_eq] at hs ⊢
      exact hs)
  exact hdet.mono (fun s hs => (matOf_isUnit_iff_det_ne_zero _ _ _).mpr hs)

theorem fin_invertible : ∀ (k : ℕ) (K : Matrix (Fin k) (Fin k) ℂ) (coupling : ℝ),
    0 < coupling →
    ∀ᵐ ω : Fin k → SingleSite ∂Measure.pi (fun _ => uniformSite),
      IsUnit (matOf K coupling ω) := by
  intro k
  induction k with
  | zero =>
    intro K coupling hc
    apply Filter.Eventually.of_forall
    intro ω
    rw [matOf_isUnit_iff_det_ne_zero]
    have hdet : (matOf K coupling ω).det = 1 := Matrix.det_fin_zero
    rw [hdet]
    exact one_ne_zero
  | succ k ih =>
    intro K coupling hc
    -- Good tails: minor nonzero via IH
    have hIH : ∀ (K' : Matrix (Fin k) (Fin k) ℂ) (coupling : ℝ), 0 < coupling →
        ∀ᵐ tail : Fin k → SingleSite ∂Measure.pi (fun _ => uniformSite),
          IsUnit (matOf K' coupling tail) := ih
    have hgood : ∀ᵐ tail : Fin k → SingleSite ∂Measure.pi (fun _ => uniformSite),
        aDet k K coupling tail ≠ 0 := by
      have h1 : ∀ᵐ tail : Fin k → SingleSite ∂Measure.pi (fun _ => uniformSite),
          IsUnit (matOf (Kminor k K) coupling tail) :=
        hIH (Kminor k K) coupling hc
      exact h1.mono (fun tail htail => by
        have hdet : (matOf (Kminor k K) coupling tail).det ≠ 0 :=
          (matOf_isUnit_iff_det_ne_zero _ _ _).mp htail
        have heq := aDet_eq_minorDet k K coupling tail
        rw [heq]
        exact hdet)
    -- Per-tail ae
    have hper : ∀ tail : Fin k → SingleSite, aDet k K coupling tail ≠ 0 →
        ∀ᵐ s ∂uniformSite,
          IsUnit (matOf K coupling ((splitEquiv k).symm (s, tail))) :=
      fun tail ha => perTail_ae k K coupling hc tail ha
    -- Combine to tail-outer ae
    have htail_outer : ∀ᵐ tail : Fin k → SingleSite ∂Measure.pi (fun _ => uniformSite),
        ∀ᵐ s ∂uniformSite,
          IsUnit (matOf K coupling ((splitEquiv k).symm (s, tail))) := by
      filter_upwards [hgood] with tail htail
      exact hper tail htail
    -- Swap to head-outer via ae_ae_comm
    have hmeas_joint : MeasurableSet
        {x : SingleSite × (Fin k → SingleSite) |
          IsUnit (matOf K coupling ((splitEquiv k).symm x))} :=
      measurableSet_jointIsUnit k K coupling
    have hmeas_comm : MeasurableSet
        {x : SingleSite × (Fin k → SingleSite) |
          (fun s tail => IsUnit (matOf K coupling ((splitEquiv k).symm (s, tail)))) x.1 x.2} :=
      hmeas_joint
    have hhead_outer : ∀ᵐ s ∂uniformSite, ∀ᵐ tail : Fin k → SingleSite
        ∂Measure.pi (fun _ => uniformSite),
          IsUnit (matOf K coupling ((splitEquiv k).symm (s, tail))) := by
      have hcomm := Measure.ae_ae_comm (μ := uniformSite)
        (ν := Measure.pi (fun _ : Fin k => uniformSite))
        (p := fun s tail => IsUnit (matOf K coupling ((splitEquiv k).symm (s, tail))))
        hmeas_comm
      -- hcomm : (∀ᵐ s, ∀ᵐ tail, p s tail) ↔ ∀ᵐ tail, ∀ᵐ s, p s tail
      -- We have tail-outer, need head-outer, so use.mpr? Check direction:
      -- ae_ae_comm : (∀ᵐ x ∂μ, ∀ᵐ y ∂ν, p x y) ↔ ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, p x y
      -- Here μ=head, ν=tail, so LHS = ∀ᵐ s, ∀ᵐ tail, RHS = ∀ᵐ tail, ∀ᵐ s.
      -- We have RHS (htail_outer), need LHS, so use.mpr? Actually.mp goes LHS→RHS,
      -- .mpr goes RHS→LHS. We have RHS, need LHS, so.mpr.
      exact hcomm.mpr htail_outer
    -- Joint ae on product via ae_prod_iff
    have hprod : ∀ᵐ p : SingleSite × (Fin k → SingleSite)
        ∂uniformSite.prod (Measure.pi (fun _ : Fin k => uniformSite)),
          IsUnit (matOf K coupling ((splitEquiv k).symm p)) := by
      have hiff := Measure.ae_prod_iff_ae_ae (μ := uniformSite)
        (ν := Measure.pi (fun _ : Fin k => uniformSite))
        (p := fun p : SingleSite × (Fin k → SingleSite) =>
          IsUnit (matOf K coupling ((splitEquiv k).symm p)))
        hmeas_joint
      -- hiff : (∀ᵐ p ∂prod, Q p) ↔ ∀ᵐ s, ∀ᵐ tail, Q (s, tail)
      -- Q (s, tail) = IsUnit (matOf... (e.symm (s, tail)))? Need to relate to hhead_outer
      -- hhead_outer is ∀ᵐ s, ∀ᵐ tail, IsUnit (matOf... (e.symm (s, tail)))
      -- which is ∀ᵐ s, ∀ᵐ tail, Q (s, tail) with Q (s,tail)=...? Since Q (s,tail) as
      -- Q applied to (s,tail) : Q (s,tail) = IsUnit (matOf... (e.symm (s,tail)))? Yes.
      rw [hiff]
      -- Need to convert hhead_outer (which is ∀ᵐ s, ∀ᵐ tail, P s tail) to
      -- ∀ᵐ s, ∀ᵐ tail, Q (s, tail) where Q (s,tail)=P s tail? They are same.
      -- hiff's RHS is ∀ᵐ s, ∀ᵐ tail, Q (s, tail) with Q (s,tail) = ...? Actually
      -- ae_prod_iff states RHS as ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, p (x, y) where p : α×β→Prop,
      -- here p = fun p => IsUnit... (e.symm p), so p (s, tail) = IsUnit... (e.symm (s,tail)).
      -- Good, matches hhead_outer (up to eta? (s,tail) as pair vs Prod.mk? Same.)
      exact hhead_outer
    -- Transfer back to pi via MeasurePreserving
    have hmp := mp_splitEquiv k
    have hmap_eq : Measure.map (splitEquiv k)
        (Measure.pi (fun _ : Fin (k + 1) => uniformSite)) =
        uniformSite.prod (Measure.pi (fun _ : Fin k => uniformSite)) :=
      hmp.map_eq
    have hae_map : ∀ᵐ p ∂Measure.map (splitEquiv k)
        (Measure.pi (fun _ : Fin (k + 1) => uniformSite)),
          IsUnit (matOf K coupling ((splitEquiv k).symm p)) := by
      rw [hmap_eq]
      exact hprod
    have hae_pi : ∀ᵐ ω : Fin (k + 1) → SingleSite
        ∂Measure.pi (fun _ => uniformSite),
          IsUnit (matOf K coupling ((splitEquiv k).symm ((splitEquiv k) ω))) := by
      have hmeas_ae : AEMeasurable (splitEquiv k)
          (Measure.pi (fun _ : Fin (k + 1) => uniformSite)) :=
        hmp.aemeasurable
      have hiff := ae_map_iff hmeas_ae hmeas_joint
      -- hiff : (∀ᵐ y ∂map e pi, Q y) ↔ ∀ᵐ x ∂pi, Q (e x)
      -- with Q y = IsUnit... (e.symm y), so Q (e ω) = IsUnit... (e.symm (e ω))
      rw [hiff] at hae_map
      exact hae_map
    -- e.symm (e ω) = ω
    have hfinal : ∀ᵐ ω : Fin (k + 1) → SingleSite
        ∂Measure.pi (fun _ => uniformSite),
          IsUnit (matOf K coupling ω) := by
      exact hae_pi.mono (fun ω hω => by
        have heq : (splitEquiv k).symm ((splitEquiv k) ω) = ω :=
          (splitEquiv k).symm_apply_apply ω
        rw [heq] at hω
        exact hω)
    exact hfinal

/-- Transfer from `Fin k` to arbitrary `n` via `equivFin`. -/
theorem diagonalInvertibility_proof : DiagonalInvertibilityStatement := by
  intro n _ _ K coupling hc
  -- k and equiv
  set k : ℕ := Fintype.card n with hk
  set e : n ≃ Fin k := Fintype.equivFin n with he
  -- Minor matrix on Fin k
  set K' : Matrix (Fin k) (Fin k) ℂ := K.submatrix e.symm e.symm with hK'
  have hFin := fin_invertible k K' coupling hc
  -- Equiv of function spaces
  -- piCongrLeft with f = e.symm : Fin k ≃ n maps Fin-functions to n-functions;
  -- its symm maps n-functions to Fin-functions.
  set E : (n → SingleSite) ≃ᵐ (Fin k → SingleSite) :=
    (MeasurableEquiv.piCongrLeft (fun _ : n => SingleSite) e.symm).symm with hE
  have hmp : MeasurePreserving E
      (Measure.pi (fun _ : n => uniformSite))
      (Measure.pi (fun _ : Fin k => uniformSite)) := by
    have h0 := MeasureTheory.measurePreserving_piCongrLeft
      (fun _ : n => uniformSite) (e.symm : Fin k ≃ n)
    -- h0 : MeasurePreserving (piCongrLeft _ e.symm) (pi Fin) (pi n)
    -- E is its symm, so MeasurePreserving E (pi n) (pi Fin) via symm
    unfold E
    exact h0.symm
  have hmap_eq : Measure.map E (Measure.pi (fun _ : n => uniformSite)) =
      Measure.pi (fun _ : Fin k => uniformSite) :=
    hmp.map_eq
  -- Measurability of Fin-side IsUnit set
  have hmeas_Fin : MeasurableSet {ω' : Fin k → SingleSite |
      IsUnit (matOf K' coupling ω')} :=
    measurableSet_isUnit_set K' coupling
  have hae_map : ∀ᵐ ω' ∂Measure.map E (Measure.pi (fun _ : n => uniformSite)),
      IsUnit (matOf K' coupling ω') := by
    rw [hmap_eq]
    exact hFin
  have hae_n : ∀ᵐ ω : n → SingleSite ∂Measure.pi (fun _ => uniformSite),
      IsUnit (matOf K' coupling (E ω)) := by
    have hmeas_ae : AEMeasurable E (Measure.pi (fun _ : n => uniformSite)) :=
      hmp.aemeasurable
    have hiff := ae_map_iff hmeas_ae hmeas_Fin
    rw [hiff] at hae_map
    exact hae_map
  -- Relate matOf K' (E ω) to matOf K ω via submatrix
  have hrel : ∀ ω : n → SingleSite,
      matOf K' coupling (E ω) = (matOf K coupling ω).submatrix e.symm e.symm := by
    intro ω
    have hE : ∀ i' : Fin k, (E ω) i' = ω (e.symm i') := by
      intro i'
      unfold E
      rfl
    apply Matrix.ext
    intro i' j'
    simp only [matOf, hK', Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply,
      Matrix.submatrix_apply, smul_eq_mul, hE i']
    by_cases hij : i' = j'
    · subst hij
      simp only [ite_true]
    · have hij2 : e.symm i' ≠ e.symm j' := fun h => hij (e.symm.injective h)
      simp only [hij, ite_false, hij2, ite_false, mul_zero, add_zero]
  -- IsUnit transfer via submatrix equiv
  have hIsUnit : ∀ ω : n → SingleSite,
      IsUnit (matOf K' coupling (E ω)) ↔ IsUnit (matOf K coupling ω) := by
    intro ω
    rw [hrel ω]
    exact Matrix.isUnit_submatrix_equiv e.symm e.symm
  exact hae_n.mono (fun ω hω => (hIsUnit ω).mp hω)

end AndersonAC.SolS9
