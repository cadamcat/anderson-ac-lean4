import AndersonAC.S45.Definitions
import AndersonAC.S45.SchurProof
import AndersonAC.S45.SingleDeletionProof

/-! Cumulative Schur identity (04-sweep.tex:291-296), proved by induction on the
step index. Generic part: elimination characterization of padded Schur complements
and the quotient property for one further pivot. -/

noncomputable section
open Matrix
open scoped BigOperators

namespace AndersonAC.AgentS45

open AndersonAC.S45

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace CumSchur

variable {P : Type*} [Fintype P] [DecidableEq P]

theorem sum_dite_mem {M : Type*} [AddCommMonoid M] (S : Finset P)
    (F : (j : P) → j ∈ S → M) :
    (∑ j, if hj : j ∈ S then F j hj else 0) = ∑ j : (↑S : Type _), F j.1 j.2 := by
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => dif_neg hj)]
  rw [← Finset.sum_coe_sort S]
  exact Finset.sum_congr rfl fun j _ => dif_pos j.2

theorem sum_split {M : Type*} [AddCommMonoid M] (E : Finset P) (f : P → M) :
    ∑ j, f j = ∑ j : (↑E : Type _), f j.1 + ∑ j : (↑(Eᶜ) : Type _), f j.1 := by
  rw [Finset.sum_coe_sort E f, Finset.sum_coe_sort Eᶜ f]
  exact (Finset.sum_add_sum_compl E f).symm

variable {𝕜 : Type*} [RCLike 𝕜]

theorem pad_apply_mem (S : Finset P) (M : Matrix S S 𝕜) (i j : P) (hi : i ∈ S) (hj : j ∈ S) :
    pad S M i j = M ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [pad, hi, hj]

theorem pad_apply_left (S : Finset P) (M : Matrix S S 𝕜) (i j : P) (hi : i ∉ S) :
    pad S M i j = 0 := by
  simp [pad, hi]

theorem pad_apply_right (S : Finset P) (M : Matrix S S 𝕜) (i j : P) (hj : j ∉ S) :
    pad S M i j = 0 := by
  unfold pad; split_ifs <;> rfl

theorem pad_mulVec_apply (S : Finset P) (M : Matrix S S 𝕜) (y : P → 𝕜) (i : P) :
    (pad S M *ᵥ y) i = if hi : i ∈ S then (M *ᵥ fun j : S => y j) ⟨i, hi⟩ else 0 := by
  by_cases hi : i ∈ S
  · rw [dif_pos hi]
    simp only [mulVec, dotProduct]
    have : ∀ j, pad S M i j * y j =
        if hj : j ∈ S then M ⟨i, hi⟩ ⟨j, hj⟩ * y j else 0 := by
      intro j
      by_cases hj : j ∈ S
      · rw [dif_pos hj, pad_apply_mem S M i j hi hj]
      · rw [dif_neg hj, pad_apply_right S M i j hj, zero_mul]
    simp only [this]
    exact sum_dite_mem S (fun j hj => M ⟨i, hi⟩ ⟨j, hj⟩ * y j)
  · rw [dif_neg hi]
    simp [mulVec, dotProduct, pad_apply_left S M i _ hi]

theorem pad_mulVec_congr (S : Finset P) (M : Matrix S S 𝕜) (y y' : P → 𝕜)
    (h : ∀ j ∈ S, y j = y' j) : pad S M *ᵥ y = pad S M *ᵥ y' := by
  funext i
  rw [pad_mulVec_apply, pad_mulVec_apply]
  have : (fun j : S => y j) = fun j : S => y' j := funext fun j => h j j.2
  rw [this]

/-- `A *ᵥ y` at row `i`, split along `E` and `Eᶜ`. -/
theorem mulVec_split (A : Matrix P P 𝕜) (E : Finset P) (y : P → 𝕜) (i : P) :
    (A *ᵥ y) i = (A.submatrix (fun _ : Unit => i) (fun j : E => j.val) *ᵥ
        (fun j : E => y j)) () +
      (A.submatrix (fun _ : Unit => i) (fun j : (↑(Eᶜ) : Type _) => j.val) *ᵥ
        (fun j : (↑(Eᶜ) : Type _) => y j)) () := by
  simp only [mulVec, dotProduct, submatrix_apply]
  exact sum_split E (fun j => A i j * y j)

/-- Rows in `E` of `A *ᵥ y`, in block form. -/
theorem rows_E (A : Matrix P P 𝕜) (E : Finset P) (y : P → 𝕜) (i : E) :
    (A *ᵥ y) i = (restrict A E *ᵥ fun j : E => y j) i +
      (A.submatrix (fun j : E => j.val) (fun j : (↑(Eᶜ) : Type _) => j.val) *ᵥ
        fun j : (↑(Eᶜ) : Type _) => y j) i := by
  simp only [mulVec, dotProduct, submatrix_apply, restrict]
  exact sum_split E (fun j => A i j * y j)

/-- Rows in `Eᶜ` of `A *ᵥ y`, in block form. -/
theorem rows_Ec (A : Matrix P P 𝕜) (E : Finset P) (y : P → 𝕜) (i : (↑(Eᶜ) : Type _)) :
    (A *ᵥ y) i = (A.submatrix (fun j : (↑(Eᶜ) : Type _) => j.val) (fun j : E => j.val) *ᵥ
        fun j : E => y j) i +
      (restrict A Eᶜ *ᵥ fun j : (↑(Eᶜ) : Type _) => y j) i := by
  simp only [mulVec, dotProduct, submatrix_apply, restrict]
  exact sum_split E (fun j => A i j * y j)

theorem inv_mulVec_cancel {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n 𝕜)
    (hM : IsUnit M) (u : n → 𝕜) : M⁻¹ *ᵥ (M *ᵥ u) = u := by
  rw [mulVec_mulVec, nonsing_inv_mul M ((isUnit_iff_isUnit_det M).mp hM), one_mulVec]

theorem mulVec_inv_cancel {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n 𝕜)
    (hM : IsUnit M) (u : n → 𝕜) : M *ᵥ (M⁻¹ *ᵥ u) = u := by
  rw [mulVec_mulVec, mul_nonsing_inv M ((isUnit_iff_isUnit_det M).mp hM), one_mulVec]

/-- Elimination characterization: if `y` is eliminated on `E`, its `Eᶜ` rows are given
by the padded Schur complement. -/
theorem schur_char (A : Matrix P P 𝕜) (E : Finset P) (hE : IsUnit (restrict A E))
    (y : P → 𝕜) (hy : ∀ i ∈ E, (A *ᵥ y) i = 0) (i : P) (hi : i ∉ E) :
    (A *ᵥ y) i = (pad Eᶜ (schur A E) *ᵥ y) i := by
  set u : E → 𝕜 := fun j => y j
  set w : (↑(Eᶜ) : Type _) → 𝕜 := fun j => y j
  set AEc := A.submatrix (fun j : E => j.val) (fun j : (↑(Eᶜ) : Type _) => j.val)
  set AcE := A.submatrix (fun j : (↑(Eᶜ) : Type _) => j.val) (fun j : E => j.val)
  have h0 : restrict A E *ᵥ u + AEc *ᵥ w = 0 := by
    funext j
    rw [Pi.add_apply, ← rows_E A E y j]
    exact hy j j.2
  have hu : u = -((restrict A E)⁻¹ *ᵥ (AEc *ᵥ w)) := by
    have : restrict A E *ᵥ u = -(AEc *ᵥ w) := eq_neg_of_add_eq_zero_left h0
    rw [← inv_mulVec_cancel _ hE u, this, mulVec_neg]
  have hic : i ∈ Eᶜ := Finset.mem_compl.mpr hi
  rw [pad_mulVec_apply, dif_pos hic]
  rw [show (A *ᵥ y) i = (A *ᵥ y) (⟨i, hic⟩ : (↑(Eᶜ) : Type _)) from rfl, rows_Ec A E y]
  change (AcE *ᵥ u) _ + (restrict A Eᶜ *ᵥ w) _ = (schur A E *ᵥ w) _
  rw [hu]
  simp only [schur, sub_mulVec, ← mulVec_mulVec, mulVec_neg, Pi.add_apply, Pi.sub_apply,
    Pi.neg_apply]
  ring

/-- Existence of the elimination. -/
theorem schur_elim (A : Matrix P P 𝕜) (E : Finset P) (hE : IsUnit (restrict A E))
    (v : P → 𝕜) : ∃ y : P → 𝕜, (∀ i ∉ E, y i = v i) ∧ ∀ i ∈ E, (A *ᵥ y) i = 0 := by
  set w : (↑(Eᶜ) : Type _) → 𝕜 := fun j => v j
  set AEc := A.submatrix (fun j : E => j.val) (fun j : (↑(Eᶜ) : Type _) => j.val)
  set u : E → 𝕜 := -((restrict A E)⁻¹ *ᵥ (AEc *ᵥ w))
  refine ⟨fun i => if hi : i ∈ E then u ⟨i, hi⟩ else v i, fun i hi => dif_neg hi, ?_⟩
  intro i hi
  rw [show (A *ᵥ _) i = (A *ᵥ _) (⟨i, hi⟩ : E) from rfl, rows_E]
  have hu : (fun j : E => (fun i => if hi : i ∈ E then u ⟨i, hi⟩ else v i) j.val) = u := by
    funext j; simp [j.2]
  have hw : (fun j : (↑(Eᶜ) : Type _) =>
      (fun i => if hi : i ∈ E then u ⟨i, hi⟩ else v i) j.val) = w := by
    funext j
    have : j.val ∉ E := Finset.mem_compl.mp j.2
    simp [this, w]
  rw [hu, hw]
  change (restrict A E *ᵥ u) _ + (AEc *ᵥ w) _ = 0
  simp only [u, mulVec_neg, mulVec_inv_cancel _ hE, Pi.neg_apply, neg_add_cancel]

/-- Vectors supported in `S` (zero outside). -/
def padVec (S : Finset P) (w : S → 𝕜) : P → 𝕜 := fun i => if hi : i ∈ S then w ⟨i, hi⟩ else 0

theorem padVec_restrict (S : Finset P) (w : S → 𝕜) : (fun j : S => padVec S w j) = w := by
  funext j; simp [padVec, j.2]

theorem restrict_mulVec_eq (A : Matrix P P 𝕜) (S : Finset P) (y : P → 𝕜)
    (hy : ∀ j ∉ S, y j = 0) (i : S) :
    (restrict A S *ᵥ fun j : S => y j) i = (A *ᵥ y) i := by
  rw [rows_E A S y i]
  have : (fun j : (↑(Sᶜ) : Type _) => y j) = 0 := by
    funext j; exact hy j (Finset.mem_compl.mp j.2)
  rw [this, mulVec_zero, Pi.zero_apply, add_zero]

/-- Invertibility of the restriction to `E ∪ F` from that on `E` and of the padded Schur
complement on `F`. -/
theorem isUnit_union (A : Matrix P P 𝕜) (E F : Finset P) (hdisj : Disjoint E F)
    (hE : IsUnit (restrict A E)) (hF : IsUnit (restrict (pad Eᶜ (schur A E)) F)) :
    IsUnit (restrict A (E ∪ F)) := by
  rw [← mulVec_injective_iff_isUnit]
  have hinjE := (mulVec_injective_iff_isUnit).mpr hE
  have hinjF := (mulVec_injective_iff_isUnit).mpr hF
  -- kernel is trivial
  suffices hker : ∀ w, restrict A (E ∪ F) *ᵥ w = 0 → w = 0 by
    intro w1 w2 h
    have := hker (w1 - w2) (by rw [mulVec_sub, h, sub_self])
    exact sub_eq_zero.mp this
  intro w hw
  set y := padVec (E ∪ F) w with hydef
  have hy0 : ∀ j ∉ E ∪ F, y j = 0 := fun j hj => by simp [hydef, padVec, hj]
  have hAy : ∀ i ∈ E ∪ F, (A *ᵥ y) i = 0 := by
    intro i hi
    rw [← restrict_mulVec_eq A (E ∪ F) y hy0 ⟨i, hi⟩, hydef, padVec_restrict, hw]
    rfl
  set S := pad Eᶜ (schur A E)
  -- y vanishes on F
  have hyF : ∀ j ∈ F, y j = 0 := by
    let z : P → 𝕜 := fun j => if j ∈ F then y j else 0
    have hz0 : ∀ j ∉ F, z j = 0 := fun j hj => by simp [z, hj]
    have hSz : S *ᵥ z = S *ᵥ y := by
      apply pad_mulVec_congr
      intro j hj
      have hjE : j ∉ E := Finset.mem_compl.mp hj
      by_cases hjF : j ∈ F
      · simp [z, hjF]
      · simp only [z, hjF, if_false]
        exact (hy0 j (by simp [hjE, hjF])).symm
    have hzero : restrict S F *ᵥ (fun j : F => z j) = 0 := by
      funext i
      rw [restrict_mulVec_eq S F z hz0 i, hSz]
      have hiE : (i : P) ∉ E := Finset.disjoint_right.mp hdisj i.2
      rw [← schur_char A E hE y (fun j hj => hAy j (Finset.mem_union_left F hj)) i hiE]
      exact hAy i (Finset.mem_union_right E i.2)
    have := hinjF (hzero.trans (mulVec_zero _).symm)
    intro j hj
    have := congrFun this ⟨j, hj⟩
    simpa [z, hj] using this
  have hyE0 : ∀ j ∉ E, y j = 0 := by
    intro j hj
    by_cases hjF : j ∈ F
    · exact hyF j hjF
    · exact hy0 j (by simp [hj, hjF])
  have hzeroE : restrict A E *ᵥ (fun j : E => y j) = 0 := by
    funext i
    rw [restrict_mulVec_eq A E y hyE0 i]
    exact hAy i (Finset.mem_union_left F i.2)
  have hyE := hinjE (hzeroE.trans (mulVec_zero _).symm)
  funext j
  have hj := j.2
  have : y j = 0 := by
    by_cases hjE : (j : P) ∈ E
    · simpa using congrFun hyE ⟨j, hjE⟩
    · exact hyE0 j hjE
  simpa [hydef, padVec, hj] using this

/-- Quotient property of padded Schur complements. -/
theorem schur_union (A : Matrix P P 𝕜) (E F : Finset P) (hdisj : Disjoint E F)
    (hE : IsUnit (restrict A E)) (hF : IsUnit (restrict (pad Eᶜ (schur A E)) F)) :
    pad (E ∪ F)ᶜ (schur A (E ∪ F)) = pad Fᶜ (schur (pad Eᶜ (schur A E)) F) := by
  have hEF := isUnit_union A E F hdisj hE hF
  set S := pad Eᶜ (schur A E)
  have hvec : ∀ v, pad (E ∪ F)ᶜ (schur A (E ∪ F)) *ᵥ v = pad Fᶜ (schur S F) *ᵥ v := by
    intro v
    obtain ⟨y, hyv, hAy⟩ := schur_elim A (E ∪ F) hEF v
    let y'' : P → 𝕜 := fun j => if j ∈ E then v j else y j
    have hSy : S *ᵥ y'' = S *ᵥ y := by
      apply pad_mulVec_congr
      intro j hj
      simp [y'', Finset.mem_compl.mp hj]
    have hcharE : ∀ i ∉ E, (A *ᵥ y) i = (S *ᵥ y) i :=
      schur_char A E hE y (fun j hj => hAy j (Finset.mem_union_left F hj))
    have hS0 : ∀ i ∈ F, (S *ᵥ y'') i = 0 := by
      intro i hi
      rw [hSy, ← hcharE i (Finset.disjoint_right.mp hdisj hi)]
      exact hAy i (Finset.mem_union_right E hi)
    have hcharF := schur_char S F hF y'' hS0
    have hy''v : ∀ j ∈ Fᶜ, y'' j = v j := by
      intro j hj
      by_cases hjE : j ∈ E
      · simp [y'', hjE]
      · simp only [y'', hjE, if_false]
        exact hyv j (by simp [hjE, Finset.mem_compl.mp hj])
    have hyv' : ∀ j ∈ (E ∪ F)ᶜ, y j = v j := fun j hj => hyv j (Finset.mem_compl.mp hj)
    funext i
    by_cases hiF : i ∈ F
    · rw [pad_mulVec_apply, dif_neg (by simp [hiF]), pad_mulVec_apply,
        dif_neg (by simp [hiF])]
    · rw [← pad_mulVec_congr Fᶜ (schur S F) y'' v hy''v, ← hcharF i hiF, hSy]
      by_cases hiE : i ∈ E
      · rw [pad_mulVec_apply, dif_neg (by simp [hiE]), pad_mulVec_apply,
          dif_neg (by simp [hiE])]
      · rw [← hcharE i hiE, ← pad_mulVec_congr _ _ y v hyv',
          schur_char A (E ∪ F) hEF y hAy i (by simp [hiE, hiF])]
  exact ext_of_mulVec_single fun j => hvec _

/-! ### Pad/mask algebra -/

theorem pad_sub (S : Finset P) (X Y : Matrix S S 𝕜) : pad S (X - Y) = pad S X - pad S Y := by
  ext i j
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · simp only [Matrix.sub_apply, pad_apply_mem _ _ _ _ hi hj]
    · simp only [Matrix.sub_apply, pad_apply_right _ _ _ _ hj, sub_zero]
  · simp only [Matrix.sub_apply, pad_apply_left _ _ _ _ hi, sub_zero]

theorem pad_add (S : Finset P) (X Y : Matrix S S 𝕜) : pad S (X + Y) = pad S X + pad S Y := by
  ext i j
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · simp only [Matrix.add_apply, pad_apply_mem _ _ _ _ hi hj]
    · simp only [Matrix.add_apply, pad_apply_right _ _ _ _ hj, add_zero]
  · simp only [Matrix.add_apply, pad_apply_left _ _ _ _ hi, add_zero]

theorem pad_neg (S : Finset P) (X : Matrix S S 𝕜) : pad S (-X) = -pad S X := by
  ext i j
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · simp only [Matrix.neg_apply, pad_apply_mem _ _ _ _ hi hj]
    · simp only [Matrix.neg_apply, pad_apply_right _ _ _ _ hj, neg_zero]
  · simp only [Matrix.neg_apply, pad_apply_left _ _ _ _ hi, neg_zero]

theorem mask_sub (S : Finset P) (X Y : Matrix P P 𝕜) : mask S (X - Y) = mask S X - mask S Y := by
  unfold mask; rw [← pad_sub]; rfl

theorem mask_add (S : Finset P) (X Y : Matrix P P 𝕜) : mask S (X + Y) = mask S X + mask S Y := by
  unfold mask; rw [← pad_add]; rfl

theorem mask_neg (S : Finset P) (X : Matrix P P 𝕜) : mask S (-X) = -mask S X := by
  unfold mask; rw [← pad_neg]; rfl

theorem mask_apply_mem (S : Finset P) (X : Matrix P P 𝕜) (i j : P) (hi : i ∈ S) (hj : j ∈ S) :
    mask S X i j = X i j := by
  simp [mask, pad, restrict, hi, hj]

theorem mask_apply_left (S : Finset P) (X : Matrix P P 𝕜) (i j : P) (hi : i ∉ S) :
    mask S X i j = 0 := by
  simp [mask, pad, hi]

theorem mask_apply_right (S : Finset P) (X : Matrix P P 𝕜) (i j : P) (hj : j ∉ S) :
    mask S X i j = 0 := by
  unfold mask; exact pad_apply_right S _ i j hj

/-- `mask T (pad U (restrict X U)) = mask T X` for `T ⊆ U`. -/
theorem mask_mask (T U : Finset P) (hTU : T ⊆ U) (X : Matrix P P 𝕜) :
    mask T (mask U X) = mask T X := by
  ext i j
  by_cases hi : i ∈ T
  · by_cases hj : j ∈ T
    · rw [mask_apply_mem T _ i j hi hj, mask_apply_mem T _ i j hi hj,
        mask_apply_mem U _ i j (hTU hi) (hTU hj)]
    · rw [mask_apply_right T _ i j hj, mask_apply_right T _ i j hj]
  · rw [mask_apply_left T _ i j hi, mask_apply_left T _ i j hi]

theorem mask_pad_restrict (T U : Finset P) (hTU : T ⊆ U) (X : Matrix P P 𝕜) :
    mask T (pad U (restrict X U)) = mask T X :=
  mask_mask T U hTU X

theorem mask_idem (S : Finset P) (X : Matrix P P 𝕜) : mask S (mask S X) = mask S X :=
  mask_mask S S le_rfl X

theorem restrict_pad (S : Finset P) (X : Matrix S S 𝕜) : restrict (pad S X) S = X := by
  ext i j
  exact pad_apply_mem S X i j i.2 j.2

theorem restrict_one (S : Finset P) : restrict (1 : Matrix P P 𝕜) S = 1 := by
  ext i j
  change (1 : Matrix P P 𝕜) i j = (1 : Matrix S S 𝕜) i j
  by_cases h : i = j
  · subst h; rw [one_apply_eq, one_apply_eq]
  · rw [one_apply_ne h, one_apply_ne (fun e => h (Subtype.ext e))]

theorem mask_pad (S : Finset P) (X : Matrix S S 𝕜) : mask S (pad S X) = pad S X := by
  unfold mask; rw [restrict_pad]

theorem mask_one_sub_pad (S : Finset P) (X : Matrix S S 𝕜) :
    mask S (1 - pad S X) = pad S (1 - X) := by
  unfold mask
  have : restrict (1 - pad S X) S = 1 - X := by
    rw [show restrict (1 - pad S X) S = restrict 1 S - restrict (pad S X) S from rfl,
      restrict_one, restrict_pad]
  rw [this]

theorem mask_univ (X : Matrix P P 𝕜) : mask Finset.univ X = X := by
  ext i j; exact mask_apply_mem _ X i j (Finset.mem_univ i) (Finset.mem_univ j)

/-! ### Singleton Schur complements -/

instance subsingleton_singleton (x : P) : Subsingleton (↑({x} : Finset P) : Type _) :=
  ⟨fun a b => Subtype.ext ((Finset.mem_singleton.mp a.2).trans (Finset.mem_singleton.mp b.2).symm)⟩

theorem restrict_singleton_mul (N : Matrix P P 𝕜) (x : P) (hN : N x x ≠ 0) :
    restrict N {x} * (Matrix.of fun _ _ => (N x x)⁻¹ : Matrix (↑({x} : Finset P) : Type _) (↑({x} : Finset P) : Type _) 𝕜) = 1 := by
  ext a b
  have ha : (a : P) = x := Finset.mem_singleton.mp a.2
  have hab : a = b := Subsingleton.elim a b
  subst hab
  rw [mul_apply, one_apply_eq, Fintype.sum_subsingleton _ a]
  simp only [restrict, submatrix_apply, of_apply, ha]
  exact mul_inv_cancel₀ hN

theorem inv_restrict_singleton (N : Matrix P P 𝕜) (x : P) (hN : N x x ≠ 0) :
    (restrict N {x})⁻¹ = (Matrix.of fun _ _ => (N x x)⁻¹ : Matrix (↑({x} : Finset P) : Type _) (↑({x} : Finset P) : Type _) 𝕜) :=
  inv_eq_right_inv (restrict_singleton_mul N x hN)

theorem isUnit_restrict_singleton (N : Matrix P P 𝕜) (x : P) (hN : N x x ≠ 0) :
    IsUnit (restrict N {x}) := by
  have h := restrict_singleton_mul N x hN
  exact ⟨⟨_, _, h, mul_eq_one_comm.mp h⟩, rfl⟩

theorem schur_singleton_apply (N : Matrix P P 𝕜) (x : P) (hN : N x x ≠ 0) (i j : P)
    (hi : i ≠ x) (hj : j ≠ x) :
    pad {x}ᶜ (schur N {x}) i j = N i j - N i x * (N x x)⁻¹ * N x j := by
  have hi' : i ∈ ({x} : Finset P)ᶜ := by simpa using hi
  have hj' : j ∈ ({x} : Finset P)ᶜ := by simpa using hj
  rw [pad_apply_mem _ _ i j hi' hj']
  unfold schur
  rw [inv_restrict_singleton N x hN]
  simp only [Matrix.sub_apply, mul_apply, of_apply,
    restrict, submatrix_apply,
    Fintype.sum_subsingleton _ (⟨x, Finset.mem_singleton_self x⟩ : (↑({x} : Finset P) : Type _))]

theorem isUnit_restrict_empty (A : Matrix P P 𝕜) : IsUnit (restrict A ∅) := by
  rw [← mulVec_injective_iff_isUnit]
  intro w1 w2 _
  funext j
  exact absurd j.2 (Finset.notMem_empty _)

theorem pad_schur_empty (A : Matrix P P 𝕜) : pad (∅ : Finset P)ᶜ (schur A ∅) = A := by
  have : IsEmpty (↑(∅ : Finset P) : Type _) := ⟨fun a => Finset.notMem_empty _ a.2⟩
  ext i j
  rw [pad_apply_mem _ _ i j (by simp) (by simp)]
  simp [schur, restrict, mul_apply]

/-- One elimination step plus a supported correction. -/
theorem schur_step (A Jm : Matrix P P 𝕜) (E G : Finset P) (x : P) (hx : x ∉ E)
    (hG : G = E ∪ {x}) (hE : IsUnit (restrict A E)) (hpiv : pad Eᶜ (schur A E) x x ≠ 0)
    (hJ : mask Gᶜ Jm = Jm) :
    IsUnit (restrict (A + Jm) G) ∧
      pad Gᶜ (schur (A + Jm) G) = pad {x}ᶜ (schur (pad Eᶜ (schur A E)) {x}) + Jm := by
  subst hG
  have hdisj : Disjoint E {x} := Finset.disjoint_singleton_right.mpr hx
  have hF := isUnit_restrict_singleton _ x hpiv
  have hres : restrict (A + Jm) (E ∪ {x}) = restrict A (E ∪ {x}) := by
    ext i j
    have hi : (i : P) ∉ (E ∪ {x})ᶜ := fun h => (Finset.mem_compl.mp h) i.2
    change A i j + Jm i j = A i j
    rw [← hJ, mask_apply_left _ _ _ _ hi, add_zero]
  refine ⟨by rw [hres]; exact isUnit_union A E {x} hdisj hE hF, ?_⟩
  have hAJ : A + Jm = A + pad (E ∪ {x})ᶜ (restrict Jm (E ∪ {x})ᶜ) := by
    conv_lhs => rw [← hJ]
    rfl
  rw [hAJ, schur_add_supported_proof, pad_add, schur_union A E {x} hdisj hE hF]
  congr 1

theorem scalar_step (M : Matrix P P 𝕜) (A : Finset P) (x : P) (hx : x ∈ A) (hM : M x x ≠ 0) :
    mask (A.erase x) (pad (survivors x) (scalarSchur M x)) = pad {x}ᶜ (schur (mask A M) {x}) := by
  have hMx : mask A M x x ≠ 0 := by rwa [mask_apply_mem _ _ _ _ hx hx]
  have hxc : x ∉ ({x} : Finset P)ᶜ := by simp
  ext i j
  by_cases hi : i ∈ A.erase x
  · have hix := Finset.ne_of_mem_erase hi
    have hiA := Finset.mem_of_mem_erase hi
    by_cases hj : j ∈ A.erase x
    · have hjx := Finset.ne_of_mem_erase hj
      have hjA := Finset.mem_of_mem_erase hj
      rw [mask_apply_mem _ _ _ _ hi hj,
        pad_apply_mem (survivors x) _ i j
          (show i ∈ survivors x from Finset.mem_erase.mpr ⟨hix, Finset.mem_univ _⟩)
          (show j ∈ survivors x from Finset.mem_erase.mpr ⟨hjx, Finset.mem_univ _⟩),
        schur_singleton_apply _ x hMx i j hix hjx]
      simp only [scalarSchur, mask_apply_mem _ _ _ _ hiA hjA, mask_apply_mem _ _ _ _ hiA hx,
        mask_apply_mem _ _ _ _ hx hjA, mask_apply_mem _ _ _ _ hx hx]
    · rw [mask_apply_right _ _ _ _ hj]
      by_cases hjx : j = x
      · subst hjx; rw [pad_apply_right _ _ _ _ hxc]
      · have hjA : j ∉ A := fun h => hj (Finset.mem_erase.mpr ⟨hjx, h⟩)
        rw [schur_singleton_apply _ x hMx i j hix hjx, mask_apply_right _ _ _ _ hjA,
          mask_apply_right _ _ x j hjA]
        ring
  · rw [mask_apply_left _ _ _ _ hi]
    by_cases hix : i = x
    · subst hix; rw [pad_apply_left _ _ _ _ hxc]
    · have hiA : i ∉ A := fun h => hi (Finset.mem_erase.mpr ⟨hix, h⟩)
      by_cases hjx : j = x
      · subst hjx; rw [pad_apply_right _ _ _ _ hxc]
      · rw [schur_singleton_apply _ x hMx i j hix hjx, mask_apply_left _ _ _ _ hiA,
          mask_apply_left _ _ i x hiA]
        ring

end CumSchur

/-! ### Padded states -/

namespace CumSchur

variable {P : Type*} [Fintype P] [DecidableEq P]

theorem pad_smul (S : Finset P) (c : ℂ) (X : Matrix S S ℂ) : c • pad S X = pad S (c • X) := by
  ext i j
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · simp only [Matrix.smul_apply, pad_apply_mem _ _ _ _ hi hj]
    · simp only [Matrix.smul_apply, pad_apply_right _ _ _ _ hj, smul_zero]
  · simp only [Matrix.smul_apply, pad_apply_left _ _ _ _ hi, smul_zero]

theorem pad_map {α β : Type*} [Zero α] [Zero β] (S : Finset P) (φ : α → β) (h0 : φ 0 = 0)
    (X : Matrix S S α) :
    (fun i j => φ (pad S X i j) : Matrix P P β) = pad S (fun i j => φ (X i j)) := by
  ext i j
  unfold pad
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · simp only [dif_pos hi, dif_pos hj]
    · simp only [dif_pos hi, dif_neg hj, h0]
  · simp only [dif_neg hi, h0]

theorem pad_mul_pad (S : Finset P) (X Y : Matrix S S ℂ) : pad S X * pad S Y = pad S (X * Y) := by
  ext i j
  rw [mul_apply]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · rw [pad_apply_mem _ _ _ _ hi hj, mul_apply]
      have : ∀ k, pad S X i k * pad S Y k j =
          if hk : k ∈ S then X ⟨i, hi⟩ ⟨k, hk⟩ * Y ⟨k, hk⟩ ⟨j, hj⟩ else 0 := by
        intro k
        by_cases hk : k ∈ S
        · rw [dif_pos hk, pad_apply_mem _ _ _ _ hi hk, pad_apply_mem _ _ _ _ hk hj]
        · rw [dif_neg hk, pad_apply_right _ _ _ _ hk, zero_mul]
      simp only [this]
      exact sum_dite_mem S _
    · rw [pad_apply_right _ _ _ _ hj]
      exact Finset.sum_eq_zero fun k _ => by rw [pad_apply_right _ _ _ _ hj, mul_zero]
  · rw [pad_apply_left _ _ _ _ hi]
    exact Finset.sum_eq_zero fun k _ => by rw [pad_apply_left _ _ _ _ hi, zero_mul]

theorem pad_mul_diagonal (S : Finset P) (X : Matrix S S ℂ) (d : P → ℂ) :
    pad S X * diagonal d = pad S (X * diagonal (fun i : S => d i)) := by
  ext i j
  rw [mul_diagonal]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · rw [pad_apply_mem _ _ _ _ hi hj, pad_apply_mem _ _ _ _ hi hj, mul_diagonal]
    · rw [pad_apply_right _ _ _ _ hj, pad_apply_right _ _ _ _ hj, zero_mul]
  · rw [pad_apply_left _ _ _ _ hi, pad_apply_left _ _ _ _ hi, zero_mul]

theorem pad_conjTranspose (S : Finset P) (X : Matrix S S ℂ) : (pad S X)ᴴ = pad S Xᴴ := by
  ext i j
  rw [conjTranspose_apply]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · rw [pad_apply_mem _ _ _ _ hj hi, pad_apply_mem _ _ _ _ hi hj, conjTranspose_apply]
    · rw [pad_apply_left _ _ _ _ hj, pad_apply_right _ _ _ _ hj, star_zero]
  · rw [pad_apply_right _ _ _ _ hi, pad_apply_left _ _ _ _ hi, star_zero]

theorem pad_transpose (S : Finset P) (X : Matrix S S ℂ) : (pad S X)ᵀ = pad S Xᵀ := by
  ext i j
  rw [transpose_apply]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · rw [pad_apply_mem _ _ _ _ hj hi, pad_apply_mem _ _ _ _ hi hj, transpose_apply]
    · rw [pad_apply_left _ _ _ _ hj, pad_apply_right _ _ _ _ hj]
  · rw [pad_apply_right _ _ _ _ hi, pad_apply_left _ _ _ _ hi]

theorem matrixIm_pad (S : Finset P) (X : Matrix S S ℂ) : matrixIm (pad S X) = pad S (matrixIm X) :=
  pad_map S (fun z : ℂ => ((z.im : ℝ) : ℂ)) (by simp) X

variable (S : Finset P) (g' : Matrix S S ℂ) (r : P → ℂ) (t : ℝ)

theorem h_pad : State.h t ⟨pad S g', r⟩ = pad S (State.h t ⟨g', fun i => r i⟩) := by
  unfold State.h; exact pad_smul S _ g'

theorem K_pad : State.K t ⟨pad S g', r⟩ = pad S (State.K t ⟨g', fun i => r i⟩) := by
  unfold State.K
  rw [h_pad]
  exact pad_map S (fun z : ℂ => z ^ 2) (by simp) _

theorem F_pad : State.F t ⟨pad S g', r⟩ = pad S (State.F t ⟨g', fun i => r i⟩) := by
  unfold State.F
  rw [h_pad]
  exact pad_map S (fun z : ℂ => ‖z‖ ^ 2) (by simp) _

omit [Fintype P] in
theorem D_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (s : State ι) (i j : ι) :
    s.D t i j = (if i = j then s.p i * s.q i else 0) - s.p i * s.F t i j * s.p j := by
  unfold State.D
  rw [Matrix.sub_apply, diagonal_apply, mul_diagonal, diagonal_mul]

theorem D_pad : State.D t ⟨pad S g', r⟩ = pad S (State.D t ⟨g', fun i => r i⟩) := by
  ext i j
  rw [D_apply, F_pad]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · rw [pad_apply_mem _ _ _ _ hi hj, pad_apply_mem _ _ _ _ hi hj, D_apply]
      simp only [State.p, State.q, pad_apply_mem _ _ _ _ hi hi, Subtype.mk.injEq]
    · rw [pad_apply_right _ _ _ _ hj, pad_apply_right _ _ _ _ hj]
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      simp [hij]
  · rw [pad_apply_left _ _ _ _ hi, pad_apply_left _ _ _ _ hi]
    simp only [State.q, pad_apply_left _ _ _ _ hi, Complex.zero_im, mul_zero, zero_mul,
      sub_zero, ite_self]

theorem sym_pad (h : g'.IsSymm) : (pad S g').IsSymm := by
  unfold IsSymm at *
  rw [pad_transpose, h]

theorem ward_pad (h : State.ward t ⟨g', fun i => r i⟩) : State.ward t ⟨pad S g', r⟩ := by
  unfold State.ward at *
  rw [h_pad, pad_mul_diagonal, pad_conjTranspose, pad_mul_pad]
  change pad S _ = matrixIm (pad S g')
  rw [matrixIm_pad, ← h]
  rfl

end CumSchur

open CumSchur in
/-- The ambient state of a live state is the padded subtype state. -/
theorem ambient_eq {P : Type*} [Fintype P] [DecidableEq P] (a : LiveState P) (r : P → ℂ) :
    a.ambient r = ⟨pad a.live (a.state r).g, r⟩ := rfl

namespace CumSchur

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The padded Schur invariant after `k` steps. -/
def SchurInv (q : Sequence P) (t : ℝ) (r : P → ℂ) (k : ℕ) : Prop :=
  IsUnit (restrict (1 - ((q.state 0).ambient r).K t - q.Jrecord t r (Finset.range k))
      (q.state k).liveᶜ) ∧
  mask (q.state k).live (1 - ((q.state k).ambient r).K t) =
    pad (q.state k).liveᶜᶜ (schur (1 - ((q.state 0).ambient r).K t -
      q.Jrecord t r (Finset.range k)) (q.state k).liveᶜ) ∧
  IsUnit (restrict (((q.state 0).ambient r).D t + q.Lrecord t r (Finset.range k))
      (q.state k).liveᶜ) ∧
  mask (q.state k).live (((q.state k).ambient r).D t) =
    pad (q.state k).liveᶜᶜ (schur (((q.state 0).ambient r).D t +
      q.Lrecord t r (Finset.range k)) (q.state k).liveᶜ)

theorem amb_K (a : LiveState P) (r : P → ℂ) (t : ℝ) :
    (a.ambient r).K t = pad a.live ((a.state r).K t) :=
  K_pad a.live (a.state r).g r t

theorem amb_F (a : LiveState P) (r : P → ℂ) (t : ℝ) :
    (a.ambient r).F t = pad a.live ((a.state r).F t) :=
  F_pad a.live (a.state r).g r t

theorem amb_D (a : LiveState P) (r : P → ℂ) (t : ℝ) :
    (a.ambient r).D t = pad a.live ((a.state r).D t) :=
  D_pad a.live (a.state r).g r t

theorem SchurInv_zero (q : Sequence P) (t : ℝ) (r : P → ℂ) (hstart : (q.state 0).live = Finset.univ) :
    SchurInv q t r 0 := by
  have hJ : q.Jrecord t r (Finset.range 0) = 0 := by simp [Sequence.Jrecord]
  have hL : q.Lrecord t r (Finset.range 0) = 0 := by simp [Sequence.Lrecord]
  unfold SchurInv
  rw [hJ, hL, sub_zero, add_zero, hstart, Finset.compl_univ, mask_univ, mask_univ,
    pad_schur_empty, pad_schur_empty]
  exact ⟨isUnit_restrict_empty _, rfl, isUnit_restrict_empty _, rfl⟩

end CumSchur

open CumSchur in
theorem cumulative_schur_proof {P : Type*} [Fintype P] [DecidableEq P]
    (q : Sequence P) (t : ℝ) (r : P → ℂ) (ht : 0 < t)
    (hp : ∀ i, 0 < (r i).im)
    (hseq : q.wellFormed t r) (hstart : (q.state 0).live = Finset.univ)
    (hstep : ∀ k < q.length, ((q.state k).state r).g.IsSymm ∧ ((q.state k).state r).ward t ∧
      ∀ x : (q.state k).live, 1 - ((q.state k).state r).K t x x ≠ 0 ∧
        0 < ((q.state k).state r).q x -
          ((q.state k).state r).p x * ((q.state k).state r).F t x x) :
    let E := (q.state q.length).liveᶜ
    let s0 := (q.state 0).ambient r
    pad (q.state q.length).live (1 - ((q.state q.length).state r).K t) =
      pad Eᶜ (schur (1 - s0.K t - q.Jrecord t r (Finset.range q.length)) E) ∧
    pad (q.state q.length).live (((q.state q.length).state r).D t) =
      pad Eᶜ (schur (s0.D t + q.Lrecord t r (Finset.range q.length)) E) := by
  intro E s0
  have hInv : ∀ k, k ≤ q.length → SchurInv q t r k := by
    intro k
    induction k with
    | zero => intro _; exact SchurInv_zero q t r hstart
    | succ k ih =>
      intro hk1
      have hk : k < q.length := hk1
      obtain ⟨hAu, hAK, hBu, hBD⟩ := ih hk.le
      have hJs : q.Jrecord t r (Finset.range (k + 1)) =
          q.Jrecord t r (Finset.range k) + q.stepJ t r k := Finset.sum_range_succ _ _
      have hLs : q.Lrecord t r (Finset.range (k + 1)) =
          q.Lrecord t r (Finset.range k) + q.stepL t r k := Finset.sum_range_succ _ _
      have hwf := hseq.2 k hk
      cases hpk : q.pivot k with
      | none =>
        rw [hpk] at hwf
        have hJ0 : q.stepJ t r k = 0 := by simp [Sequence.stepJ, hpk]
        have hL0 : q.stepL t r k = 0 := by simp [Sequence.stepL, hpk]
        unfold SchurInv
        rw [hJs, hLs, hJ0, hL0, add_zero, add_zero, hwf]
        exact ⟨hAu, hAK, hBu, hBD⟩
      | some x =>
        rw [hpk] at hwf
        set a := q.state k with ha_def
        set b := q.state (k + 1) with hb_def
        set ξ := q.scalar k
        have hR : StepRel t r a b x ξ := hwf
        set s := a.ambient r with hs_def
        have hwfa : a.g = mask a.live a.g := hseq.1 k hk.le
        have hwfb : b.g = mask b.live b.g := hseq.1 (k + 1) hk1
        have hs_g : s.g = a.g := hwfa.symm
        obtain ⟨hsymk, hwk, hpivk⟩ := hstep k hk
        have hxS := hR.pivot_live
        have hsym : s.g.IsSymm := sym_pad a.live _ hsymk
        have hw : s.ward t := ward_pad a.live _ r t hwk
        have hden : 1 + ((ξ : ℂ) + t * s.r x) * s.g x x ≠ 0 := by
          rw [hs_g]; exact hR.denominator
        have hKx : s.K t x x = (a.state r).K t ⟨x, hxS⟩ ⟨x, hxS⟩ := by
          rw [hs_def, amb_K, pad_apply_mem _ _ _ _ hxS hxS]
        have hFx : s.F t x x = (a.state r).F t ⟨x, hxS⟩ ⟨x, hxS⟩ := by
          rw [hs_def, amb_F, pad_apply_mem _ _ _ _ hxS hxS]
        have hqx : s.q x = (a.state r).q ⟨x, hxS⟩ := by
          show (pad a.live (a.state r).g x x).im = ((a.state r).g ⟨x, hxS⟩ ⟨x, hxS⟩).im
          rw [pad_apply_mem _ _ _ _ hxS hxS]
        have hpx : s.p x = (a.state r).p ⟨x, hxS⟩ := rfl
        have hax : 1 - s.K t x x ≠ 0 := by rw [hKx]; exact (hpivk ⟨x, hxS⟩).1
        have hpv : 0 < s.q x - s.p x * s.F t x x := by
          rw [hqx, hpx, hFx]; exact (hpivk ⟨x, hxS⟩).2
        obtain ⟨-, hK1, hD1⟩ := single_deletion_proof t s x ξ ht hsym hw hden hax hpv
        set s' := deleteState t s x ξ with hs'_def
        -- the new ambient matrix is the padded deleted state
        have hbsub : b.live ⊆ survivors x := by
          rw [hR.survivors]; intro i hi
          exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hi, Finset.mem_univ _⟩
        have hgb : mask b.live b.g = pad (survivors x) s'.g := by
          rw [← hwfb, hR.update]
          ext i j
          by_cases hi : i ∈ b.live
          · by_cases hj : j ∈ b.live
            · refine (mask_apply_mem b.live _ i j hi hj).trans ?_
              rw [pad_apply_mem _ _ _ _ (hbsub hi) (hbsub hj)]
              show _ = s.g i j - ((ξ : ℂ) + t * s.r x) * s.g i x * s.g x j /
                  (1 + ((ξ : ℂ) + t * s.r x) * s.g x x)
              rw [hs_g]
              rfl
            · refine (mask_apply_right b.live _ i j hj).trans ?_
              by_cases hjx : j = x
              · subst hjx; rw [pad_apply_right _ _ _ _ (by simp [survivors])]
              · have hjS : j ∈ survivors x := Finset.mem_erase.mpr ⟨hjx, Finset.mem_univ _⟩
                have hja : j ∉ a.live := fun h => hj (by
                  rw [hR.survivors]; exact Finset.mem_erase.mpr ⟨hjx, h⟩)
                rw [pad_apply_mem _ _ _ _ (hbsub hi) hjS]
                show 0 = s.g i j - ((ξ : ℂ) + t * s.r x) * s.g i x * s.g x j /
                  (1 + ((ξ : ℂ) + t * s.r x) * s.g x x)
                have hgj : ∀ i', s.g i' j = 0 := fun i' => pad_apply_right _ _ i' j hja
                rw [hgj, hgj]
                ring
          · refine (mask_apply_left b.live _ i j hi).trans ?_
            by_cases hix : i = x
            · subst hix; rw [pad_apply_left _ _ _ _ (by simp [survivors])]
            · have hiS : i ∈ survivors x := Finset.mem_erase.mpr ⟨hix, Finset.mem_univ _⟩
              have hia : i ∉ a.live := fun h => hi (by
                rw [hR.survivors]; exact Finset.mem_erase.mpr ⟨hix, h⟩)
              by_cases hjx : j = x
              · subst hjx; rw [pad_apply_right _ _ _ _ (by simp [survivors])]
              · have hjS : j ∈ survivors x := Finset.mem_erase.mpr ⟨hjx, Finset.mem_univ _⟩
                rw [pad_apply_mem _ _ _ _ hiS hjS]
                show 0 = s.g i j - ((ξ : ℂ) + t * s.r x) * s.g i x * s.g x j /
                  (1 + ((ξ : ℂ) + t * s.r x) * s.g x x)
                have hgi : ∀ j', s.g i j' = 0 := fun j' => pad_apply_left _ _ i j' hia
                rw [hgi, hgi]
                ring
        have hbamb : b.ambient r = ⟨pad (survivors x) s'.g, r⟩ := by
          show (⟨mask b.live b.g, r⟩ : State P) = _
          rw [hgb]
        have hG : b.liveᶜ = a.liveᶜ ∪ {x} := by
          rw [hR.survivors, Finset.compl_erase, Finset.insert_eq, Finset.union_comm]
        have hxE : x ∉ a.liveᶜ := fun h => (Finset.mem_compl.mp h) hxS
        -- K part
        have hscK := scalar_step (1 - s.K t) a.live x hxS (by simpa using hax)
        rw [← hR.survivors] at hscK
        have hstepJ : q.stepJ t r k = mask b.live (Jinc t s x ξ) := by
          unfold Sequence.stepJ; rw [hpk]
        have hpivA : pad a.liveᶜᶜ (schur (1 - s0.K t - q.Jrecord t r (Finset.range k))
            a.liveᶜ) x x ≠ 0 := by
          rw [← hAK, mask_apply_mem _ _ _ _ hxS hxS]; simpa using hax
        obtain ⟨hAu', hAK'⟩ := schur_step (1 - s0.K t - q.Jrecord t r (Finset.range k))
          (-(mask b.live (Jinc t s x ξ))) a.liveᶜ b.liveᶜ x hxE hG hAu hpivA
          (by rw [compl_compl, mask_neg, mask_idem])
        have hA' : 1 - s0.K t - q.Jrecord t r (Finset.range (k + 1)) =
            1 - s0.K t - q.Jrecord t r (Finset.range k) + -(mask b.live (Jinc t s x ξ)) := by
          rw [hJs, hstepJ]; abel
        -- D part
        have hDx : s.D t x x ≠ 0 := by
          rw [D_apply, if_pos rfl]
          have hp0 := hp x
          have : s.p x * s.q x - s.p x * s.F t x x * s.p x =
              s.p x * (s.q x - s.p x * s.F t x x) := by ring
          rw [this]
          exact (mul_pos hp0 hpv).ne'
        have hscD := scalar_step (s.D t) a.live x hxS hDx
        rw [← hR.survivors] at hscD
        have hstepL : q.stepL t r k = mask b.live (Linc t s x ξ) := by
          unfold Sequence.stepL; rw [hpk]
        have hpivB : pad a.liveᶜᶜ (schur (s0.D t + q.Lrecord t r (Finset.range k))
            a.liveᶜ) x x ≠ 0 := by
          rw [← hBD, mask_apply_mem _ _ _ _ hxS hxS]; exact hDx
        obtain ⟨hBu', hBD'⟩ := schur_step (s0.D t + q.Lrecord t r (Finset.range k))
          (mask b.live (Linc t s x ξ)) a.liveᶜ b.liveᶜ x hxE hG hBu hpivB
          (by rw [compl_compl, mask_idem])
        have hB' : s0.D t + q.Lrecord t r (Finset.range (k + 1)) =
            s0.D t + q.Lrecord t r (Finset.range k) + mask b.live (Linc t s x ξ) := by
          rw [hLs, hstepL, add_assoc]
        unfold SchurInv
        rw [hA', hB']
        refine ⟨hAu', ?_, hBu', ?_⟩
        · have hLK : mask b.live (1 - (b.ambient r).K t) =
              mask b.live (pad (survivors x) (1 - s'.K t)) := by
            rw [hbamb, K_pad]
            conv_lhs => rw [← mask_mask b.live (survivors x) hbsub]
            rw [mask_one_sub_pad]
            rfl
          rw [hAK', ← hAK, ← hscK, hLK, hK1, pad_sub, mask_sub,
            mask_pad_restrict b.live (survivors x) hbsub, sub_eq_add_neg]
        · have hLD : mask b.live ((b.ambient r).D t) =
              mask b.live (pad (survivors x) (s'.D t)) := by
            rw [hbamb, D_pad]
            rfl
          rw [hBD', ← hBD, ← hscD, hLD, hD1, pad_add, mask_add,
            mask_pad_restrict b.live (survivors x) hbsub]
  obtain ⟨-, hK, -, hD⟩ := hInv q.length le_rfl
  refine ⟨?_, ?_⟩
  · rw [← hK, amb_K, mask_one_sub_pad]
  · rw [← hD, amb_D, mask_pad]


end AndersonAC.AgentS45
