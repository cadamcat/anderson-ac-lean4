import AndersonAC.S78.PhysicalCertificate

/-!
# Sequential Schur quotient ((A))

The Schur complement of `B` onto a set `A` (02-state.tex:236–247: the subscript names the
eliminated indices `Aᶜ`) is characterised by solving the eliminated rows:
`SchurRel B A S` says that for every `v` there is `x` with `x = v` on `A`, `(B x)ᵢ = 0` off `A`
and `(B x)ᵢ = ∑_{k ∈ A} S i k v k` on `A`; `OffInj B A` says that the eliminated block is
injective. With these:

* `schurRel_unique` — `S` is determined on `A × A`;
* `offInj_iff_isUnit` — `OffInj B A` is the invertibility of the block `B_{Aᶜ Aᶜ}`;
* `schurRel_activeSchur` — `SolS78.activeSchur B A` (padded by zero) satisfies `SchurRel`;
* `schurRel_step`, `offInj_step` — the quotient formula `B/(Aᶜ ∪ {p}) = (B/Aᶜ)/p` for a nonzero
  scalar pivot, with the diagonal shift `ξ` at `p` (the revealed residual);
* `schurRel_conj` — for a real `B`, the Schur complement is real.
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open Matrix

section Generic

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

/-- `S` is, on `A × A`, the Schur complement of `B` onto `A` (eliminated set `Aᶜ`). -/
def SchurRel (B : Matrix ι ι K) (A : Finset ι) (S : Matrix ι ι K) : Prop :=
  ∀ v : ι → K, ∃ x : ι → K, (∀ i ∈ A, x i = v i) ∧ (∀ i, i ∉ A → (B *ᵥ x) i = 0) ∧
    ∀ i ∈ A, (B *ᵥ x) i = ∑ k ∈ A, S i k * v k

/-- The eliminated block `B_{Aᶜ Aᶜ}` is injective. -/
def OffInj (B : Matrix ι ι K) (A : Finset ι) : Prop :=
  ∀ z : ι → K, (∀ i ∈ A, z i = 0) → (∀ i, i ∉ A → (B *ᵥ z) i = 0) → z = 0

/-- The scalar Schur step at `p` with shift `ξ` (the `K`-valued form of `schurStepM`). -/
def schurStepK (S : Matrix ι ι K) (p : ι) (ξ : K) : Matrix ι ι K :=
  fun i k => if i = p ∨ k = p then (if i = k then 1 else 0)
    else S i k - S i p * S p k / (S p p + ξ)

omit [Fintype ι] in
theorem sum_single_mul {A : Finset ι} (f : ι → K) {k : ι} (hk : k ∈ A) :
    ∑ k' ∈ A, f k' * (Pi.single k (1 : K) : ι → K) k' = f k := by
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd hk h

/-- **Uniqueness of the Schur complement on `A × A`.** -/
theorem schurRel_unique {B : Matrix ι ι K} {A : Finset ι} {S₁ S₂ : Matrix ι ι K}
    (h₁ : SchurRel B A S₁) (h₂ : SchurRel B A S₂) (hI : OffInj B A) {i k : ι}
    (hi : i ∈ A) (hk : k ∈ A) : S₁ i k = S₂ i k := by
  obtain ⟨x₁, hx₁, hT₁, hA₁⟩ := h₁ (Pi.single k 1)
  obtain ⟨x₂, hx₂, hT₂, hA₂⟩ := h₂ (Pi.single k (1 : K))
  have hz : x₁ - x₂ = 0 := hI _ (fun i hi => by simp [hx₁ i hi, hx₂ i hi])
    (fun i hi => by rw [Matrix.mulVec_sub, Pi.sub_apply, hT₁ i hi, hT₂ i hi, sub_zero])
  have hx : x₁ = x₂ := sub_eq_zero.mp hz
  have e₁ := hA₁ i hi
  rw [hx, hA₂ i hi, sum_single_mul _ hk, sum_single_mul _ hk] at e₁
  exact e₁.symm

/-- **The quotient formula, Schur part**: eliminating one more active site `p` with a nonzero
pivot `S p p + ξ` (after the shift `ξ` of the diagonal entry at `p`). -/
theorem schurRel_step {B : Matrix ι ι K} {A : Finset ι} {S : Matrix ι ι K}
    (h : SchurRel B A S) {p : ι} (hp : p ∈ A) (ξ : K) (hpiv : S p p + ξ ≠ 0) :
    SchurRel (B + diagonal (Pi.single p ξ : ι → K)) (A.erase p) (schurStepK S p ξ) := by
  intro v
  set c : K := -(∑ k ∈ A.erase p, S p k * v k) / (S p p + ξ) with hc
  obtain ⟨x, hx, hT, hA⟩ := h (Function.update v p c)
  have hxp : x p = c := by rw [hx p hp]; simp
  have hsplit : ∀ i, ∑ k ∈ A, S i k * Function.update v p c k =
      S i p * c + ∑ k ∈ A.erase p, S i k * v k := by
    intro i
    rw [← Finset.add_sum_erase A _ hp]
    congr 1
    · simp
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  have hB' : ∀ i, ((B + diagonal (Pi.single p ξ : ι → K)) *ᵥ x) i = (B *ᵥ x) i + (Pi.single p ξ : ι → K) i * x i := by
    intro i
    rw [Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal]
  refine ⟨x, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hx i (Finset.mem_of_mem_erase hi), Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  · rw [hB']
    by_cases hip : i = p
    · subst hip
      rw [hA i hp, hsplit, hxp, Pi.single_eq_same, hc]
      field_simp
      ring
    · have hiA : i ∉ A := fun h' => hi (Finset.mem_erase.mpr ⟨hip, h'⟩)
      rw [hT i hiA, Pi.single_eq_of_ne hip]
      ring
  · have hip : i ≠ p := Finset.ne_of_mem_erase hi
    rw [hB', hA i (Finset.mem_of_mem_erase hi), hsplit, Pi.single_eq_of_ne hip, zero_mul, add_zero]
    have hrhs : ∑ k ∈ A.erase p, schurStepK S p ξ i k * v k =
        ∑ k ∈ A.erase p, S i k * v k - S i p / (S p p + ξ) * ∑ k ∈ A.erase p, S p k * v k := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      have hkp : k ≠ p := Finset.ne_of_mem_erase hk
      simp only [schurStepK, hip, hkp, or_self, ite_false]
      ring
    rw [hrhs, hc]
    ring

/-- **The quotient formula, invertibility part**: the enlarged eliminated block stays
injective when the pivot is nonzero. -/
theorem offInj_step {B : Matrix ι ι K} {A : Finset ι} {S : Matrix ι ι K}
    (h : SchurRel B A S) (hI : OffInj B A) {p : ι} (hp : p ∈ A) (ξ : K)
    (hpiv : S p p + ξ ≠ 0) : OffInj (B + diagonal (Pi.single p ξ : ι → K)) (A.erase p) := by
  intro z hz hBz
  have hB' : ∀ i, ((B + diagonal (Pi.single p ξ : ι → K)) *ᵥ z) i = (B *ᵥ z) i + (Pi.single p ξ : ι → K) i * z i := by
    intro i
    rw [Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal]
  have hoff : ∀ i, i ∉ A → (B *ᵥ z) i = 0 := by
    intro i hi
    have hip : i ≠ p := fun h' => hi (h' ▸ hp)
    have := hBz i (fun h' => hi (Finset.mem_of_mem_erase h'))
    rwa [hB', Pi.single_eq_of_ne hip, zero_mul, add_zero] at this
  obtain ⟨x, hx, hT, hA⟩ := h z
  have hxz : x = z := by
    have := hI (x - z) (fun i hi => by simp [hx i hi])
      (fun i hi => by rw [Matrix.mulVec_sub, Pi.sub_apply, hT i hi, hoff i hi, sub_zero])
    exact sub_eq_zero.mp this
  have hzp : z p = 0 := by
    have h1 := hBz p (Finset.notMem_erase p A)
    rw [hB', ← hxz, hA p hp, ← Finset.add_sum_erase A _ hp, Pi.single_eq_same] at h1
    have h2 : ∑ k ∈ A.erase p, S p k * z k = 0 :=
      Finset.sum_eq_zero (fun k hk => by rw [hz k hk, mul_zero])
    rw [h2, add_zero, hxz] at h1
    have h3 : (S p p + ξ) * z p = 0 := by rw [add_mul]; exact h1
    exact (mul_eq_zero.mp h3).resolve_left hpiv
  apply hI z _ hoff
  intro i hi
  by_cases hip : i = p
  · rw [hip, hzp]
  · exact hz i (Finset.mem_erase.mpr ⟨hip, hi⟩)

/-- A zero pivot is excluded by the injectivity of the enlarged eliminated block. -/
theorem pivot_ne_zero_of_offInj {B : Matrix ι ι K} {A : Finset ι} {S : Matrix ι ι K}
    (h : SchurRel B A S) {p : ι} (hp : p ∈ A) (ξ : K)
    (hI : OffInj (B + diagonal (Pi.single p ξ : ι → K)) (A.erase p)) : S p p + ξ ≠ 0 := by
  intro h0
  obtain ⟨x, hx, hT, hA⟩ := h (Pi.single p (1 : K))
  have hxp : x p = 1 := by rw [hx p hp]; simp
  have : x = 0 := by
    apply hI x
    · intro i hi
      rw [hx i (Finset.mem_of_mem_erase hi), Pi.single_eq_of_ne (Finset.ne_of_mem_erase hi)]
    · intro i hi
      rw [Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal]
      by_cases hip : i = p
      · subst hip
        rw [hA i hp, sum_single_mul _ hp, Pi.single_eq_same, hxp, mul_one, h0]
      · have hiA : i ∉ A := fun h' => hi (Finset.mem_erase.mpr ⟨hip, h'⟩)
        rw [hT i hiA, Pi.single_eq_of_ne hip, zero_mul, add_zero]
  rw [this] at hxp
  exact zero_ne_one hxp

end Generic

section Complex

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The eliminated block `B_{Aᶜ Aᶜ}` in the indexing of `SolS78.activeSchur`. -/
def offBlock (B : Matrix ι ι ℂ) (A : Finset ι) :
    Matrix {i // i ∉ A} {i // i ∉ A} ℂ :=
  B.submatrix (fun i : {i // i ∉ A} => i.val) (fun i : {i // i ∉ A} => i.val)

/-- Split a sum over `ι` into `A` and its complement. -/
theorem sum_split_mem (A : Finset ι) (f : ι → ℂ) :
    ∑ k, f k = ∑ a : {i // i ∈ A}, f a.val + ∑ t : {i // i ∉ A}, f t.val := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ A) f]
  congr 1
  exact Finset.sum_congr (by ext; simp) (fun _ _ => rfl)

theorem mulVec_off_of_zero_on (B : Matrix ι ι ℂ) (A : Finset ι) (z : ι → ℂ)
    (hz : ∀ i ∈ A, z i = 0) (t : {i // i ∉ A}) :
    (offBlock B A *ᵥ fun t' : {i // i ∉ A} => z t'.val) t = (B *ᵥ z) t.val := by
  simp only [Matrix.mulVec, dotProduct, offBlock, Matrix.submatrix_apply]
  rw [sum_split_mem A (fun k => B t.val k * z k)]
  have : ∑ a : {i // i ∈ A}, B t.val a.val * z a.val = 0 :=
    Finset.sum_eq_zero (fun a _ => by rw [hz a.val a.2, mul_zero])
  rw [this, zero_add]

/-- **`OffInj` is the invertibility of the eliminated block.** -/
theorem offInj_iff_isUnit (B : Matrix ι ι ℂ) (A : Finset ι) :
    OffInj B A ↔ IsUnit (offBlock B A).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  constructor
  · intro hI w₁ w₂ hw
    let z : ι → ℂ := fun i => if h : i ∈ A then 0 else (w₁ - w₂) ⟨i, h⟩
    have hz0 : ∀ i ∈ A, z i = 0 := fun i hi => by simp [z, hi]
    have hzT : (fun t : {i // i ∉ A} => z t.val) = w₁ - w₂ := by
      funext t; simp [z, t.2]
    have hzz : z = 0 := by
      apply hI z hz0
      intro i hi
      have := mulVec_off_of_zero_on B A z hz0 ⟨i, hi⟩
      rw [← this, hzT, Matrix.mulVec_sub, hw, sub_self, Pi.zero_apply]
    funext t
    have := congrFun hzz t.val
    have h2 := congrFun hzT t
    simp only [Pi.zero_apply] at this
    rw [this, Pi.sub_apply] at h2
    exact (sub_eq_zero.mp h2.symm)
  · intro hinj z hz hBz
    have hzT : (fun t : {i // i ∉ A} => z t.val) = 0 := by
      apply hinj
      rw [Matrix.mulVec_zero]
      funext t
      rw [mulVec_off_of_zero_on B A z hz t, Pi.zero_apply, hBz t.val t.2]
    funext i
    by_cases hi : i ∈ A
    · exact hz i hi
    · exact congrFun hzT ⟨i, hi⟩

/-- `SolS78.activeSchur` padded by zero to a full matrix. -/
def padSchur (S : Matrix ι ι ℂ) (A : Finset ι) : Matrix ι ι ℂ := fun i k =>
  if h : i ∈ A ∧ k ∈ A then SolS78.activeSchur S A ⟨i, h.1⟩ ⟨k, h.2⟩ else 0

/-- **The block formula satisfies `SchurRel`** when the eliminated block is invertible. -/
theorem schurRel_activeSchur (B : Matrix ι ι ℂ) (A : Finset ι) (hI : OffInj B A) :
    SchurRel B A (padSchur B A) := by
  have hU : IsUnit (offBlock B A).det := (offInj_iff_isUnit B A).mp hI
  set D := offBlock B A with hDdef
  let BTA : Matrix {i // i ∉ A} {i // i ∈ A} ℂ :=
    B.submatrix (fun i : {i // i ∉ A} => i.val) (fun i : {i // i ∈ A} => i.val)
  let BAT : Matrix {i // i ∈ A} {i // i ∉ A} ℂ :=
    B.submatrix (fun i : {i // i ∈ A} => i.val) (fun i : {i // i ∉ A} => i.val)
  let BAA : Matrix {i // i ∈ A} {i // i ∈ A} ℂ :=
    B.submatrix (fun i : {i // i ∈ A} => i.val) (fun i : {i // i ∈ A} => i.val)
  intro v
  let vA : {i // i ∈ A} → ℂ := fun a => v a.val
  let w : {i // i ∉ A} → ℂ := -(D⁻¹ *ᵥ (BTA *ᵥ vA))
  let x : ι → ℂ := fun i => if h : i ∈ A then v i else w ⟨i, h⟩
  have hBx : ∀ i, (B *ᵥ x) i =
      ∑ a : {i // i ∈ A}, B i a.val * vA a + ∑ t : {i // i ∉ A}, B i t.val * w t := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    rw [sum_split_mem A (fun k => B i k * x k)]
    congr 1
    · apply Finset.sum_congr rfl; intro a _; simp [x, vA, a.2]
    · apply Finset.sum_congr rfl; intro t _; simp [x, t.2]
  refine ⟨x, fun i hi => by simp [x, hi], fun i hi => ?_, fun i hi => ?_⟩
  · have e : (B *ᵥ x) i = (BTA *ᵥ vA) ⟨i, hi⟩ + (D *ᵥ w) ⟨i, hi⟩ := by
      rw [hBx]; rfl
    rw [e]
    have hDD : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv D hU
    simp only [w, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Pi.neg_apply]
    rw [← Matrix.mul_assoc, hDD, Matrix.one_mul]; ring
  · have e : (B *ᵥ x) i = (BAA *ᵥ vA) ⟨i, hi⟩ + (BAT *ᵥ w) ⟨i, hi⟩ := by
      rw [hBx]; rfl
    rw [e]
    have hdefS : SolS78.activeSchur B A = BAA - BAT * D⁻¹ * BTA := rfl
    have hw : BAT *ᵥ w = -((BAT * D⁻¹ * BTA) *ᵥ vA) := by
      simp only [w, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have hS : (SolS78.activeSchur B A *ᵥ vA) ⟨i, hi⟩ =
        (BAA *ᵥ vA) ⟨i, hi⟩ + (BAT *ᵥ w) ⟨i, hi⟩ := by
      rw [hdefS, Matrix.sub_mulVec, hw, Pi.sub_apply, Pi.neg_apply, sub_eq_add_neg]
    rw [← hS]
    simp only [Matrix.mulVec, dotProduct]
    rw [← Finset.sum_coe_sort A]
    apply Finset.sum_congr rfl
    intro a _
    simp [padSchur, hi, a.2, vA]

omit [DecidableEq ι] in
/-- **A real matrix has a real Schur complement**: conjugating a `SchurRel` solution. -/
theorem schurRel_conj {B : Matrix ι ι ℂ} {A : Finset ι} {S : Matrix ι ι ℂ}
    (hB : ∀ i k, (starRingEnd ℂ) (B i k) = B i k) (h : SchurRel B A S) :
    SchurRel B A (fun i k => (starRingEnd ℂ) (S i k)) := by
  intro v
  obtain ⟨x, hx, hT, hA⟩ := h (fun i => (starRingEnd ℂ) (v i))
  have hc : ∀ i, (B *ᵥ fun k => (starRingEnd ℂ) (x k)) i = (starRingEnd ℂ) ((B *ᵥ x) i) := by
    intro i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hB]
  refine ⟨fun k => (starRingEnd ℂ) (x k), fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · simp [hx i hi]
  · rw [hc, hT i hi, map_zero]
  · rw [hc, hA i hi, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp

end Complex

end AndersonAC.AgentS78
