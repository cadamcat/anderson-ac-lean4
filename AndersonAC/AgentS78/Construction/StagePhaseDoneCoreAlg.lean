import AndersonAC.AgentS78.Construction.StagePhaseDoneSnap

/-!
# The DONE exit of a clearing attempt: algebra of sequential core eliminations. For the torus-indexed damped inverse `fullInv A M t r` (StagePhaseClr.lean):

* `fullInv_eqns` / `fullInv_of_eqns` / `fullInv_kernel`: it is the unique solution of the damped
  equations on `A`;
* `elim_step`: one Schur step `schurStepM M p ξ` at `p ∈ A` (any real `ξ`, including the zero
  pivot, where `schurStepM` deletes `p`) changes the inverse on `A \ {p}` by a rank-one term
  `c · g_{·p} g_{p·}`;
* `coreElim_repr`: after sequential core eliminations (`CoreElim`) the inverse on the survivors
  is `G + G X G` with `G` the snapshot inverse and `X` supported on core × core.

This is the algebraic part of Lemma 6.1 (06-clearing.tex:120–160) in sequential form; it needs no
invertibility of the true core block (07-assembly.tex:248–251), because a zero pivot is a
deletion, which is again a rank-one change supported at the eliminated core site.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78.DoneA

open AndersonAC.S78 AndersonAC.AgentS78
open scoped BigOperators Matrix

variable {d m : ℕ}

/-- The entry `(i, l)` of the damped matrix `M − t diag r` on the torus. -/
def dEnt (t : ℝ) (r : Torus d m → ℂ) (M : Matrix (Torus d m) (Torus d m) ℝ)
    (i l : Torus d m) : ℂ :=
  (M i l : ℂ) - (t : ℂ) * (if i = l then r i else 0)

section Inverse

variable (A : Finset (Torus d m)) (M : Matrix (Torus d m) (Torus d m) ℝ) (t : ℝ)
  (r : Torus d m → ℂ)

theorem restrict_symm (hM : ∀ i k, M i k = M k i) : (restrictM A M).IsSymm := by
  ext a b; simp [restrictM, hM b.val a.val]

theorem damped_unit (hM : ∀ i k, M i k = M k i) (ht : 0 < t) (hr : ∀ i, 0 < (r i).im) :
    IsUnit (AndersonAC.S6.dampedMatrix (restrictM A M) t (fun a : A => r a)) :=
  AndersonAC.S2.damped_invertible (restrictM A M) (restrict_symm A M hM) ht _ (fun a => hr a)

theorem dampedMatrix_entry (a b : A) :
    AndersonAC.S6.dampedMatrix (restrictM A M) t (fun a : A => r a) a b = dEnt t r M a b := by
  simp only [AndersonAC.S6.dampedMatrix, restrictM, dEnt, Matrix.sub_apply, Matrix.map_apply,
    Matrix.submatrix_apply, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  congr 2
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg h, if_neg (fun h' => h (Subtype.ext h'))]

theorem fullInv_entry (a b : A) :
    fullInv A M t r a b =
      (AndersonAC.S6.dampedMatrix (restrictM A M) t (fun a : A => r a))⁻¹ a b := by
  unfold fullInv
  rw [dif_pos ⟨a.2, b.2⟩]
  rfl

/-- The damped inverse solves the damped equations on `A`. -/
theorem fullInv_eqns (hM : ∀ i k, M i k = M k i) (ht : 0 < t) (hr : ∀ i, 0 < (r i).im) :
    ∀ i ∈ A, ∀ k ∈ A,
      ∑ l ∈ A, dEnt t r M i l * fullInv A M t r l k = if i = k then 1 else 0 := by
  intro i hi k hk
  set 𝓜 := AndersonAC.S6.dampedMatrix (restrictM A M) t (fun a : A => r a)
  have hU := damped_unit A M t r hM ht hr
  have h1 : 𝓜 * 𝓜⁻¹ = 1 := Matrix.mul_nonsing_inv 𝓜 ((Matrix.isUnit_iff_isUnit_det _).mp hU)
  have h2 := congrFun (congrFun h1 ⟨i, hi⟩) ⟨k, hk⟩
  rw [Matrix.mul_apply, Matrix.one_apply] at h2
  have h3 : ∑ l ∈ A, dEnt t r M i l * fullInv A M t r l k =
      ∑ a : A, 𝓜 ⟨i, hi⟩ a * 𝓜⁻¹ a ⟨k, hk⟩ := by
    rw [← Finset.sum_coe_sort A]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact congrArg₂ (· * ·) (dampedMatrix_entry A M t r ⟨i, hi⟩ a).symm
      (fullInv_entry A M t r a ⟨k, hk⟩)
  rw [h3, h2]
  by_cases hik : i = k
  · subst hik; simp
  · rw [if_neg (fun h => hik (congrArg Subtype.val h)), if_neg hik]

/-- A solution of the damped equations on `A` is the damped inverse there. -/
theorem fullInv_of_eqns (hM : ∀ i k, M i k = M k i) (ht : 0 < t) (hr : ∀ i, 0 < (r i).im)
    (h : Matrix (Torus d m) (Torus d m) ℂ)
    (hh : ∀ i ∈ A, ∀ k ∈ A, ∑ l ∈ A, dEnt t r M i l * h l k = if i = k then 1 else 0) :
    ∀ i ∈ A, ∀ k ∈ A, fullInv A M t r i k = h i k := by
  intro i hi k hk
  set 𝓜 := AndersonAC.S6.dampedMatrix (restrictM A M) t (fun a : A => r a)
  let H : Matrix A A ℂ := fun a b => h a b
  have hMH : 𝓜 * H = 1 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.one_apply]
    have := hh a a.2 b b.2
    rw [← Finset.sum_coe_sort A] at this
    have h4 : ∑ c : A, 𝓜 a c * H c b = ∑ c : A, dEnt t r M a c * h c b :=
      Finset.sum_congr rfl fun c _ => congrArg (· * H c b) (dampedMatrix_entry A M t r a c)
    rw [h4, this]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg (fun h' => hab (Subtype.ext h')), if_neg hab]
  have hinv : 𝓜⁻¹ = H := Matrix.inv_eq_right_inv hMH
  rw [fullInv_entry A M t r ⟨i, hi⟩ ⟨k, hk⟩, hinv]

/-- The damped equations on `A` have only the zero solution with zero right side. -/
theorem fullInv_kernel (hM : ∀ i k, M i k = M k i) (ht : 0 < t) (hr : ∀ i, 0 < (r i).im)
    (v : Torus d m → ℂ) (hv : ∀ i ∈ A, ∑ l ∈ A, dEnt t r M i l * v l = 0) :
    ∀ i ∈ A, v i = 0 := by
  intro i hi
  set 𝓜 := AndersonAC.S6.dampedMatrix (restrictM A M) t (fun a : A => r a)
  have hU := damped_unit A M t r hM ht hr
  let V : A → ℂ := fun a => v a
  have hMV : 𝓜.mulVec V = 0 := by
    ext a
    rw [Matrix.mulVec, dotProduct, Pi.zero_apply]
    have := hv a a.2
    rw [← Finset.sum_coe_sort A] at this
    rw [← this]
    exact Finset.sum_congr rfl fun c _ => congrArg (· * V c) (dampedMatrix_entry A M t r a c)
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hU
  have hV : V = 0 := hinj (by rw [hMV, Matrix.mulVec_zero])
  exact congrFun hV ⟨i, hi⟩

end Inverse

/-! ## One elimination step -/

theorem schurStepM_symm (M : Matrix (Torus d m) (Torus d m) ℝ) (hM : ∀ i k, M i k = M k i)
    (p : Torus d m) (ξ : ℝ) (i k : Torus d m) : schurStepM M p ξ i k = schurStepM M p ξ k i := by
  unfold schurStepM
  by_cases h : i = p ∨ k = p
  · rw [if_pos h, if_pos (Or.comm.mp h)]
    by_cases hik : i = k
    · subst hik; rfl
    · rw [if_neg hik, if_neg (Ne.symm hik)]
  · rw [if_neg h, if_neg (fun h' => h (Or.comm.mp h'))]
    rw [hM i k, hM i p, hM p k, mul_comm (M p i)]

theorem dEnt_schur (t : ℝ) (r : Torus d m → ℂ) (M : Matrix (Torus d m) (Torus d m) ℝ)
    (p : Torus d m) (ξ : ℝ) (i l : Torus d m) (hi : i ≠ p) (hl : l ≠ p) :
    dEnt t r (schurStepM M p ξ) i l =
      dEnt t r M i l - dEnt t r M i p * dEnt t r M p l * (((M p p + ξ : ℝ) : ℂ))⁻¹ := by
  unfold dEnt schurStepM
  rw [if_neg (by tauto), if_neg hi, if_neg (Ne.symm hl)]
  push_cast
  ring

/-- **One Schur step is a rank-one change of the damped inverse on the survivors.** -/
theorem elim_step (A : Finset (Torus d m)) (M : Matrix (Torus d m) (Torus d m) ℝ) (t : ℝ)
    (r : Torus d m → ℂ) (hM : ∀ i k, M i k = M k i) (ht : 0 < t) (hr : ∀ i, 0 < (r i).im)
    (p : Torus d m) (hp : p ∈ A) (ξ : ℝ) :
    ∃ c : ℂ, ∀ i ∈ A.erase p, ∀ k ∈ A.erase p,
      fullInv (A.erase p) (schurStepM M p ξ) t r i k =
        fullInv A M t r i k + c * fullInv A M t r i p * fullInv A M t r p k := by
  set g := fullInv A M t r with hg
  set D := dEnt t r M with hD
  set q : ℂ := (((M p p + ξ : ℝ) : ℂ))⁻¹ with hq
  set β := D p p with hβ
  have E := fullInv_eqns A M t r hM ht hr
  have hM2 := schurStepM_symm M hM p ξ
  have hsplit : ∀ f : Torus d m → ℂ, ∑ l ∈ A, f l = f p + ∑ l ∈ A.erase p, f l :=
    fun f => (Finset.add_sum_erase A f hp).symm
  have hne : ∀ i ∈ A.erase p, i ≠ p := fun i hi => (Finset.mem_erase.mp hi).1
  have hmemA : ∀ i ∈ A.erase p, i ∈ A := fun i hi => (Finset.mem_erase.mp hi).2
  -- the four contracted equations
  have F1 : ∀ i ∈ A.erase p, ∀ k ∈ A.erase p,
      ∑ l ∈ A.erase p, D i l * g l k = (if i = k then 1 else 0) - D i p * g p k := by
    intro i hi k hk
    have := E i (hmemA i hi) k (hmemA k hk)
    rw [hsplit] at this
    rw [← this]; ring
  have F2 : ∀ i ∈ A.erase p, ∑ l ∈ A.erase p, D i l * g l p = -(D i p * g p p) := by
    intro i hi
    have := E i (hmemA i hi) p hp
    rw [hsplit, if_neg (hne i hi)] at this
    linear_combination this
  have F3 : ∀ k ∈ A.erase p, ∑ l ∈ A.erase p, D p l * g l k = -(β * g p k) := by
    intro k hk
    have := E p hp k (hmemA k hk)
    rw [hsplit, if_neg (Ne.symm (hne k hk))] at this
    linear_combination this
  have F4 : ∑ l ∈ A.erase p, D p l * g l p = 1 - β * g p p := by
    have := E p hp p hp
    rw [hsplit, if_pos rfl] at this
    linear_combination this
  have hD2 : ∀ i ∈ A.erase p, ∀ l ∈ A.erase p,
      dEnt t r (schurStepM M p ξ) i l = D i l - D i p * D p l * q := fun i hi l hl =>
    dEnt_schur t r M p ξ i l (hne i hi) (hne l hl)
  set κ := g p p + q * (1 - β * g p p) with hκ
  have hκ0 : κ ≠ 0 := by
    intro h0
    have hker := fullInv_kernel (A.erase p) (schurStepM M p ξ) t r hM2 ht hr
      (fun l => g l p) (by
        intro i hi
        rw [Finset.sum_congr rfl fun l hl => by rw [hD2 i hi l hl]]
        have : ∀ l, (D i l - D i p * D p l * q) * g l p =
            D i l * g l p - (D i p * q) * (D p l * g l p) := fun l => by ring
        rw [Finset.sum_congr rfl fun l _ => this l, Finset.sum_sub_distrib, ← Finset.mul_sum,
          F2 i hi, F4]
        linear_combination (-(D i p)) * h0)
    have h0' : ∑ l ∈ A.erase p, D p l * g l p = 0 :=
      Finset.sum_eq_zero fun l hl => by rw [hker l hl, mul_zero]
    rw [F4] at h0'
    have hgp : g p p = 0 := by
      have : κ = g p p := by rw [hκ, show 1 - β * g p p = 0 from h0', mul_zero, add_zero]
      rw [← this, h0]
    rw [hgp, mul_zero, sub_zero] at h0'
    exact one_ne_zero h0'
  refine ⟨(q * β - 1) / κ, ?_⟩
  set c := (q * β - 1) / κ with hc
  have hcκ : c * κ = q * β - 1 := div_mul_cancel₀ _ hκ0
  apply fullInv_of_eqns (A.erase p) (schurStepM M p ξ) t r hM2 ht hr
  intro i hi k hk
  rw [Finset.sum_congr rfl fun l hl => by rw [hD2 i hi l hl]]
  have : ∀ l, (D i l - D i p * D p l * q) * (g l k + c * g l p * g p k) =
      D i l * g l k + (c * g p k) * (D i l * g l p) - (D i p * q) * (D p l * g l k) -
        (D i p * q * c * g p k) * (D p l * g l p) := fun l => by ring
  rw [Finset.sum_congr rfl fun l _ => this l, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    F1 i hi k hk, F2 i hi, F3 k hk, F4]
  have hcκ' : c * (g p p + q * (1 - β * g p p)) = q * β - 1 := hcκ
  linear_combination (-(D i p * g p k)) * hcκ'

/-! ## Sequential core eliminations -/

/-- **Representation after sequential core eliminations**: `g' = G + G X G` on the survivors,
`X` supported on `core × core`. -/
theorem coreElim_repr (core A : Finset (Torus d m)) (Mh : Matrix (Torus d m) (Torus d m) ℝ)
    (t : ℝ) (r : Torus d m → ℂ) (hM : ∀ i k, Mh i k = Mh k i) (ht : 0 < t)
    (hr : ∀ i, 0 < (r i).im) {A' : Finset (Torus d m)} {M' : Matrix (Torus d m) (Torus d m) ℝ}
    (h : CoreElim core A Mh A' M') :
    (∀ i k, M' i k = M' k i) ∧ ∃ X : Matrix (Torus d m) (Torus d m) ℂ,
      (∀ b b', X b b' ≠ 0 → (b ∈ core ∧ b ∈ A ∧ b ∉ A') ∧ (b' ∈ core ∧ b' ∈ A ∧ b' ∉ A')) ∧
      ∀ i ∈ A', ∀ k ∈ A', fullInv A' M' t r i k = fullInv A Mh t r i k +
        ∑ b, ∑ b', fullInv A Mh t r i b * X b b' * fullInv A Mh t r b' k := by
  set G := fullInv A Mh t r with hG
  induction h with
  | refl =>
    refine ⟨hM, 0, fun b b' h => absurd rfl h, fun i _ k _ => ?_⟩
    simp only [Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    try rfl
  | @step A₁ M₁ p ξ hprev hp hpc ih =>
    have hA₁ : A₁ ⊆ A := (CoreElim.sub hprev).1
    obtain ⟨hM₁, X, hXs, hX⟩ := ih
    obtain ⟨c, hc⟩ := elim_step A₁ M₁ t r hM₁ ht hr p hp ξ
    refine ⟨schurStepM_symm M₁ hM₁ p ξ, ?_⟩
    let u : Torus d m → ℂ := fun b => (if b = p then 1 else 0) + ∑ b', X b b' * G b' p
    let w : Torus d m → ℂ := fun b' => (if b' = p then 1 else 0) + ∑ b, G p b * X b b'
    refine ⟨fun b b' => X b b' + c * u b * w b', ?_, ?_⟩
    · have hgrow : ∀ z, (z ∈ core ∧ z ∈ A ∧ z ∉ A₁) → (z ∈ core ∧ z ∈ A ∧ z ∉ A₁.erase p) :=
        fun z hz => ⟨hz.1, hz.2.1, fun h => hz.2.2 (Finset.mem_of_mem_erase h)⟩
      have hpgood : p ∈ core ∧ p ∈ A ∧ p ∉ A₁.erase p :=
        ⟨hpc, hA₁ hp, Finset.notMem_erase p A₁⟩
      intro b b' hbb
      by_cases hX0 : X b b' ≠ 0
      · exact ⟨hgrow b (hXs b b' hX0).1, hgrow b' (hXs b b' hX0).2⟩
      push_neg at hX0
      simp only at hbb
      rw [hX0, zero_add] at hbb
      have hu : u b ≠ 0 := fun h => hbb (by rw [h]; ring)
      have hw : w b' ≠ 0 := fun h => hbb (by rw [h]; ring)
      constructor
      · by_cases hbp : b = p
        · exact hbp ▸ hpgood
        by_contra hb
        apply hu
        simp only [u, if_neg hbp, zero_add]
        exact Finset.sum_eq_zero fun b' _ => by
          by_cases hz : X b b' = 0
          · rw [hz, zero_mul]
          · exact absurd (hgrow b (hXs b b' hz).1) hb
      · by_cases hbp : b' = p
        · exact hbp ▸ hpgood
        by_contra hb
        apply hw
        simp only [w, if_neg hbp, zero_add]
        exact Finset.sum_eq_zero fun b _ => by
          by_cases hz : X b b' = 0
          · rw [hz, mul_zero]
          · exact absurd (hgrow b' (hXs b b' hz).2) hb
    · intro i hi k hk
      have hiA : i ∈ A₁ := (Finset.mem_erase.mp hi).2
      have hkA : k ∈ A₁ := (Finset.mem_erase.mp hk).2
      rw [hc i hi k hk, hX i hiA k hkA, hX i hiA p hp, hX p hp k hkA]
      have hu' : ∑ b, G i b * u b = G i p + ∑ b, ∑ b', G i b * X b b' * G b' p := by
        simp only [u, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]
      have hw' : ∑ b', w b' * G b' k = G p k + ∑ b, ∑ b', G p b * X b b' * G b' k := by
        simp only [w, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]
        rw [Finset.sum_comm]
      rw [← hu', ← hw']
      have hexp : ∑ b, ∑ b', G i b * (X b b' + c * u b * w b') * G b' k =
          ∑ b, ∑ b', G i b * X b b' * G b' k + c * ((∑ b, G i b * u b) * ∑ b', w b' * G b' k) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b' _ => ?_
        ring
      rw [hexp]
      ring

end AndersonAC.AgentS78.DoneA
