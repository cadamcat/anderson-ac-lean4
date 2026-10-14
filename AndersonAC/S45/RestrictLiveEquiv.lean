import AndersonAC.S45.Definitions

/-! Reindexing S45 sweep sequences along index equivalences.

This file depends only on the definition layer (no `S45.Statements`, no norms).
It transports sequences, live states and analytic data along a bijection
`e : P ≃ Q`, for use in the live-set transport (`RestrictLive` gives the
subtype; this file reindexes the subtype to a `Fin` model for the
`Fin`-stated S45 sweep lemmas).  Live sets use `Finset.image` (plain
coercions, so `Equiv` simp lemmas match); sums reindex by exact bijection
(no vanishing arguments needed).  Operator norms, Ward identities,
comparators and dual forms are *not* transported here: the forward (b)/(c)
pipeline states those natively on the target type.
-/

noncomputable section
open Matrix
namespace AndersonAC.S45

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

/-- Reindex an ambient live state along an equivalence. -/
def LiveState.reindex (e : P ≃ Q) (a : LiveState P) : LiveState Q where
  live := Finset.image e a.live
  g := fun p q => a.g (e.symm p) (e.symm q)

/-- The reindexed live set unfolds to the image. -/
theorem LiveState.reindex_live_eq (e : P ≃ Q) (a : LiveState P) :
    ((a.reindex e).live) = Finset.image e a.live := rfl

/-- Reindex a sweep sequence along an equivalence (pivots mapped, scalars kept). -/
def Sequence.reindex (e : P ≃ Q) (q : Sequence P) : Sequence Q where
  length := q.length
  state k := (q.state k).reindex e
  pivot k := (q.pivot k).map e
  scalar := q.scalar

@[simp] theorem Sequence.reindex_length (e : P ≃ Q) (q : Sequence P) :
    (q.reindex e).length = q.length := rfl

@[simp] theorem Sequence.reindex_scalar (e : P ≃ Q) (q : Sequence P) (k : ℕ) :
    (q.reindex e).scalar k = q.scalar k := rfl

theorem Sequence.reindex_state_eq (e : P ≃ Q) (q : Sequence P) (k : ℕ) :
    (q.reindex e).state k = (q.state k).reindex e := rfl

/-- Reindexed pivots project back along the inverse. -/
theorem Sequence.reindex_pivot_val (e : P ≃ Q) (q : Sequence P) (k : ℕ) :
    (((q.reindex e).pivot k).map e.symm) = q.pivot k := by
  cases hq : q.pivot k with
  | none => simp [Sequence.reindex, hq]
  | some x => simp [Sequence.reindex, hq, Equiv.apply_symm_apply]

/-- The start live set transports (image of `univ` is `univ`). -/
theorem Sequence.reindex_start (e : P ≃ Q) (q : Sequence P)
    (hstart : (q.state 0).live = Finset.univ) :
    (((q.reindex e).state 0).live = Finset.univ) := by
  have hst : (((q.reindex e).state 0).live) =
      Finset.image e ((q.state 0).live) := rfl
  rw [hst, hstart]
  ext y
  simp only [Finset.mem_image, Finset.mem_univ]
  constructor
  · rintro ⟨x, _, rfl⟩
    trivial
  · intro _
    obtain ⟨x, rfl⟩ := Equiv.surjective e y
    exact ⟨x, trivial, rfl⟩

/-- Membership in the reindexed live set corresponds to membership upstairs. -/
theorem LiveState.mem_reindex (e : P ≃ Q) (a : LiveState P) (p : Q) :
    p ∈ (a.reindex e).live ↔ e.symm p ∈ a.live := by
  rw [LiveState.reindex_live_eq]
  constructor
  · intro h
    obtain ⟨x, hx, hxx⟩ := Finset.mem_image.mp h
    have hxe : e.symm p = x := by
      rw [← hxx]
      exact Equiv.symm_apply_apply e x
    rw [hxe]
    exact hx
  · intro h
    exact Finset.mem_image.mpr ⟨e.symm p, h, Equiv.apply_symm_apply e p⟩

/-- Live ports correspond across the reindexing. -/
def LiveState.reindexEquiv (e : P ≃ Q) (a : LiveState P) :
    (a.reindex e).live ≃ a.live :=
  Equiv.subtypeEquiv e.symm (fun q => LiveState.mem_reindex e a q)

/-- The reindexed state's matrix entries agree with the original ones. -/
theorem LiveState.reindex_state_g (e : P ≃ Q) (a : LiveState P) (r : P → ℂ)
    (r' : Q → ℂ) (i j : (a.reindex e).live) :
    (((a.reindex e).state r').g i j) =
      ((a.state r).g ((reindexEquiv e a) i) ((reindexEquiv e a) j)) := rfl

/-- The reindexed damping agrees up to the given linkage. -/
theorem LiveState.reindex_state_r (e : P ≃ Q) (a : LiveState P) (r : P → ℂ)
    (r' : Q → ℂ) (hr : ∀ q : Q, r' q = r (e.symm q)) (i : (a.reindex e).live) :
    (((a.reindex e).state r').r i) = ((a.state r).r ((reindexEquiv e a) i)) := by
  have h1 : (((a.reindex e).state r').r i) = r' i.1 := rfl
  have h2 : ((a.state r).r ((reindexEquiv e a) i)) = r ((reindexEquiv e a) i).1 := rfl
  rw [h1, h2, hr]
  rfl

/-- The normalized inverse agrees entry-wise. -/
theorem LiveState.reindex_state_h (e : P ≃ Q) (a : LiveState P) (r : P → ℂ)
    (r' : Q → ℂ) (t : ℝ) (i j : (a.reindex e).live) :
    (((a.reindex e).state r').h t i j) =
      ((a.state r).h t ((reindexEquiv e a) i) ((reindexEquiv e a) j)) := rfl

/-- The entrywise square agrees entry-wise. -/
theorem LiveState.reindex_state_K (e : P ≃ Q) (a : LiveState P) (r : P → ℂ)
    (r' : Q → ℂ) (t : ℝ) (i j : (a.reindex e).live) :
    (((a.reindex e).state r').K t i j) =
      ((a.state r).K t ((reindexEquiv e a) i) ((reindexEquiv e a) j)) := rfl

/-- Symmetry is preserved by reindexing. -/
theorem LiveState.reindex_state_symm (e : P ≃ Q) (a : LiveState P) (r : P → ℂ)
    (r' : Q → ℂ) (h : (a.state r).g.IsSymm) :
    (((a.reindex e).state r').g.IsSymm) := by
  apply Matrix.IsSymm.ext
  intro i j
  rw [reindex_state_g, reindex_state_g]
  exact (h.apply _ _).symm

/-- Fourth-power rows transport along the equivalence (universe version). -/
theorem LiveState.reindex_fourthRow_univ (e : P ≃ Q) (a : LiveState P) (r : P → ℂ)
    (r' : Q → ℂ) (t : ℝ) (i : (a.reindex e).live) :
    (((a.reindex e).state r').fourthRow t Finset.univ i) =
      ((a.state r).fourthRow t Finset.univ ((reindexEquiv e a) i)) := by
  simp only [State.fourthRow]
  have hsum : (∑ j' ∈ (Finset.univ : Finset (a.reindex e).live), ‖((a.reindex e).state r').h t i j'‖^4) =
      (∑ j ∈ (Finset.univ : Finset a.live), ‖((a.reindex e).state r').h t i ((reindexEquiv e a).symm j)‖^4) :=
    (Equiv.sum_comp (reindexEquiv e a).symm _).symm
  rw [hsum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [reindex_state_h, Equiv.apply_symm_apply]

/-- Submatrix along a reindexing preserves units. -/
theorem LiveState.reindex_isUnit (e : P ≃ Q) (a : LiveState P)
    (M : CMat a.live) (hM : IsUnit M) :
    IsUnit (M.submatrix (reindexEquiv e a) (reindexEquiv e a)) := by
  obtain ⟨u, rfl⟩ := hM
  refine ⟨⟨((↑u : CMat a.live).submatrix (reindexEquiv e a) (reindexEquiv e a)),
    ((↑(u⁻¹) : CMat a.live).submatrix (reindexEquiv e a) (reindexEquiv e a)),
    ?_, ?_⟩, rfl⟩
  · rw [Matrix.submatrix_mul_equiv _ _ _ (reindexEquiv e a) _,
      Units.mul_inv]
    have h1 : ((1 : CMat a.live).submatrix (reindexEquiv e a) (reindexEquiv e a)) = 1 := by
      ext x y
      simp only [Matrix.submatrix_apply, Matrix.one_apply]
      by_cases hij : x = y
      · subst hij
        simp
      · have hne : (reindexEquiv e a) x ≠ (reindexEquiv e a) y :=
          fun h => hij ((reindexEquiv e a).injective h)
        simp [hij, hne]
    rw [h1]
  · rw [Matrix.submatrix_mul_equiv _ _ _ (reindexEquiv e a) _,
      Units.inv_mul]
    have h1 : ((1 : CMat a.live).submatrix (reindexEquiv e a) (reindexEquiv e a)) = 1 := by
      ext x y
      simp only [Matrix.submatrix_apply, Matrix.one_apply]
      by_cases hij : x = y
      · subst hij
        simp
      · have hne : (reindexEquiv e a) x ≠ (reindexEquiv e a) y :=
          fun h => hij ((reindexEquiv e a).injective h)
        simp [hij, hne]
    rw [h1]

/-- The transformed lag agrees along the reindexing. -/
theorem LiveState.reindex_lag (e : P ≃ Q) (a : LiveState P) (r : P → ℂ)
    (r' : Q → ℂ) (t : ℝ) (hr : ∀ q : Q, r' q = r (e.symm q))
    (hU : IsUnit (1 - (a.state r).K t))
    (i : (a.reindex e).live) :
    (((a.reindex e).state r').lag t i) =
      ((a.state r).lag t ((reindexEquiv e a) i)) := by
  have hKmat : ((((a.reindex e).state r').K t)) =
      ((((a.state r).K t).submatrix (reindexEquiv e a) (reindexEquiv e a))) := by
    ext x y
    exact reindex_state_K e a r r' t x y
  have h1K : (1 - (((a.reindex e).state r').K t)) =
      (((1 - (a.state r).K t).submatrix (reindexEquiv e a) (reindexEquiv e a))) := by
    have hsub2 : ((((1 - (a.state r).K t).submatrix (reindexEquiv e a) (reindexEquiv e a)))) =
        (1 : CMat _).submatrix (reindexEquiv e a) (reindexEquiv e a) -
          (((a.state r).K t).submatrix (reindexEquiv e a) (reindexEquiv e a)) := by
      simp only [Matrix.submatrix_sub, Pi.sub_apply]
    rw [hsub2]
    have h1 : ((1 : CMat a.live).submatrix (reindexEquiv e a) (reindexEquiv e a)) = 1 := by
      ext x y
      simp only [Matrix.submatrix_apply, Matrix.one_apply]
      by_cases hij : x = y
      · subst hij
        simp
      · have hne : (reindexEquiv e a) x ≠ (reindexEquiv e a) y :=
          fun h => hij ((reindexEquiv e a).injective h)
        simp [hij, hne]
    rw [h1, hKmat]
  have hU' : IsUnit (1 - (((a.reindex e).state r').K t)) := by
    rw [h1K]
    exact reindex_isUnit e a _ hU
  have hraw : ((((a.reindex e).state r').rawLag)) =
      (((a.state r).rawLag) ∘ (reindexEquiv e a)) := by
    funext x
    have hg_x := reindex_state_g e a r r' x x
    have hr_x := reindex_state_r e a r r' hr x
    simp only [State.rawLag, Function.comp_apply, hg_x, hr_x]
  have hdet : IsUnit ((1 - (a.state r).K t).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp hU
  have hdet' : IsUnit ((1 - (((a.reindex e).state r').K t)).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp hU'
  have hPlag : ((1 - (a.state r).K t) *ᵥ ((a.state r).lag t)) =
      (a.state r).rawLag := by
    have hlag : (a.state r).lag t =
        ((((1 - (a.state r).K t)⁻¹)) *ᵥ ((a.state r).rawLag)) := rfl
    rw [hlag, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
      Matrix.one_mulVec]
  have step2 : ((1 - (((a.reindex e).state r').K t)) *ᵥ
      (((a.state r).lag t) ∘ (reindexEquiv e a))) =
      (((a.reindex e).state r').rawLag) := by
    rw [h1K, hraw]
    have hmv := Matrix.submatrix_mulVec_equiv (1 - (a.state r).K t)
      (((a.state r).lag t) ∘ (reindexEquiv e a)) (reindexEquiv e a) (reindexEquiv e a)
    rw [hmv]
    have hcomp : ((((a.state r).lag t) ∘ (reindexEquiv e a)) ∘ (reindexEquiv e a).symm) =
        (a.state r).lag t := by
      funext j
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
    rw [hcomp, hPlag]
  have hclose : ((((a.state r).lag t) ∘ (reindexEquiv e a))) =
      ((((a.reindex e).state r').lag t)) := by
    have hlag' : (((a.reindex e).state r').lag t) =
        (((1 - (((a.reindex e).state r').K t))⁻¹) *ᵥ
          (((a.reindex e).state r').rawLag)) := rfl
    rw [hlag', ← step2, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hdet', Matrix.one_mulVec]
  exact (congrFun hclose i).symm

/-- Ambient lags agree across the reindexing. -/
theorem LiveState.reindex_ambientLag (e : P ≃ Q) (a : LiveState P) (r : P → ℂ)
    (r' : Q → ℂ) (t : ℝ) (hr : ∀ q : Q, r' q = r (e.symm q))
    (hU : IsUnit (1 - (a.state r).K t))
    (p : Q) (hp : p ∈ (a.reindex e).live) :
    (((a.reindex e).ambientLag t r') p) = ((a.ambientLag t r) (e.symm p)) := by
  simp only [LiveState.ambientLag]
  have hpP : e.symm p ∈ a.live := by
    have h := (LiveState.mem_reindex e a p).mp hp
    simpa using h
  simp only [hp, hpP, if_true]
  have hl := LiveState.reindex_lag e a r r' t hr hU ⟨p, hp⟩
  exact hl

/-- Submatrix along a reindexing preserves inverses (under invertibility). -/
theorem LiveState.reindex_inv_of_isUnit (e : P ≃ Q) (a : LiveState P)
    (M : CMat a.live) (hM : IsUnit M) :
    (((M.submatrix (reindexEquiv e a) (reindexEquiv e a))⁻¹)) =
      (((M⁻¹).submatrix (reindexEquiv e a) (reindexEquiv e a))) := by
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).mp hM
  have hU : IsUnit (M.submatrix (reindexEquiv e a) (reindexEquiv e a)) :=
    LiveState.reindex_isUnit e a M hM
  have hdetS : IsUnit ((M.submatrix (reindexEquiv e a) (reindexEquiv e a))).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hU
  have hone : ((1 : CMat a.live).submatrix (reindexEquiv e a) (reindexEquiv e a)) = 1 := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.one_apply]
    by_cases hij : x = y
    · subst hij
      simp
    · have hne : (reindexEquiv e a) x ≠ (reindexEquiv e a) y :=
        fun h => hij ((reindexEquiv e a).injective h)
      simp [hij, hne]
  have h1 : M.submatrix (reindexEquiv e a) (reindexEquiv e a) *
      (M⁻¹).submatrix (reindexEquiv e a) (reindexEquiv e a) = 1 := by
    have hmul := Matrix.submatrix_mul_equiv M (M⁻¹)
      (reindexEquiv e a) (reindexEquiv e a) (reindexEquiv e a)
    rw [hmul, Matrix.mul_nonsing_inv _ hdet, hone]
  have h2 : (M⁻¹).submatrix (reindexEquiv e a) (reindexEquiv e a) *
      M.submatrix (reindexEquiv e a) (reindexEquiv e a) = 1 := by
    have hmul := Matrix.submatrix_mul_equiv (M⁻¹) M
      (reindexEquiv e a) (reindexEquiv e a) (reindexEquiv e a)
    rw [hmul, Matrix.nonsing_inv_mul _ hdet, hone]
  have hcalc : (M⁻¹).submatrix (reindexEquiv e a) (reindexEquiv e a) =
      (M.submatrix (reindexEquiv e a) (reindexEquiv e a))⁻¹ := by
    calc (M⁻¹).submatrix (reindexEquiv e a) (reindexEquiv e a)
        = (M⁻¹).submatrix (reindexEquiv e a) (reindexEquiv e a) * 1 := (mul_one _).symm
      _ = (M⁻¹).submatrix (reindexEquiv e a) (reindexEquiv e a) *
          (M.submatrix (reindexEquiv e a) (reindexEquiv e a) *
            (M.submatrix (reindexEquiv e a) (reindexEquiv e a))⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hdetS]
      _ = ((M⁻¹).submatrix (reindexEquiv e a) (reindexEquiv e a) *
          M.submatrix (reindexEquiv e a) (reindexEquiv e a)) *
          (M.submatrix (reindexEquiv e a) (reindexEquiv e a))⁻¹ := by
          rw [mul_assoc]
      _ = 1 * (M.submatrix (reindexEquiv e a) (reindexEquiv e a))⁻¹ := by rw [h2]
      _ = (M.submatrix (reindexEquiv e a) (reindexEquiv e a))⁻¹ := one_mul _
  exact hcalc.symm

/-- A single step transports along the equivalence. -/
theorem StepRel_reindex {t : ℝ} {r : P → ℂ} {r' : Q → ℂ} {a b : LiveState P}
    {x : P} {ξ : ℝ} (e : P ≃ Q) (hr : ∀ q : Q, r' q = r (e.symm q))
    (hrel : StepRel t r a b x ξ) :
    StepRel t r' (a.reindex e) (b.reindex e) (e x) ξ := by
  have hrx : r' (e x) = r x := by
    rw [hr]
    exact congrArg r (Equiv.symm_apply_apply e x)
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (e x) ∈ Finset.image e a.live
    rw [← LiveState.reindex_live_eq]
    exact Finset.mem_image.mpr ⟨x, hrel.pivot_live, rfl⟩
  · show Finset.image e b.live = (Finset.image e a.live).erase (e x)
    rw [hrel.survivors]
    exact Finset.image_erase e.injective _ _
  · ext p q
    have hmem : ∀ p : Q, p ∈ (a.reindex e).live ↔ e.symm p ∈ a.live :=
      fun p => LiveState.mem_reindex e a p
    have hmemB : ∀ p : Q, p ∈ (b.reindex e).live ↔ e.symm p ∈ b.live :=
      fun p => LiveState.mem_reindex e b p
    have e2 : ∀ p q : Q, ((a.reindex e).g p q) = a.g (e.symm p) (e.symm q) :=
      fun p q => rfl
    have e2b : ∀ p q : Q, ((b.reindex e).g p q) = b.g (e.symm p) (e.symm q) :=
      fun p q => rfl
    rw [e2b]
    have hupd := hrel.update
    rw [hupd]
    by_cases hpb : e.symm p ∈ b.live
    · have hpbQ : p ∈ (b.reindex e).live := (hmemB p).mpr hpb
      by_cases hqb : e.symm q ∈ b.live
      · have hqbQ : q ∈ (b.reindex e).live := (hmemB q).mpr hqb
        simp [mask, pad, restrict, Matrix.submatrix_apply, hpb, hqb, hpbQ, hqbQ,
          e2, hrx, Equiv.symm_apply_apply]
        try rfl
      · have hqbQ : q ∉ (b.reindex e).live := fun h => hqb ((hmemB q).mp h)
        simp [mask, pad, hpb, hqb, hpbQ, hqbQ]
    · have hpbQ : p ∉ (b.reindex e).live := fun h => hpb ((hmemB p).mp h)
      simp [mask, pad, hpb, hpbQ]
  · rw [hrx]
    have e2xx : ((a.reindex e).g (e x) (e x)) = a.g x x := by
      have h1 : ((a.reindex e).g (e x) (e x)) =
          a.g (e.symm (e x)) (e.symm (e x)) := rfl
      rw [h1, Equiv.symm_apply_apply]
    rw [e2xx]
    exact hrel.denominator

/-- Well-formedness transports along the equivalence. -/
theorem Sequence.wellFormed_reindex (e : P ≃ Q) (q : Sequence P) (t : ℝ) (r : P → ℂ)
    (r' : Q → ℂ) (hr : ∀ q_ : Q, r' q_ = r (e.symm q_))
    (hseq : q.wellFormed t r) : ((q.reindex e).wellFormed t r') := by
  constructor
  · intro k hk
    have hk' : k ≤ q.length := by simpa [Sequence.reindex_length] using hk
    have hvan : ∀ u v : P, u ∉ (q.state k).live ∨ v ∉ (q.state k).live →
        (q.state k).g u v = 0 := by
      intro u v h
      have em := congrArg (fun M : CMat P => M u v) (hseq.1 k hk')
      rcases h with hi | hj
      · simpa [mask, pad, hi] using em
      · simpa [mask, pad, hj] using em
    ext a b
    have hmem : ∀ p : Q, p ∈ (((q.reindex e).state k)).live ↔
        e.symm p ∈ (q.state k).live := by
      intro p
      rw [Sequence.reindex_state_eq e q k]
      exact LiveState.mem_reindex e (q.state k) p
    by_cases hp : a ∈ ((q.reindex e).state k).live
    · have hpP : e.symm a ∈ (q.state k).live := (hmem a).mp hp
      by_cases hq : b ∈ ((q.reindex e).state k).live
      · have hqP : e.symm b ∈ (q.state k).live := (hmem b).mp hq
        simp [mask, pad, restrict, Matrix.submatrix_apply, hp, hq, hpP, hqP]
        try rfl
      · have hqP : e.symm b ∉ (q.state k).live :=
          fun h => hq ((hmem b).mpr h)
        have hz := hvan (e.symm a) (e.symm b) (Or.inr hqP)
        have eg : (((q.reindex e).state k).g a b) =
            ((q.state k).g (e.symm a) (e.symm b)) := rfl
        simp [mask, pad, restrict, Matrix.submatrix_apply, hp, hq, hpP, hqP, eg, hz]
        try rfl
    · have hpP : e.symm a ∉ (q.state k).live := fun h => hp ((hmem a).mpr h)
      have hz := hvan (e.symm a) (e.symm b) (Or.inl hpP)
      have eg : (((q.reindex e).state k).g a b) =
          ((q.state k).g (e.symm a) (e.symm b)) := rfl
      simp [mask, pad, restrict, Matrix.submatrix_apply, hp, hpP, eg, hz]
      try rfl
  · intro k hk
    have hk' : k < q.length := by simpa [Sequence.reindex_length] using hk
    have hstep := hseq.2 k hk'
    cases hpv : q.pivot k with
    | none =>
        have hqn : (q.reindex e).pivot k = none := by simp [Sequence.reindex, hpv]
        have hsame : q.state (k + 1) = q.state k := by simpa [hpv] using hstep
        simp [Sequence.reindex, hpv]
        exact congrArg (LiveState.reindex e) hsame
    | some x =>
        have hrel : StepRel t r (q.state k) (q.state (k + 1)) x (q.scalar k) := by
          simpa [hpv] using hstep
        have hr := StepRel_reindex e hr hrel
        simp [Sequence.reindex, hpv]
        exact hr

end AndersonAC.S45
