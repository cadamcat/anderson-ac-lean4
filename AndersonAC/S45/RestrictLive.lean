import AndersonAC.S45.Definitions

/-! Live-set restriction for S45 sweep sequences.

This file depends only on the definition layer.  In particular it does not import
`S45.Statements`, the planning module that contains proof holes.
-/

noncomputable section
open Matrix
namespace AndersonAC.S45

variable {P : Type*} [Fintype P] [DecidableEq P]
variable {t : ℝ} {r : P → ℂ}

/-- Restrict an ambient live state to ports in `S`.  The ambient matrix is pulled
back along the subtype map; its existing zero mask is preserved. -/
def LiveState.restrictLive (S : Finset P) (a : LiveState P) :
    LiveState {p // p ∈ S} where
  live := Finset.univ.filter (fun p : {p // p ∈ S} => (p : P) ∈ a.live)
  g := fun p q => a.g p.1 q.1

theorem restrict_mask {α : Type*} [Zero α] (S L : Finset P) (A : Matrix P P α) :
    restrict (mask L A) S =
      mask (Finset.univ.filter (fun p : {p // p ∈ S} => (p : P) ∈ L))
        (restrict A S) := by
  ext p q
  by_cases hp : (p : P) ∈ L <;> by_cases hq : (q : P) ∈ L <;>
    simp [mask, pad, restrict, hp, hq]

@[simp] theorem LiveState.mem_restrictLive (S : Finset P) (a : LiveState P)
    (p : {p // p ∈ S}) : p ∈ (a.restrictLive S).live ↔ (p : P) ∈ a.live := by
  simp [LiveState.restrictLive]

/-- Reinterpret the pivots as ports in `S`; an out-of-set pivot is dropped.  Under
`pivotsIn`, it is never dropped along the sequence's defined steps. -/
def Sequence.restrictLive (S : Finset P) (q : Sequence P) :
    Sequence {p // p ∈ S} where
  length := q.length
  state k := (q.state k).restrictLive S
  pivot k := match q.pivot k with
    | none => none
    | some p => if hp : p ∈ S then some ⟨p, hp⟩ else none
  scalar := q.scalar

@[simp] theorem Sequence.restrictLive_length (S : Finset P) (q : Sequence P) :
    (q.restrictLive S).length = q.length := rfl

@[simp] theorem Sequence.restrictLive_scalar (S : Finset P) (q : Sequence P) (k : ℕ) :
    (q.restrictLive S).scalar k = q.scalar k := rfl

@[simp] theorem Sequence.restrictLive_pivot_none (S : Finset P) (q : Sequence P)
    (k : ℕ) (h : q.pivot k = none) : (q.restrictLive S).pivot k = none := by
  simp [Sequence.restrictLive, h]

theorem Sequence.restrictLive_pivot_some (S : Finset P) (q : Sequence P)
    (k : ℕ) (p : P) (hp : p ∈ S) (h : q.pivot k = some p) :
    (q.restrictLive S).pivot k = some ⟨p, hp⟩ := by
  simp [Sequence.restrictLive, h, hp]

/-- Every live port remains in the initial set if all pivots lie in it. -/
theorem Sequence.live_subset_initial (q : Sequence P) (S : Finset P)
    (hstart : (q.state 0).live = S)
    (hseq : q.wellFormed t r) :
    ∀ k ≤ q.length, (q.state k).live ⊆ S := by
  intro k hk
  induction k with
  | zero =>
      simpa [hstart]
  | succ k ih =>
      have hklt : k < q.length := Nat.lt_of_succ_le hk
      have hprev : k ≤ q.length := Nat.le_of_lt hklt
      have hstep := hseq.2 k hklt
      cases hp : q.pivot k with
      | none =>
          have hsame : q.state (k + 1) = q.state k := by simpa [hp] using hstep
          rw [hsame]
          exact ih hprev
      | some p =>
          have hrel : StepRel t r (q.state k) (q.state (k + 1)) p (q.scalar k) := by
            simpa [hp] using hstep
          intro x hx
          rw [hrel.survivors] at hx
          exact ih hprev (Finset.mem_of_mem_erase hx)

/-- The restricted sequence starts with every port of its subtype when the
original sequence starts with exactly `S`. -/
theorem Sequence.restrictLive_start (q : Sequence P) (S : Finset P)
    (hstart : (q.state 0).live = S) :
    ((q.restrictLive S).state 0).live = Finset.univ := by
  ext p
  simp [Sequence.restrictLive, LiveState.restrictLive, hstart]

/-- Well-formedness is preserved when each deleted pivot belongs to `S`. -/
theorem Sequence.wellFormed_restrictLive (q : Sequence P) (S : Finset P)
    (hseq : q.wellFormed t r)
    (hpiv : ∀ k < q.length, ∀ p, q.pivot k = some p → p ∈ S) :
    (q.restrictLive S).wellFormed t (fun p => r p.1) := by
  constructor
  · intro k hk
    ext p q'
    have hmaskR := congrArg (fun A : CMat P => restrict A S) (hseq.1 k hk)
    rw [restrict_mask S (q.state k).live (q.state k).g] at hmaskR
    have hentry := congrArg (fun A : CMat {p // p ∈ S} => A p q') hmaskR
    exact hentry
  · intro k hk
    have hstep := hseq.2 k hk
    cases hp : q.pivot k with
    | none =>
        have hsame : q.state (k + 1) = q.state k := by simpa [hp] using hstep
        simp [Sequence.restrictLive, hp]
        exact congrArg (LiveState.restrictLive S) hsame
    | some x =>
        have hxS : x ∈ S := hpiv k hk x hp
        have hrel : StepRel t r (q.state k) (q.state (k + 1)) x (q.scalar k) := by
          simpa [hp] using hstep
        simp [Sequence.restrictLive, hp, hxS]
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa [LiveState.restrictLive] using hrel.pivot_live
        · change Finset.univ.filter
              (fun p : {p // p ∈ S} => (p : P) ∈ (q.state (k + 1)).live) =
            (Finset.univ.filter
              (fun p : {p // p ∈ S} => (p : P) ∈ (q.state k).live)).erase ⟨x, hxS⟩
          rw [hrel.survivors]
          ext p
          simp [Finset.mem_erase, Subtype.ext_iff]
        · ext p q'
          let F : CMat P := fun i j =>
            (q.state k).g i j -
              ((q.scalar k : ℂ) + t * r x) * (q.state k).g i x * (q.state k).g x j /
                (1 + ((q.scalar k : ℂ) + t * r x) * (q.state k).g x x)
          have hu := congrArg (fun A : CMat P => restrict A S) hrel.update
          rw [restrict_mask S (q.state (k + 1)).live F] at hu
          have huEntry := congrArg (fun A : CMat {p // p ∈ S} => A p q') hu
          exact huEntry
        · simpa [LiveState.restrictLive] using hrel.denominator

/-! ## Transports along the subtype inclusion.

`S` is the initial (hence, under `hpiv`, every) live set.  All analytic data of the
restricted sequence is entry-wise equal to the original data at the projected ports.
No statement here mentions operator norms; norm conclusions are assembled by consumers
(e.g. via `AgentS78.PadNorm`), which this layer must not import.
-/

/-- The port damping pulled back to the live subtype. -/
def restrictDamping (S : Finset P) (r : P → ℂ) : {p // p ∈ S} → ℂ :=
  fun p => r ↑p

/-- Restricted pivots project to the original pivots. -/
theorem Sequence.restrictLive_pivot_val (S : Finset P) (q : Sequence P)
    (hpiv : ∀ k < q.length, ∀ p, q.pivot k = some p → p ∈ S)
    (k : ℕ) (hk : k < q.length) :
    ((q.restrictLive S).pivot k).map Subtype.val = q.pivot k := by
  cases hq : q.pivot k with
  | none => simp [Sequence.restrictLive, hq]
  | some p =>
      have hp : p ∈ S := hpiv k hk p hq
      simp [Sequence.restrictLive, hq, hp]

/-- The live ports of the restriction, as a subtype of the original live ports. -/
def LiveState.subLiveEquiv (S : Finset P) (a : LiveState P) (hsub : a.live ⊆ S) :
    (a.restrictLive S).live ≃ a.live where
  toFun i := ⟨(i.1 : P), (mem_restrictLive S a i.1).mp i.2⟩
  invFun j := ⟨⟨j.1, hsub j.2⟩, (mem_restrictLive S a ⟨j.1, hsub j.2⟩).mpr j.2⟩
  left_inv i := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv j := by apply Subtype.ext; rfl

@[simp] theorem LiveState.subLiveEquiv_val (S : Finset P) (a : LiveState P)
    (hsub : a.live ⊆ S) (i : (a.restrictLive S).live) :
    (((subLiveEquiv S a hsub i : a.live) : P)) = (i.1 : P) := rfl

/-- The restricted state's matrix entries agree with the original ones. -/
theorem LiveState.restrictLive_state_g (S : Finset P) (a : LiveState P) (r : P → ℂ)
    (i j : (a.restrictLive S).live) :
    ((a.restrictLive S).state (restrictDamping S r)).g i j =
      (a.state r).g ⟨(i.1 : P), (mem_restrictLive S a i.1).mp i.2⟩
        ⟨(j.1 : P), (mem_restrictLive S a j.1).mp j.2⟩ := rfl

/-- The restricted state's damping agrees with the original one. -/
theorem LiveState.restrictLive_state_r (S : Finset P) (a : LiveState P) (r : P → ℂ)
    (i : (a.restrictLive S).live) :
    ((a.restrictLive S).state (restrictDamping S r)).r i =
      (a.state r).r ⟨(i.1 : P), (mem_restrictLive S a i.1).mp i.2⟩ := rfl

/-- The imaginary-damping coordinate agrees. -/
theorem LiveState.restrictLive_state_p (S : Finset P) (a : LiveState P) (r : P → ℂ)
    (i : (a.restrictLive S).live) :
    ((a.restrictLive S).state (restrictDamping S r)).p i =
      (a.state r).p ⟨(i.1 : P), (mem_restrictLive S a i.1).mp i.2⟩ := rfl

/-- The imaginary-diagonal coordinate agrees. -/
theorem LiveState.restrictLive_state_q (S : Finset P) (a : LiveState P) (r : P → ℂ)
    (i : (a.restrictLive S).live) :
    ((a.restrictLive S).state (restrictDamping S r)).q i =
      (a.state r).q ⟨(i.1 : P), (mem_restrictLive S a i.1).mp i.2⟩ := rfl

/-- The normalized inverse agrees entry-wise. -/
theorem LiveState.restrictLive_state_h (S : Finset P) (a : LiveState P) (r : P → ℂ)
    (t : ℝ) (i j : (a.restrictLive S).live) :
    ((a.restrictLive S).state (restrictDamping S r)).h t i j =
      (a.state r).h t ⟨(i.1 : P), (mem_restrictLive S a i.1).mp i.2⟩
        ⟨(j.1 : P), (mem_restrictLive S a j.1).mp j.2⟩ := rfl

/-- The entrywise square agrees entry-wise. -/
theorem LiveState.restrictLive_state_K (S : Finset P) (a : LiveState P) (r : P → ℂ)
    (t : ℝ) (i j : (a.restrictLive S).live) :
    ((a.restrictLive S).state (restrictDamping S r)).K t i j =
      (a.state r).K t ⟨(i.1 : P), (mem_restrictLive S a i.1).mp i.2⟩
        ⟨(j.1 : P), (mem_restrictLive S a j.1).mp j.2⟩ := rfl

/-- The absolute square agrees entry-wise. -/
theorem LiveState.restrictLive_state_F (S : Finset P) (a : LiveState P) (r : P → ℂ)
    (t : ℝ) (i j : (a.restrictLive S).live) :
    ((a.restrictLive S).state (restrictDamping S r)).F t i j =
      (a.state r).F t ⟨(i.1 : P), (mem_restrictLive S a i.1).mp i.2⟩
        ⟨(j.1 : P), (mem_restrictLive S a j.1).mp j.2⟩ := rfl

/-- Projecting a restricted state back gives the original ambient state. -/
theorem Sequence.restrictLive_state_eq (S : Finset P) (q : Sequence P) (k : ℕ) :
    (q.restrictLive S).state k = (q.state k).restrictLive S := rfl

/-- Symmetry is preserved by restriction. -/
theorem LiveState.restrictLive_state_symm (S : Finset P) (a : LiveState P) (r : P → ℂ)
    (h : (a.state r).g.IsSymm) :
    ((a.restrictLive S).state (restrictDamping S r)).g.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  rw [restrictLive_state_g, restrictLive_state_g]
  exact (h.apply _ _).symm

/-- The diagonal comparison data is preserved (for `cumulative_schur` prefixes). -/
theorem Sequence.hstep_restrictLive (q : Sequence P) (S : Finset P) (t : ℝ) (r : P → ℂ)
    (k : ℕ) (hsub : (q.state k).live ⊆ S)
    (hK : ∀ x : (q.state k).live, 1 - ((q.state k).state r).K t x x ≠ 0 ∧
      0 < ((q.state k).state r).q x -
        ((q.state k).state r).p x * ((q.state k).state r).F t x x) :
    ∀ x' : ((q.restrictLive S).state k).live,
      1 - (((q.restrictLive S).state k).state (restrictDamping S r)).K t x' x' ≠ 0 ∧
      0 < (((q.restrictLive S).state k).state (restrictDamping S r)).q x' -
        (((q.restrictLive S).state k).state (restrictDamping S r)).p x' *
          (((q.restrictLive S).state k).state (restrictDamping S r)).F t x' x' := by
  intro x'
  have h2 : x'.1 ∈ ((q.state k).restrictLive S).live :=
    by simpa only [Sequence.restrictLive_state_eq] using x'.2
  exact hK ((LiveState.subLiveEquiv S (q.state k) hsub) ⟨x'.1, h2⟩)

/-- Masked ambient matrices vanish outside the live set. -/
theorem LiveState.mask_entry_zero (a : LiveState P) (h : a.g = mask a.live a.g)
    (i j : P) (hij : i ∉ a.live ∨ j ∉ a.live) : a.g i j = 0 := by
  rcases hij with hi | hj
  · have e := congrArg (fun M : CMat P => M i j) h
    simpa [mask, pad, hi] using e
  · have e := congrArg (fun M : CMat P => M i j) h
    simpa [mask, pad, hj] using e

/-- The restricted ambient matrix agrees with the original on the subtype. -/
theorem LiveState.restrictLive_ambient_g (S : Finset P) (a : LiveState P) (r : P → ℂ)
    (p q : {p // p ∈ S}) :
    ((a.restrictLive S).ambient (restrictDamping S r)).g p q =
      (a.ambient r).g p.1 q.1 := by
  have e1 : ((a.restrictLive S).ambient (restrictDamping S r)).g
      = mask ((a.restrictLive S).live) ((a.restrictLive S).g) := rfl
  have e2 : (a.ambient r).g = mask a.live a.g := rfl
  rw [e1, e2]
  by_cases hp : p ∈ (a.restrictLive S).live
  · have hpP : (p : P) ∈ a.live := (mem_restrictLive S a p).mp hp
    by_cases hq : q ∈ (a.restrictLive S).live
    · have hqP : (q : P) ∈ a.live := (mem_restrictLive S a q).mp hq
      simp only [mask, pad, hp, hq, hpP, hqP, ite_true, ite_false]
      simp only [restrict, Matrix.submatrix_apply, LiveState.restrictLive]
      try rfl
    · have hqP : (q : P) ∉ a.live := fun h => hq ((mem_restrictLive S a q).mpr h)
      simp only [mask, pad, hp, hq, hpP, hqP, ite_true, ite_false]
      simp only [restrict, Matrix.submatrix_apply, LiveState.restrictLive]
      try rfl
  · have hpP : (p : P) ∉ a.live := fun h => hp ((mem_restrictLive S a p).mpr h)
    simp only [mask, pad, hp, hpP, ite_true, ite_false]
    simp only [restrict, Matrix.submatrix_apply, LiveState.restrictLive]
    try rfl

/-- Fourth-power rows transport along the subtype equivalence. -/
theorem LiveState.restrictLive_fourthRow (S : Finset P) (a : LiveState P) (r : P → ℂ)
    (t : ℝ) (hsub : a.live ⊆ S) (C : Finset a.live)
    (i : (a.restrictLive S).live) :
    ((a.restrictLive S).state (restrictDamping S r)).fourthRow t
        (C.map (subLiveEquiv S a hsub).symm.toEmbedding) i =
      (a.state r).fourthRow t C ((subLiveEquiv S a hsub) i) := by
  simp only [State.fourthRow, Finset.sum_map]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [LiveState.restrictLive_state_h]
  rfl

/-- A diagonal sandwich has no sums entry-wise. -/
theorem diagonal_sandwich_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (M : RMat ι) (i j : ι) :
    (diagonal d * M * diagonal d) i j = d i * M i j * d j := by
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq,
    Finset.sum_ite_eq']
  by_cases hij : i = j <;> simp [hij]

/-- The comparator matrix agrees entry-wise. -/
theorem LiveState.restrictLive_state_D (S : Finset P) (a : LiveState P) (r : P → ℂ)
    (t : ℝ) (i j : (a.restrictLive S).live) :
    ((a.restrictLive S).state (restrictDamping S r)).D t i j =
      (a.state r).D t ⟨(i.1 : P), (mem_restrictLive S a i.1).mp i.2⟩
        ⟨(j.1 : P), (mem_restrictLive S a j.1).mp j.2⟩ := by
  simp only [State.D, Matrix.sub_apply, diagonal_sandwich_apply, Matrix.diagonal_apply,
    LiveState.restrictLive_state_p, LiveState.restrictLive_state_q,
    LiveState.restrictLive_state_F, Subtype.ext_iff]
  try rfl

/-- Quadratic forms transport along the subtype equivalence. -/
theorem LiveState.restrictLive_qform (S : Finset P) (a : LiveState P)
    (hsub : a.live ⊆ S) (D0' : RMat (a.restrictLive S).live) (D0 : RMat a.live)
    (hD : ∀ x y : (a.restrictLive S).live, D0' x y =
      D0 ((subLiveEquiv S a hsub) x) ((subLiveEquiv S a hsub) y))
    (f' : (a.restrictLive S).live → ℝ) :
    qform D0' f' = qform D0 (fun j : a.live => f' ((subLiveEquiv S a hsub).symm j)) := by
  classical
  set e := subLiveEquiv S a hsub with he
  simp only [qform, Matrix.mulVec, dotProduct]
  calc ∑ i' : (a.restrictLive S).live, f' i' * ∑ j', D0' i' j' * f' j'
      = ∑ j : a.live, f' (e.symm j) * ∑ j', D0' (e.symm j) j' * f' j' :=
        (Equiv.sum_comp e.symm _).symm
    _ = ∑ j : a.live, f' (e.symm j) * ∑ k : a.live,
          D0 j k * f' (e.symm k) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        calc ∑ j' : (a.restrictLive S).live, D0' (e.symm j) j' * f' j'
            = ∑ k : a.live, D0' (e.symm j) (e.symm k) * f' (e.symm k) :=
              (Equiv.sum_comp e.symm _).symm
          _ = ∑ k : a.live, D0 j k * f' (e.symm k) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [hD]
              simp only [Equiv.apply_symm_apply]

/-- The dual form agrees under pullback along the subtype equivalence. -/
theorem LiveState.restrictLive_state_X (S : Finset P) (a : LiveState P) (r : P → ℂ)
    (t : ℝ) (hsub : a.live ⊆ S) (y : (a.restrictLive S).live → ℝ) :
    ((a.restrictLive S).state (restrictDamping S r)).X t y =
      (a.state r).X t (fun j : a.live =>
        y ((subLiveEquiv S a hsub).symm j)) := by
  classical
  set e := subLiveEquiv S a hsub with he
  unfold State.X dualForm
  congr 1
  ext v
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨f', rfl⟩
    refine ⟨fun j : a.live => f' (e.symm j), ?_⟩
    have h1 : (∑ i' : (a.restrictLive S).live, y i' * f' i')
        = ∑ j : a.live, y (e.symm j) * f' (e.symm j) :=
      (Equiv.sum_comp e.symm _).symm
    have h2 : qform (((a.restrictLive S).state (restrictDamping S r)).D t) f'
        = qform ((a.state r).D t) (fun j : a.live => f' (e.symm j)) :=
      restrictLive_qform S a hsub _ _
        (fun x y' => restrictLive_state_D S a r t x y') f'
    rw [h1, h2]
  · rintro ⟨f, rfl⟩
    refine ⟨fun k : (a.restrictLive S).live => f (e k), ?_⟩
    have h1 : (∑ j : a.live, y (e.symm j) * f j)
        = ∑ i' : (a.restrictLive S).live, y i' * f (e i') := by
      rw [← Equiv.sum_comp e.symm (fun i' => y i' * f (e i'))]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Equiv.apply_symm_apply]
    have h2 : qform (((a.restrictLive S).state (restrictDamping S r)).D t)
        (fun k : (a.restrictLive S).live => f (e k))
        = qform ((a.state r).D t) f := by
      have hq := restrictLive_qform S a hsub
        (((a.restrictLive S).state (restrictDamping S r)).D t) ((a.state r).D t)
        (fun x y' => restrictLive_state_D S a r t x y') (fun k => f (e k))
      have hfe : (fun j : a.live => f (e (e.symm j))) = f := by
        funext j
        simp only [Equiv.apply_symm_apply]
      simp only [← he] at hq
      rw [hfe] at hq
      exact hq
    rw [h1, h2]

/-- Submatrix along the subtype equivalence is the identity on scalars. -/
theorem LiveState.subLive_submatrix_one (S : Finset P) (a : LiveState P)
    (hsub : a.live ⊆ S) :
    ((1 : CMat a.live).submatrix (subLiveEquiv S a hsub) (subLiveEquiv S a hsub)) = 1 := by
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.one_apply]
  by_cases hij : x = y
  · subst hij
    simp
  · have hne : (subLiveEquiv S a hsub) x ≠ (subLiveEquiv S a hsub) y :=
      fun h => hij ((subLiveEquiv S a hsub).injective h)
    simp [hij, hne]

/-- Submatrix along the subtype equivalence preserves units. -/
theorem LiveState.subLive_isUnit (S : Finset P) (a : LiveState P)
    (hsub : a.live ⊆ S) (M : CMat a.live) (hM : IsUnit M) :
    IsUnit (M.submatrix (subLiveEquiv S a hsub) (subLiveEquiv S a hsub)) := by
  obtain ⟨u, rfl⟩ := hM
  refine ⟨⟨((↑u : CMat a.live).submatrix (subLiveEquiv S a hsub) (subLiveEquiv S a hsub)),
    ((↑(u⁻¹) : CMat a.live).submatrix (subLiveEquiv S a hsub) (subLiveEquiv S a hsub)),
    ?_, ?_⟩, rfl⟩
  · rw [Matrix.submatrix_mul_equiv _ _ _ (subLiveEquiv S a hsub) _,
      Units.mul_inv, subLive_submatrix_one S a hsub]
  · rw [Matrix.submatrix_mul_equiv _ _ _ (subLiveEquiv S a hsub) _,
      Units.inv_mul, subLive_submatrix_one S a hsub]

/-- The Ward identity transports along the subtype equivalence. -/
theorem LiveState.restrictLive_state_ward (S : Finset P) (a : LiveState P) (r : P → ℂ)
    (t : ℝ) (hsub : a.live ⊆ S) (h : (a.state r).ward t) :
    (((a.restrictLive S).state (restrictDamping S r)).ward t) := by
  set e := subLiveEquiv S a hsub with he
  unfold State.ward at h ⊢
  have hg : (((a.restrictLive S).state (restrictDamping S r)).g) =
      (((a.state r).g).submatrix e e) := by
    ext x y
    exact restrictLive_state_g S a r x y
  have hh : (((a.restrictLive S).state (restrictDamping S r)).h t) =
      (((a.state r).h t).submatrix e e) := by
    ext x y
    exact restrictLive_state_h S a r t x y
  have hpdiag : diagonal (fun i => (((a.restrictLive S).state
      (restrictDamping S r)).p i : ℂ)) =
      ((diagonal (fun i => (((a.state r).p i : ℂ)))).submatrix e e) := by
    ext x y
    simp only [Matrix.diagonal_apply, Matrix.submatrix_apply]
    by_cases hij : x = y
    · subst hij
      rw [if_pos rfl, if_pos rfl]
      congr 1
    · have hne : e x ≠ e y := fun hh => hij (e.injective hh)
      rw [if_neg hij, if_neg hne]
  have hconj : ((((a.restrictLive S).state (restrictDamping S r)).h t)ᴴ) =
      ((((a.state r).h t)ᴴ).submatrix e e) := by
    rw [hh, Matrix.conjTranspose_submatrix]
  have hmIm : matrixIm (((a.restrictLive S).state (restrictDamping S r)).g) =
      ((matrixIm ((a.state r).g)).submatrix e e) := by
    rw [hg]
    ext x y
    simp only [matrixIm, Matrix.submatrix_apply]
  calc (((a.restrictLive S).state (restrictDamping S r)).h t) *
        diagonal (fun i => (((a.restrictLive S).state (restrictDamping S r)).p i : ℂ)) *
        ((((a.restrictLive S).state (restrictDamping S r)).h t)ᴴ)
      = ((((a.state r).h t) * diagonal (fun i => (((a.state r).p i : ℂ))) *
          (((a.state r).h t)ᴴ)).submatrix e e) := by
        rw [hconj, hh, hpdiag, Matrix.submatrix_mul_equiv _ _ e e e,
          Matrix.submatrix_mul_equiv _ _ e e e]
    _ = ((matrixIm ((a.state r).g)).submatrix e e) := by rw [h]
    _ = matrixIm (((a.restrictLive S).state (restrictDamping S r)).g) :=
        hmIm.symm

/-- The transformed lag agrees along the subtype equivalence. -/
theorem LiveState.restrictLive_lag (S : Finset P) (a : LiveState P) (r : P → ℂ)
    (t : ℝ) (hsub : a.live ⊆ S) (hU : IsUnit (1 - (a.state r).K t))
    (i : (a.restrictLive S).live) :
    (((a.restrictLive S).state (restrictDamping S r)).lag t i) =
      ((a.state r).lag t ((subLiveEquiv S a hsub) i)) := by
  set e := subLiveEquiv S a hsub with he
  have hKmat : ((((a.restrictLive S).state (restrictDamping S r)).K t)) =
      ((((a.state r).K t).submatrix e e)) := by
    ext x y
    exact restrictLive_state_K S a r t x y
  have h1K : (1 - (((a.restrictLive S).state (restrictDamping S r)).K t)) =
      (((1 - (a.state r).K t).submatrix e e)) := by
    have hsub2 : (((1 - (a.state r).K t).submatrix e e)) =
        (1 : CMat _).submatrix e e - (((a.state r).K t).submatrix e e) := by
      simp only [Matrix.submatrix_sub, Pi.sub_apply]
    rw [hsub2, subLive_submatrix_one S a hsub, hKmat]
  have hU' : IsUnit (1 - (((a.restrictLive S).state (restrictDamping S r)).K t)) := by
    rw [h1K]
    exact subLive_isUnit S a hsub _ hU
  have hraw : ((((a.restrictLive S).state (restrictDamping S r)).rawLag)) =
      (((a.state r).rawLag) ∘ e) := by
    funext x
    have hg_x : (((a.restrictLive S).state (restrictDamping S r)).g x x) =
        ((a.state r).g (e x) (e x)) := restrictLive_state_g S a r x x
    have hr_x : ((((a.restrictLive S).state (restrictDamping S r)).r x)) =
        (((a.state r).r (e x))) := restrictLive_state_r S a r x
    simp only [State.rawLag, Function.comp_apply, hg_x, hr_x]
  have hdet : IsUnit ((1 - (a.state r).K t).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp hU
  have hdet' : IsUnit ((1 - (((a.restrictLive S).state
      (restrictDamping S r)).K t)).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp hU'
  have hPlag : ((1 - (a.state r).K t) *ᵥ ((a.state r).lag t)) =
      (a.state r).rawLag := by
    have hlag : (a.state r).lag t =
        ((((1 - (a.state r).K t)⁻¹)) *ᵥ ((a.state r).rawLag)) := rfl
    rw [hlag, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
      Matrix.one_mulVec]
  have step2 : ((1 - (((a.restrictLive S).state (restrictDamping S r)).K t)) *ᵥ
      (((a.state r).lag t) ∘ e)) =
      (((a.restrictLive S).state (restrictDamping S r)).rawLag) := by
    rw [h1K, hraw]
    have hmv := Matrix.submatrix_mulVec_equiv (1 - (a.state r).K t)
      (((a.state r).lag t) ∘ e) e e
    rw [hmv]
    have hcomp : ((((a.state r).lag t) ∘ e) ∘ e.symm) = (a.state r).lag t := by
      funext j
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
    rw [hcomp, hPlag]
  have hclose : ((((a.state r).lag t) ∘ e)) =
      ((((a.restrictLive S).state (restrictDamping S r)).lag t)) := by
    have hlag' : (((a.restrictLive S).state (restrictDamping S r)).lag t) =
        (((1 - (((a.restrictLive S).state (restrictDamping S r)).K t))⁻¹) *ᵥ
          (((a.restrictLive S).state (restrictDamping S r)).rawLag)) := rfl
    rw [hlag', ← step2, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hdet', Matrix.one_mulVec]
  exact (congrFun hclose i).symm

/-- Ambient lags agree on the subtype. -/
theorem LiveState.restrictLive_ambientLag (S : Finset P) (a : LiveState P) (r : P → ℂ)
    (t : ℝ) (hsub : a.live ⊆ S) (hU : IsUnit (1 - (a.state r).K t))
    (p : {p // p ∈ S}) :
    (((a.restrictLive S).ambientLag t (restrictDamping S r)) p) =
      ((a.ambientLag t r) p.1) := by
  simp only [LiveState.ambientLag]
  by_cases hp : p ∈ (a.restrictLive S).live
  · have hpP : (p : P) ∈ a.live := (mem_restrictLive S a p).mp hp
    simp only [hp, hpP, if_true]
    exact restrictLive_lag S a r t hsub hU ⟨p, hp⟩
  · have hpP : (p : P) ∉ a.live := fun h => hp ((mem_restrictLive S a p).mpr h)
    simp [hp, hpP]

/-- The heat coefficient agrees on restricted ambient states. -/
theorem Sequence.gamma_restrictLive (q : Sequence P) (S : Finset P) (t : ℝ) (r : P → ℂ)
    (k : ℕ) (x : P) (hxS : x ∈ S) (ξ : ℝ) :
    gamma t (((q.restrictLive S).state k).ambient (restrictDamping S r)) ⟨x, hxS⟩ ξ =
      gamma t ((q.state k).ambient r) x ξ := by
  simp only [gamma, Sequence.restrictLive_state_eq]
  rw [show ((((q.state k).restrictLive S).ambient (restrictDamping S r)).r ⟨x, hxS⟩) =
      (((q.state k).ambient r).r x) from rfl,
    LiveState.restrictLive_ambient_g S (q.state k) r ⟨x, hxS⟩ ⟨x, hxS⟩]

/-- Ambient normalized inverses agree on the subtype. -/
theorem LiveState.ambient_h_restrictLive (S : Finset P) (a : LiveState P) (r : P → ℂ)
    (t : ℝ) (p q : {p // p ∈ S}) :
    (((a.restrictLive S).ambient (restrictDamping S r)).h t p q) =
      ((a.ambient r).h t p.1 q.1) := by
  have hg := LiveState.restrictLive_ambient_g S a r p q
  simp only [State.h, Matrix.smul_apply, hg]

/-- Ambient entrywise squares agree on the subtype. -/
theorem LiveState.ambient_K_restrictLive (S : Finset P) (a : LiveState P) (r : P → ℂ)
    (t : ℝ) (p q : {p // p ∈ S}) :
    (((a.restrictLive S).ambient (restrictDamping S r)).K t p q) =
      ((a.ambient r).K t p.1 q.1) := by
  have hh := LiveState.ambient_h_restrictLive S a r t p q
  simp only [State.K, AndersonAC.Blueprint.entrywiseSquare, hh]

/-- Ambient absolute squares agree on the subtype. -/
theorem LiveState.ambient_F_restrictLive (S : Finset P) (a : LiveState P) (r : P → ℂ)
    (t : ℝ) (p q : {p // p ∈ S}) :
    (((a.restrictLive S).ambient (restrictDamping S r)).F t p q) =
      ((a.ambient r).F t p.1 q.1) := by
  have hh := LiveState.ambient_h_restrictLive S a r t p q
  simp only [State.F, entryAbsSquare, hh]

/-- Ambient damping coordinates agree on the subtype. -/
theorem LiveState.ambient_p_restrictLive (S : Finset P) (a : LiveState P) (r : P → ℂ)
    (p : {p // p ∈ S}) :
    (((a.restrictLive S).ambient (restrictDamping S r)).p p) =
      ((a.ambient r).p p.1) := rfl

/-- Survivor membership corresponds across the restriction. -/
theorem Sequence.surv_mem_restrictLive (S : Finset P) (x : P) (hxS : x ∈ S)
    (p : {p // p ∈ S}) :
    p ∈ survivors ⟨x, hxS⟩ ↔ p.1 ∈ survivors x := by
  simp [survivors, Finset.mem_erase, Subtype.ext_iff]

/-- Applying a padded matrix at in-set indices (for restriction proofs). -/
theorem pad_mem_entry {α : Type*} [Zero α] (Sd : Finset P) (M : Matrix Sd Sd α)
    (i j : P) (hi : i ∈ Sd) (hj : j ∈ Sd) : pad Sd M i j = M ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [pad, hi, hj]

/-- Applying a padded matrix at an out-of-set row. -/
theorem pad_left_entry {α : Type*} [Zero α] (Sd : Finset P) (M : Matrix Sd Sd α)
    (i j : P) (hi : i ∉ Sd) : pad Sd M i j = 0 := by
  simp [pad, hi]

/-- Applying a padded matrix at an out-of-set column. -/
theorem pad_right_entry {α : Type*} [Zero α] (Sd : Finset P) (M : Matrix Sd Sd α)
    (i j : P) (hj : j ∉ Sd) : pad Sd M i j = 0 := by
  unfold pad
  split_ifs <;> rfl

/-- Coercion of an explicit subtype_mk reduces (for restriction normal forms). -/
theorem subtype_coe_mk {α : Type*} {p : α → Prop} (a : α) (h : p a) :
    ((⟨a, h⟩ : {x // p x}).1 : α) = a := rfl

/-- The `J` increment restricts entry-wise. -/
theorem Sequence.Jinc_restrictLive (q : Sequence P) (S : Finset P) (t : ℝ) (r : P → ℂ)
    (k : ℕ) (x : P) (hxS : x ∈ S) (ξ : ℝ) :
    restrict (Jinc t ((q.state k).ambient r) x ξ) S =
      Jinc t (((q.restrictLive S).state k).ambient (restrictDamping S r)) ⟨x, hxS⟩ ξ := by
  have hγ : gamma t ((((q.state k).restrictLive S).ambient (restrictDamping S r))) ⟨x, hxS⟩ ξ =
      gamma t ((q.state k).ambient r) x ξ :=
    Sequence.gamma_restrictLive q S t r k x hxS ξ
  ext a b
  by_cases hp : a.1 ∈ survivors x
  · have hp' : a ∈ survivors ⟨x, hxS⟩ := (surv_mem_restrictLive S x hxS a).mpr hp
    by_cases hq : b.1 ∈ survivors x
    · have hq' : b ∈ survivors ⟨x, hxS⟩ := (surv_mem_restrictLive S x hxS b).mpr hq
      have hh_px : State.h t (((q.state k).restrictLive S).ambient (restrictDamping S r)) a ⟨x, hxS⟩ =
          State.h t ((q.state k).ambient r) a.1 x :=
        LiveState.ambient_h_restrictLive S (q.state k) r t a ⟨x, hxS⟩
      have hh_pq := LiveState.ambient_h_restrictLive S (q.state k) r t a b
      have hh_xq : State.h t (((q.state k).restrictLive S).ambient (restrictDamping S r)) ⟨x, hxS⟩ b =
          State.h t ((q.state k).ambient r) x b.1 :=
        LiveState.ambient_h_restrictLive S (q.state k) r t ⟨x, hxS⟩ b
      have hK_px : State.K t (((q.state k).restrictLive S).ambient (restrictDamping S r)) a ⟨x, hxS⟩ =
          State.K t ((q.state k).ambient r) a.1 x :=
        LiveState.ambient_K_restrictLive S (q.state k) r t a ⟨x, hxS⟩
      have hK_xq : State.K t (((q.state k).restrictLive S).ambient (restrictDamping S r)) ⟨x, hxS⟩ b =
          State.K t ((q.state k).ambient r) x b.1 :=
        LiveState.ambient_K_restrictLive S (q.state k) r t ⟨x, hxS⟩ b
      have hKxx : State.K t (((q.state k).restrictLive S).ambient
          (restrictDamping S r)) ⟨x, hxS⟩ ⟨x, hxS⟩ =
          State.K t ((q.state k).ambient r) x x :=
        LiveState.ambient_K_restrictLive S (q.state k) r t ⟨x, hxS⟩ ⟨x, hxS⟩
      rw [Sequence.restrictLive_state_eq S q k]
      simp [restrict, Matrix.submatrix_apply, Jinc, pad, hp, hq, hp', hq',
        hγ, hh_px, hh_pq, hh_xq, hK_px, hK_xq, hKxx]
    · have hq' : b ∉ survivors ⟨x, hxS⟩ := fun h => hq ((surv_mem_restrictLive S x hxS b).mp h)
      simp [restrict, Matrix.submatrix_apply, Jinc, pad, hp, hq, hp', hq']
  · have hp' : a ∉ survivors ⟨x, hxS⟩ := fun h => hp ((surv_mem_restrictLive S x hxS a).mp h)
    simp [restrict, Matrix.submatrix_apply, Jinc, pad, hp, hp']

/-- Restricted `J` steps agree with the original steps. -/
theorem Sequence.restrictLive_stepJ (q : Sequence P) (S : Finset P) (t : ℝ) (r : P → ℂ)
    (hpiv : ∀ k < q.length, ∀ p, q.pivot k = some p → p ∈ S)
    (k : ℕ) (hk : k < q.length) :
    restrict (q.stepJ t r k) S =
      ((q.restrictLive S).stepJ t (restrictDamping S r) k) := by
  cases hq : q.pivot k with
  | none =>
      simp [Sequence.stepJ, hq, restrict]
  | some x =>
      have hxS : x ∈ S := hpiv k hk x hq
      have hqs : (q.restrictLive S).pivot k = some ⟨x, hxS⟩ := by
        simp [Sequence.restrictLive, hq, hxS]
      simp only [Sequence.stepJ, hq, hqs]
      rw [restrict_mask S _ _, Sequence.Jinc_restrictLive q S t r k x hxS _]
      rfl

/-- Restriction commutes with finite sums of matrices. -/
theorem restrict_sum (S : Finset P) (A : ℕ → CMat P) (K : Finset ℕ) :
    restrict (∑ k ∈ K, A k) S = ∑ k ∈ K, restrict (A k) S := by
  induction K using Finset.induction with
  | empty => simp [restrict]
  | insert a s h ih =>
      rw [Finset.sum_insert h, Finset.sum_insert h, ← ih]
      ext p q
      simp [restrict, Matrix.submatrix_apply, Pi.add_apply]

/-- Restricted `J` records agree with the original records. -/
theorem Sequence.Jrecord_restrictLive (q : Sequence P) (S : Finset P) (t : ℝ) (r : P → ℂ)
    (hpiv : ∀ k < q.length, ∀ p, q.pivot k = some p → p ∈ S)
    (K : Finset ℕ) (hK : K ⊆ Finset.range q.length) :
    restrict (q.Jrecord t r K) S =
      ((q.restrictLive S).Jrecord t (restrictDamping S r) K) := by
  simp only [Sequence.Jrecord]
  rw [restrict_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  exact Sequence.restrictLive_stepJ q S t r hpiv k
    (Finset.mem_range.mp (hK hk))

/-- Masked matrices vanish outside the mask set. -/
theorem mask_entry_zero' {α : Type*} [Zero α] (L : Finset P) (A : Matrix P P α)
    (i j : P) (hij : i ∉ L ∨ j ∉ L) : mask L A i j = 0 := by
  rcases hij with hi | hj
  · simp [mask, pad, hi]
  · simp [mask, pad, hj]

/-- `J` records vanish outside the initial live set (on in-range indices). -/
theorem Sequence.Jrecord_supported (q : Sequence P) (S : Finset P) (t : ℝ) (r : P → ℂ)
    (hseq : q.wellFormed t r) (hstart : (q.state 0).live = S)
    (K : Finset ℕ) (hK : K ⊆ Finset.range q.length) (i j : P) (hij : i ∉ S ∨ j ∉ S) :
    q.Jrecord t r K i j = 0 := by
  revert hK hij
  induction K using Finset.induction with
  | empty =>
      intro hK hij
      simp only [Sequence.Jrecord, Finset.sum_empty]
      rfl
  | insert a s h ih =>
      intro hK hij
      have ha : a < q.length := Finset.mem_range.mp (hK (Finset.mem_insert_self a s))
      have hs : s ⊆ Finset.range q.length :=
        fun x hx => hK (Finset.mem_insert_of_mem hx)
      have ih' := ih hs hij
      have hterm : q.stepJ t r a i j = 0 := by
        have hsub : (q.state (a + 1)).live ⊆ S :=
          Sequence.live_subset_initial q S hstart hseq (a + 1) (Nat.succ_le_of_lt ha)
        have hmem : i ∉ (q.state (a + 1)).live ∨ j ∉ (q.state (a + 1)).live := by
          rcases hij with hi | hj
          · exact Or.inl (fun hh => hi (hsub hh))
          · exact Or.inr (fun hh => hj (hsub hh))
        cases hpa : q.pivot a with
        | none =>
            have h0 : q.stepJ t r a = 0 := by simp [Sequence.stepJ, hpa]
            rw [h0]
            rfl
        | some x =>
            have h1 : q.stepJ t r a =
                mask ((q.state (a + 1)).live) (Jinc t ((q.state a).ambient r) x (q.scalar a)) := by
              simp [Sequence.stepJ, hpa]
            rw [h1]
            exact mask_entry_zero' _ _ i j hmem
      have hmat : q.Jrecord t r (insert a s) = q.stepJ t r a + q.Jrecord t r s := by
        simp [Sequence.Jrecord, Finset.sum_insert h]
      have hentry : (q.stepJ t r a + q.Jrecord t r s) i j =
          (q.stepJ t r a i j + q.Jrecord t r s i j) := rfl
      rw [hmat, hentry, hterm, ih', add_zero]

end AndersonAC.S45
