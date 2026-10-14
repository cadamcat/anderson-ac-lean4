import AndersonAC.S45.Definitions
import AndersonAC.S45.RestrictLive
import AndersonAC.S45.RestrictLiveEquiv

/-! Active-site transport for S45 sweep sequences.

Given a port type `initialPorts I` and an active set `active : Finset I`
(the committed endpoint's active sites), the stage-start live set is the
ports of the active sites:

`activeLive active = univ.filter (fun p => p.1 ∈ active)`.

This is exactly `(sweepStartLiveState θ x).live` for a run record `x`
(see `AgentS78.ResetBlock.sweepStartLiveState`; that file is not imported
here to keep this layer free of the construction imports).

For a sweep `q : Sequence (initialPorts I)` starting at `activeLive`
with well-formed bit-pivot steps, restriction to `activeLive` plus
reindexing along `activeEquiv` gives a sequence on
`initialPorts {i // i ∈ active}` starting at `univ`, with isomorphic
live states and entry-wise equal analytic data.  This is the (b) transport
the v3 TileGoodCore consumers (ordinary_sweep_endpoint, local_transfer via
`RestrictLiveTransfer`, cumulative_schur via `RestrictLiveSchur`,
prestate_of_prefix) apply after `Fintype.equivFin`.

This file depends only on the definition layer plus `RestrictLive` /
`RestrictLiveEquiv`; no `S45.Statements`, no norms.
-/

noncomputable section
open Matrix
namespace AndersonAC.S45

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The stage-start live set: ports of the active sites. -/
def activeLive (active : Finset I) : Finset (initialPorts I) :=
  Finset.univ.filter (fun p : initialPorts I => p.1 ∈ active)

@[simp] theorem mem_activeLive (active : Finset I) (p : initialPorts I) :
    p ∈ activeLive active ↔ p.1 ∈ active := by
  simp [activeLive]

/-- Ports in the restriction are exactly the active-site ports. -/
def activeEquiv (active : Finset I) :
    {p // p ∈ activeLive active} ≃ initialPorts {i // i ∈ active} where
  toFun p := (⟨p.1.1, (mem_activeLive active p.1).mp p.2⟩, p.1.2)
  invFun q := ⟨(q.1.1, q.2), (mem_activeLive active _).mpr q.1.2⟩
  left_inv p := by
    apply Subtype.ext
    show ((p.1.1, p.1.2)) = p.1
    exact (Prod.eta p.1).symm
  right_inv q := by
    show ((⟨q.1.1, _⟩, q.2)) = q
    exact (Prod.eta q).symm

@[simp] theorem activeEquiv_val (active : Finset I)
    (p : {p // p ∈ activeLive active}) :
    ((activeEquiv active p).1.1 : I) = (p.1.1 : I) := rfl

@[simp] theorem activeEquiv_snd (active : Finset I)
    (p : {p // p ∈ activeLive active}) :
    (activeEquiv active p).2 = p.1.2 := rfl

@[simp] theorem activeEquiv_symm_val (active : Finset I)
    (q : initialPorts {i // i ∈ active}) :
    (((activeEquiv active).symm q).1.1 : I) = (q.1.1 : I) := rfl

@[simp] theorem activeEquiv_symm_snd (active : Finset I)
    (q : initialPorts {i // i ∈ active}) :
    (((activeEquiv active).symm q).1.2 : Bool) = q.2 := rfl

/-- The active-site sequence: restrict to the stage-start live set, then
reindex to the active-site ports. -/
def Sequence.activeRestrict (q : Sequence (initialPorts I)) (active : Finset I) :
    Sequence (initialPorts {i // i ∈ active}) :=
  (q.restrictLive (activeLive active)).reindex (activeEquiv active)

@[simp] theorem Sequence.activeRestrict_length (q : Sequence (initialPorts I))
    (active : Finset I) : (q.activeRestrict active).length = q.length := rfl

@[simp] theorem Sequence.activeRestrict_scalar (q : Sequence (initialPorts I))
    (active : Finset I) (k : ℕ) :
    (q.activeRestrict active).scalar k = q.scalar k := rfl

theorem Sequence.activeRestrict_state_eq (q : Sequence (initialPorts I))
    (active : Finset I) (k : ℕ) :
    (q.activeRestrict active).state k =
      ((q.state k).restrictLive (activeLive active)).reindex
        (activeEquiv active) := rfl

/-- Pivots of a well-formed sequence starting at the active live set lie in
it (so restriction never drops a defined pivot). -/
theorem Sequence.pivots_mem_activeLive (q : Sequence (initialPorts I))
    (active : Finset I) (t : ℝ) (r : initialPorts I → ℂ)
    (hstart : (q.state 0).live = activeLive active)
    (hseq : q.wellFormed t r) :
    ∀ k < q.length, ∀ p, q.pivot k = some p → p ∈ activeLive active := by
  intro k hk p hp
  have hsub : (q.state k).live ⊆ activeLive active :=
    Sequence.live_subset_initial q (activeLive active) hstart hseq k
      (Nat.le_of_lt hk)
  have hstep := hseq.2 k hk
  have hrel : StepRel t r (q.state k) (q.state (k + 1)) p (q.scalar k) := by
    simpa [hp] using hstep
  exact hsub hrel.pivot_live

/-- Damping on the active-site ports pulled back from the Torus ports. -/
def activeDamping (active : Finset I) (r : initialPorts I → ℂ) :
    initialPorts {i // i ∈ active} → ℂ :=
  fun q => (restrictDamping (activeLive active) r) ((activeEquiv active).symm q)

/-- The pulled-back damping unfolds to the original damping at the
projected port. -/
theorem activeDamping_eq (active : Finset I) (r : initialPorts I → ℂ)
    (q : initialPorts {i // i ∈ active}) :
    activeDamping active r q = r ((q.1.1 : I), q.2) := rfl

/-- Well-formedness transports to the active-site sequence. -/
theorem Sequence.wellFormed_activeRestrict (q : Sequence (initialPorts I))
    (active : Finset I) (t : ℝ) (r : initialPorts I → ℂ)
    (hstart : (q.state 0).live = activeLive active)
    (hseq : q.wellFormed t r) :
    (q.activeRestrict active).wellFormed t (activeDamping active r) := by
  have hpiv := Sequence.pivots_mem_activeLive q active t r hstart hseq
  have hqS : (q.restrictLive (activeLive active)).wellFormed t
      (restrictDamping (activeLive active) r) :=
    Sequence.wellFormed_restrictLive q (activeLive active) hseq hpiv
  exact Sequence.wellFormed_reindex (activeEquiv active)
    (q.restrictLive (activeLive active)) t _ _ (fun _ => rfl) hqS

/-- The active-site sequence starts with every port live. -/
theorem Sequence.activeRestrict_start (q : Sequence (initialPorts I))
    (active : Finset I)
    (hstart : (q.state 0).live = activeLive active) :
    ((q.activeRestrict active).state 0).live = Finset.univ :=
  Sequence.reindex_start (activeEquiv active)
    (q.restrictLive (activeLive active))
    (Sequence.restrictLive_start q (activeLive active) hstart)

/-- Restricted pivots project to the original pivots. -/
theorem Sequence.activeRestrict_pivot_val (q : Sequence (initialPorts I))
    (active : Finset I) (t : ℝ) (r : initialPorts I → ℂ)
    (hstart : (q.state 0).live = activeLive active)
    (hseq : q.wellFormed t r) (k : ℕ) (hk : k < q.length) :
    ((((q.activeRestrict active).pivot k).map
      (fun p => (((activeEquiv active).symm p).1 : initialPorts I))) =
      q.pivot k) := by
  have hpiv := Sequence.pivots_mem_activeLive q active t r hstart hseq
  have h1 := Sequence.restrictLive_pivot_val (activeLive active) q hpiv k hk
  cases hq : q.pivot k with
  | none =>
      simp [Sequence.activeRestrict, Sequence.reindex, Sequence.restrictLive, hq]
  | some p =>
      have hp : p ∈ activeLive active := hpiv k hk p hq
      have hr : (q.restrictLive (activeLive active)).pivot k = some ⟨p, hp⟩ := by
        simp only [Sequence.restrictLive, hq, dite_eq_left hp]
      simp only [Sequence.activeRestrict, Sequence.reindex, hr, Option.map_some]
      have h2 : (activeEquiv active).symm ((activeEquiv active) ⟨p, hp⟩) =
          ⟨p, hp⟩ :=
        Equiv.symm_apply_apply _ _
      rw [h2]

/-- Live ports of the active restriction correspond to live ports upstairs. -/
def Sequence.activeLiveEquiv (q : Sequence (initialPorts I)) (active : Finset I)
    (k : ℕ) (hsub : (q.state k).live ⊆ activeLive active) :
    ((q.activeRestrict active).state k).live ≃ (q.state k).live :=
  (LiveState.reindexEquiv (activeEquiv active)
    ((q.state k).restrictLive (activeLive active))).trans
    (LiveState.subLiveEquiv (activeLive active) (q.state k) hsub)

/-- The live-subset hypothesis needed above follows from the start. -/
theorem Sequence.activeLive_subset (q : Sequence (initialPorts I))
    (active : Finset I) (t : ℝ) (r : initialPorts I → ℂ)
    (hstart : (q.state 0).live = activeLive active)
    (hseq : q.wellFormed t r) (k : ℕ) (hk : k ≤ q.length) :
    (q.state k).live ⊆ activeLive active :=
  Sequence.live_subset_initial q (activeLive active) hstart hseq k hk

/-- The active restriction's ambient matrix is the original matrix at the
projected ports (LiveState level). -/
theorem Sequence.activeRestrict_g (q : Sequence (initialPorts I))
    (active : Finset I) (k : ℕ)
    (p q' : initialPorts {i // i ∈ active}) :
    ((q.activeRestrict active).state k).g p q' =
      (q.state k).g ((p.1.1 : I), p.2) ((q'.1.1 : I), q'.2) := rfl

/-- The active state's matrix entries agree with the original ones along the
live equivalence. -/
theorem Sequence.activeRestrict_state_g (q : Sequence (initialPorts I))
    (active : Finset I) (r : initialPorts I → ℂ) (k : ℕ)
    (hsub : (q.state k).live ⊆ activeLive active)
    (i j : ((q.activeRestrict active).state k).live) :
    (((q.activeRestrict active).state k).state
      (activeDamping active r)).g i j =
      ((q.state k).state r).g ((q.activeLiveEquiv active k hsub) i)
        ((q.activeLiveEquiv active k hsub) j) := rfl

/-- Symmetry is preserved by the active restriction. -/
theorem Sequence.activeRestrict_state_symm (q : Sequence (initialPorts I))
    (active : Finset I) (r : initialPorts I → ℂ) (k : ℕ)
    (h : ((q.state k).state r).g.IsSymm) :
    ((((q.activeRestrict active).state k).state
      (activeDamping active r)).g.IsSymm) := by
  have hR := LiveState.restrictLive_state_symm (activeLive active) (q.state k) r h
  exact LiveState.reindex_state_symm (activeEquiv active)
    ((q.state k).restrictLive (activeLive active))
    (restrictDamping (activeLive active) r) (activeDamping active r) hR

end AndersonAC.S45
