import AndersonAC.AgentS78.Construction.Freshness
import AndersonAC.AgentS78.Construction.Record

/-!
# the declared-fresh true signs of a committed record

02-state.tex:96–103: at a coupled site (active, not pending) the installed partial value is
the true revealed prefix and no digit of its remaining suffix has been queried. The record
declares exactly these true signs fresh (`declaredFresh`), and nothing once aborted (no
trial follows an abort, so a failure that aborts need not mark); auxiliary signs and orders are
handled by the per-block index sets (`fresh_of_declared_aux`). `declaredFresh_mono`: the
declared set shrinks when the active set shrinks, pending marks are added and prefix lengths
grow, which is what every block does (02-state.tex:107–113). Terminal sites (exact value
installed: clearing DONE, and the final residual sweep, whose `trueSuffix` query reveals the
whole suffix, 05:353–359) are excluded (05:343: terminal slots are skipped).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (SignIndex)

variable {d m : ℕ}

/-- True signs declared unqueried by a committed record: the suffixes, from the prefix
length, of the sites that are neither pending nor terminal. (Active and terminal sites
partition the committed sites, 02-state.tex:107–113, so these are the coupled sites; the
definition does not mention the active set, so that the sweep end, which recomputes the active
set from the live reserve ports, keeps the declared set.) -/
def declaredFresh (x : RunRecord d m) : Set (SignIndex (Torus d m)) :=
  {z | x.aborted = false ∧
    ∃ i k, z = Sum.inl (i, k) ∧ i ∉ x.pending ∧ i ∉ x.terminal ∧ x.prefixLength i ≤ k}

theorem declaredFresh_mono (x x' : RunRecord d m)
    (habort : x'.aborted = false → x.aborted = false)
    (hcoupled : x'.aborted = false → ∀ i, i ∉ x'.pending → i ∉ x'.terminal →
      i ∉ x.pending ∧ i ∉ x.terminal ∧ x.prefixLength i ≤ x'.prefixLength i) :
    declaredFresh x' ⊆ declaredFresh x := by
  rintro z ⟨hab, i, k, rfl, hp, ht, hk⟩
  obtain ⟨hp', ht', hle⟩ := hcoupled hab i hp ht
  exact ⟨habort hab, i, k, rfl, hp', ht', hle.trans hk⟩

/-- An aborted record declares nothing fresh (no trial follows an abort). -/
theorem declaredFresh_aborted (x : RunRecord d m) (h : x.aborted = true) :
    declaredFresh x = ∅ := by
  ext z; simp [declaredFresh, h]

end AndersonAC.AgentS78
