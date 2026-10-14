import AndersonAC.S78.Definitions

set_option autoImplicit false

namespace AndersonAC.SolS78

/-- A pending state persists back to any stage no earlier than its latest label.
The induction parameter is the gap between the requested and current stages. -/
theorem pending_persistence_proof (pending : ℕ → Prop) (latest : ℕ → ℕ)
    (hstep : ∀ n, pending (n + 1) →
      (pending n ∧ latest (n + 1) = latest n) ∨ latest (n + 1) = n + 1)
    (hstamp : ∀ n, pending n → latest n ≤ n) (r j : ℕ)
    (hrj : r ≤ j) (hp : pending j) (hl : latest j ≤ r) : pending r := by
  have hgap : j = r + (j - r) := by omega
  have haux : ∀ k j, j = r + k → pending j → latest j ≤ r → pending r := by
    intro k
    induction k with
    | zero =>
        intro j hj hpj _
        have hjr : j = r := by omega
        simpa [hjr] using hpj
    | succ k ih =>
        intro j hj hpj hlj
        have hj' : j = (r + k) + 1 := by omega
        have hcurrent : pending ((r + k) + 1) := by simpa [hj'] using hpj
        rcases hstep (r + k) hcurrent with ⟨hprev, hkeep⟩ | hnew
        · have hprevLabel : latest (r + k) ≤ r := by
            calc
              latest (r + k) = latest ((r + k) + 1) := hkeep.symm
              _ = latest j := by rw [hj']
              _ ≤ r := hlj
          exact ih (r + k) (by simp) hprev hprevLabel
        · have hle : (r + k) + 1 ≤ r := by
            calc
              (r + k) + 1 = latest ((r + k) + 1) := hnew.symm
              _ = latest j := by rw [hj']
              _ ≤ r := hlj
          omega
  exact haux (j - r) j hgap hp hl

end AndersonAC.SolS78
