import AndersonAC.S78Metric.SegBound

open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78

/-- Adding uniformly bounded, separated terminal groups degrades the old
distance estimate by a factor independent of the number of groups. -/
theorem assembly_metric_proof {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (G : SimpleGraph ι) (hconn : G.Connected) (T : Finset ι) (O : κ → Finset ι)
    (c μ R ℓ : ℝ) (M : ℕ) (hc : 0 < c) (hμ : 0 ≤ μ)
    (hold : ∀ u v, c * (G.dist u v : ℝ) - μ ≤ terminalDistance G T u v)
    (hsize : ∀ a, (O a).card ≤ M)
    (hsep : ∀ a a', a ≠ a' → ∀ u ∈ O a, ∀ v ∈ O a', R - 2 * ℓ ≤ (G.dist u v : ℝ))
    (hmargin : 2 * (M : ℝ) < c * (R - 2 * ℓ) - μ) :
    ∀ u v, c * (1 - 2 * (M : ℝ) / (c * (R - 2 * ℓ) - μ)) * (G.dist u v : ℝ) - μ - 2 * (M : ℝ) ≤
      terminalDistance G (T ∪ Finset.univ.biUnion O) u v := by
  classical
  intro u v
  let S : Set ℕ := {n | ∃ xs : List ι, xs.IsChain G.Adj ∧ xs.head? = some u ∧
    xs.getLast? = some v ∧ pathCost (T ∪ newTerms O) xs = n}
  have hS : S.Nonempty := by
    obtain ⟨xs, hchain, hhead, hlast⟩ := exists_chain_of_connected hconn u v
    exact ⟨_, xs, hchain, hhead, hlast, rfl⟩
  obtain ⟨xs, hchain, hhead, hlast, hmin⟩ := csInf_mem hS
  obtain ⟨ys, hychain, hyhead, hylast, hynd, _, hycost⟩ :=
    exists_nodup_subchain (T ∪ newTerms O) G u v xs hchain hhead hlast
  let A : ℝ := pathCost T ys
  let B : ℝ := pathCost (T ∪ newTerms O) ys
  let k : ℕ := (hitSet O ys).card
  let L : ℝ := c * (R - 2 * ℓ) - μ
  let q : ℝ := 2 * (M : ℝ) / L
  have hL : 0 < L := sepL_pos hmargin
  have hq : 0 ≤ q := div_nonneg (by positivity) (le_of_lt hL)
  have hq1 : q < 1 := (div_lt_one hL).mpr hmargin
  have hqL : q * L = 2 * (M : ℝ) := div_mul_cancel₀ _ (ne_of_gt hL)
  have hA : c * (G.dist u v : ℝ) - μ ≤ A :=
    oldCost_ge_of_hold T c μ hold hychain hyhead hylast
  have hsave : A ≤ B + 2 * (M : ℝ) * (k : ℝ) := by
    have hs := saving_le T (newTerms O) ys
    have hcount := dcount_le_hit_mul O M hsize ys hynd
    have hnat : pathCost T ys ≤ pathCost (T ∪ newTerms O) ys +
        2 * ((hitSet O ys).card * M) := by
      change dcount (newTerms O) ys ≤ (hitSet O ys).card * M at hcount
      omega
    have hreal := Nat.cast_le (α := ℝ).mpr hnat
    push_cast at hreal
    dsimp [A, B, k]
    nlinarith only [hreal]
  have hB : c * (1 - q) * (G.dist u v : ℝ) - μ - 2 * (M : ℝ) ≤ B := by
    by_cases hk : k = 0
    · have hsave0 : A ≤ B := by simpa [hk] using hsave
      have hd : 0 ≤ (G.dist u v : ℝ) := by positivity
      have hdrop : 0 ≤ c * q * (G.dist u v : ℝ) := by positivity
      have hM : 0 ≤ (M : ℝ) := by positivity
      nlinarith only [hA, hsave0, hdrop, hM]
    · have hkpos : 1 ≤ k := by omega
      have hseg : ((k - 1 : ℕ) : ℝ) * L ≤ A :=
        seg_lower_bound T O hc hμ hold hsep hmargin ys hychain
      rw [Nat.cast_sub hkpos, Nat.cast_one] at hseg
      have hscaled := mul_le_mul_of_nonneg_left hseg hq
      have heq : q * (((k : ℝ) - 1) * L) =
          2 * (M : ℝ) * (k : ℝ) - 2 * (M : ℝ) := by
        calc q * (((k : ℝ) - 1) * L) = (q * L) * ((k : ℝ) - 1) := by ring
          _ = _ := by rw [hqL]; ring
      rw [heq] at hscaled
      have hBA : (1 - q) * A - 2 * (M : ℝ) ≤ B := by
        nlinarith only [hsave, hscaled]
      have hscaledA := mul_le_mul_of_nonneg_left hA (le_of_lt (sub_pos.mpr hq1))
      have hqμ := mul_nonneg hq hμ
      nlinarith only [hBA, hscaledA, hqμ]
  have hBmin : B ≤ ((sInf S : ℕ) : ℝ) := by
    dsimp [B]
    apply Nat.cast_le.mpr
    exact hycost.trans (le_of_eq hmin)
  change c * (1 - q) * (G.dist u v : ℝ) - μ - 2 * (M : ℝ) ≤ ((sInf S : ℕ) : ℝ)
  exact hB.trans hBmin

end AndersonAC.SolS78
