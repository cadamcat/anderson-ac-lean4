import AndersonAC.AgentS6.CapReduction

/-! The monitored region (06-clearing.tex:1064–1066, 1095–1100): sites within ordinary distance
`R` of the core lie in a ball of radius `t^{-C_loc} + R` around the core center, so their number
is at most `K (1 + t^{-C_loc} + R)^d`, independently of the torus volume. -/

noncomputable section
open MeasureTheory

namespace AndersonAC.AgentS6

open AndersonAC.S6

universe u

theorem monitored_card {Ω : Type u} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)}
    {t : ℝ} {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))} {q : StoppedTrial (Ω := Ω) core t r g0 order}
    {μ : Measure Ω} {d : ℕ} {c K Cloc : ℝ} {dist : Fin n → Fin n → ℝ}
    {collapsed : ℕ → Ω → Fin n → Fin n → ℝ} {ell : ℝ}
    (hin : TrialLocalInput q μ d c K Cloc dist collapsed ell) (R : ℝ) (hR : 0 ≤ R)
    (hcore : core.Nonempty) :
    ((Finset.univ.filter (fun i => distanceToCore dist core i ≤ R)).card : ℝ) ≤
      K * (1 + (t ^ (-Cloc) + R)) ^ d := by
  obtain ⟨center, hball⟩ := hin.core_ball
  have hsub : Finset.univ.filter (fun i => distanceToCore dist core i ≤ R) ⊆
      Finset.univ.filter (fun j => dist center j ≤ t ^ (-Cloc) + R) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    unfold distanceToCore at hi
    rw [dif_pos hcore] at hi
    obtain ⟨b, hb, hbeq⟩ := Finset.exists_mem_eq_inf' hcore (dist i)
    rw [hbeq] at hi
    have h1 := hin.dist_triangle center b i
    have h2 := hball b hb
    have h3 := hin.dist_symm i b
    linarith
  have hL : 0 ≤ t ^ (-Cloc) + R := by
    have : 0 ≤ t ^ (-Cloc) := by
      obtain ⟨b, hb⟩ := hcore
      exact le_trans (hin.dist_nonneg center b) (hball b hb)
    linarith
  calc ((Finset.univ.filter (fun i => distanceToCore dist core i ≤ R)).card : ℝ)
      ≤ ((Finset.univ.filter (fun j => dist center j ≤ t ^ (-Cloc) + R)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ K * (1 + (t ^ (-Cloc) + R)) ^ d := hin.volume center _ hL

end AndersonAC.AgentS6

#print axioms AndersonAC.AgentS6.monitored_card
