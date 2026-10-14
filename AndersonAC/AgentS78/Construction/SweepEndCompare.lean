import AndersonAC.AgentS78.PostSweep
import AndersonAC.AgentS78.Construction.StagePhase
import AndersonAC.AgentS78.Construction.TorusMetric

/-!
# The initial comparison of the post-sweep endpoint

agent-s78send (2026-10-14). `ClearPhaseData.ofSweep'`'s `initialComparison` at the sweep end
(07-assembly.tex:970–1000): from the stage comparators of the old endpoint at `t_{j−1}`
(`StageBounds`, `b' = t_{n₀} t_{j−1}`) and the affine mixture of `SweepFacts` (Proposition 4.9),
the post-sweep inverse form is comparable to `|y|² + θ b' Λ⁺` (`post_sweep_wstar`), hence the
post-sweep energy has constant kernel (`constantKernel_of_dual_lower`) and is comparable to the
spatial energy at `b = θ b' = t_{n₀} t_j` (`initial_comparison`).
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

theorem spatialEnergy_nonneg' (G : SimpleGraph (Torus d m))
    (A : Finset (Torus d m)) (b : ℝ) (hb : 0 < b) (f : Torus d m → ℝ) :
    0 ≤ spatialEnergy G A b f := by
  classical
  unfold spatialEnergy
  apply Real.sInf_nonneg
  rintro e ⟨α, v, -, rfl⟩
  have hg : 0 ≤ gradientEnergy G v := by
    unfold gradientEnergy
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_)
    split_ifs <;> positivity
  have := inv_nonneg.mpr hb.le
  have h2 : 0 ≤ ∑ i ∈ A, α i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  positivity

theorem active_nonempty_of_count (s : Endpoint (Torus d m))
    (hcount : Fintype.card (Torus d m) ≤ 2 * s.active.card) : s.active.Nonempty := by
  haveI : Nonempty (Torus d m) := (torusConnected_proof d m).nonempty
  have hpos : 0 < Fintype.card (Torus d m) := Fintype.card_pos
  exact Finset.card_pos.mp (by omega)

/-- **Initial comparison of the post-sweep endpoint.** -/
theorem sweep_initialComparison {n₀ j : ℕ} {u cP CP cL CL C₀ Cb : ℝ} (hm : 0 < m)
    (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hcP : 0 < cP) (hcL : 0 < cL) (hCL : 0 ≤ CL)
    (hC₀ : 0 ≤ C₀) (old sw : Endpoint (Torus d m)) (r : Torus d m → ℂ)
    (hSB : StageBounds d m n₀ (j - 1) u cP CP cL CL C₀ old r)
    (hsw : SweepFacts Cb (stageScale u (j - 1) m) (stageScale u j m) old sw r)
    (hDs : IsDampedEndpoint sw r (stageScale u j m))
    (hθ1 : 1 / 4 ≤ stageScale u j m / stageScale u (j - 1) m)
    (hθ2 : stageScale u j m / stageScale u (j - 1) m ≤ 5 / 8)
    (hε0 : 0 ≤ Cb * stageScale u (j - 1) m ^ (0.10 * delta))
    (hε : Cb * stageScale u (j - 1) m ^ (0.10 * delta) ≤ 1 / 2) :
    ∀ f, (3 / 2 * max (C₀ + 1 / cP ^ 2) CL)⁻¹ *
        spatialEnergy (nnGraph d m) sw.active (stageScale u n₀ m * stageScale u j m) f ≤
        endpointEnergy sw r (stageScale u j m) f ∧
      endpointEnergy sw r (stageScale u j m) f ≤
        (min cL (3 / (8 * CP ^ 2)) / 2)⁻¹ *
          spatialEnergy (nnGraph d m) sw.active (stageScale u n₀ m * stageScale u j m) f := by
  classical
  set t := stageScale u (j - 1) m with ht_def
  set t' := stageScale u j m with ht'_def
  set θ := t' / t with hθ_def
  have ht : 0 < t := stageScale_pos' hu _ m
  have ht' : 0 < t' := stageScale_pos' hu _ m
  have hs0 : 0 < stageScale u n₀ m := stageScale_pos' hu n₀ m
  have hb' : 0 < stageScale u n₀ m * t := mul_pos hs0 ht
  have hθb : θ * (stageScale u n₀ m * t) = stageScale u n₀ m * t' := by
    rw [hθ_def]; field_simp
  unfold StageBounds at hSB
  dsimp only at hSB
  obtain ⟨hdiag, -, -, -, hcount, -, hcomp⟩ := hSB
  have hact := hsw.active
  have hne : sw.active.Nonempty := by
    rw [hact]; exact active_nonempty_of_count old hcount
  have hCP : 0 < CP := by
    obtain ⟨i, hi⟩ := hne
    rw [hact] at hi
    exact hcP.trans_le ((hdiag i hi).2.1.trans (hdiag i hi).2.2.1)
  have hΛ0 : ∀ y, 0 ≤ inverseEnergy Finset.univ (gradientEnergy (nnGraph d m)) y := fun y =>
    inverseEnergy_nonneg_zero _ _ (by simp [gradientEnergy]) y
  set cc := min cL (3 / (8 * CP ^ 2)) / 2 with hcc
  set CC := 3 / 2 * max (C₀ + 1 / cP ^ 2) CL with hCC
  have hcc0 : 0 < cc := by
    have : 0 < min cL (3 / (8 * CP ^ 2)) := lt_min hcL (by positivity)
    rw [hcc]; linarith
  have hCC0 : 0 < CC := by
    have : 0 < max (C₀ + 1 / cP ^ 2) CL :=
      lt_of_lt_of_le (by positivity) (le_max_left _ _)
    rw [hCC]; positivity
  have hW : ∀ y, neutral sw.active y →
      cc * ((∑ i ∈ sw.active, y i ^ 2) + (stageScale u n₀ m * t') *
          inverseEnergy Finset.univ (gradientEnergy (nnGraph d m)) y) ≤
        inverseEnergy sw.active (endpointEnergy sw r t') y ∧
      inverseEnergy sw.active (endpointEnergy sw r t') y ≤
        CC * ((∑ i ∈ sw.active, y i ^ 2) + (stageScale u n₀ m * t') *
          inverseEnergy Finset.univ (gradientEnergy (nnGraph d m)) y) := by
    intro y hy
    have hy' : neutral old.active y := by rwa [← hact]
    obtain ⟨c1, c2, -⟩ := hcomp y hy'
    have haff := hsw.affine y hy'
    unfold stageTarget at haff
    have H := post_sweep_wstar old.active (Xof old r t) (Xof sw r t')
      (inverseEnergy Finset.univ (gradientEnergy (nnGraph d m))) (fun i => (r i).im) y θ
      (Cb * t ^ (0.10 * delta)) (stageScale u n₀ m * t) cP CP cL CL C₀ hθ1 hθ2 hε0 hε hb'.le
      (hΛ0 y) hcP hcL hCL hC₀ (fun i hi => ⟨(hdiag i hi).2.1, (hdiag i hi).2.2.1⟩) c1 c2 haff
    rw [hθb, ← hact] at H
    exact H
  have hp : ∀ i ∈ sw.active, 0 ≤ (r i).im := fun i hi => by
    rw [hact] at hi; exact hcP.le.trans (hdiag i hi).2.1
  have hker : constantKernel sw.active (endpointEnergy sw r t') := by
    refine constantKernel_of_dual_lower sw.active (fun i => (r i).im) (normalizedInverse sw t')
      (fun y => (∑ i ∈ sw.active, y i ^ 2) + (stageScale u n₀ m * t') *
        inverseEnergy Finset.univ (gradientEnergy (nnGraph d m)) y) cc hcc0 (fun y _ => ?_)
      (fun y hy => (hW y hy).1)
    have := mul_nonneg (mul_pos hs0 ht').le (hΛ0 y)
    linarith
  exact initial_comparison hm sw r t' ht' hDs hne hp hker _ cc CC (mul_pos hs0 ht') hcc0 hCC0 hW

end AndersonAC.AgentS78
