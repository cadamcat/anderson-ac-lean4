import AndersonAC.AgentS78.Construction.StagePhase
import AndersonAC.AgentS78.Construction.StagePhaseRows
import AndersonAC.S78.Statements

/-!
# the stage operation turns the clearing-phase invariant into the next
# stage boundary

`stage_end_core` (07-assembly.tex:1012–1030, proof of Proposition 7.5; Proposition 7.4 on the
active block): if the committed record `x` of stage `j` carries `ClearPhaseData` and `ζ` is a
solution of the diagonal reset equation on the active block in the ball of radius
`t_j^{.35δ}`, then the reset endpoint `resetEndpoint x.endpoint x.r ζ t_j` with damping
`x.r + ζ` ends a stage history up to `j` (`BoundaryHist … j`). Inputs used:

* `S78.committed_assembly` (unconditional) at the last committed state;
* `SolS78.reset_variation_proof` (row, kernel and form changes of a reset fixed point) with
  `Blueprint.Packages.ward`;
* `reset_step` (ResetJoin.lean) for the reset half of the `StageStep`;
* `BoundaryHist.extend`.

The constants: `Cmin` depends only on `d, CA, cA, PA`; the scale threshold `t₀` only on these
and on the stage-history constant `C ≥ Cmin` (uniform in `m, n₀, j, u, E`).
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- The reset endpoint is damped at the reset damping. -/
theorem resetEndpoint_damped {d m : ℕ} (s : Endpoint (Torus d m)) (r : Torus d m → ℂ)
    (ζ : s.active → ℂ) (t c : ℝ)
    (hM : ∀ i j, s.M i j = s.M j i ∧ (s.M i j).im = 0) (ht : 0 < t) (hc : 0 < c)
    (hr : ∀ a : s.active, c ≤ (((fun b : s.active => r b.val) + ζ) a).im) :
    IsDampedEndpoint (resetEndpoint s r ζ t) (r + padV s.active ζ) t := by
  classical
  refine ⟨hM, ?_, ?_⟩
  · intro i j h
    show padM s.active _ i j = 0
    rcases h with h | h
    · exact padM_support s.active _ i j (Or.inl fun a ha => h (ha ▸ a.property))
    · exact padM_support s.active _ i j (Or.inr fun a ha => h (ha ▸ a.property))
  · set MA := s.M.submatrix (fun a : s.active => a.val) (fun a : s.active => a.val) with hMA
    set rr : s.active → ℂ := (fun a : s.active => r a.val) + ζ with hrr
    have hdiag : (fun a : s.active => (r + padV s.active ζ) a.val) = rr := by
      funext a; simp [padV, a.property, rr]
    have hMh : MA.IsHermitian :=
      AndersonAC.SolS78.real_symmetric_hermitian MA (fun a b => hM a.val b.val)
    have hu := AndersonAC.SolS78.damped_isUnit MA rr t c hMh ht hc hr
    show (MA - (t : ℂ) • Matrix.diagonal (fun a : s.active => (r + padV s.active ζ) a.val)) *
        (padM s.active (resetInverse MA rr t)).submatrix (fun a : s.active => a.val)
          (fun a : s.active => a.val) = 1 ∧
      (padM s.active (resetInverse MA rr t)).submatrix (fun a : s.active => a.val)
          (fun a : s.active => a.val) *
        (MA - (t : ℂ) • Matrix.diagonal (fun a : s.active => (r + padV s.active ζ) a.val)) = 1
    rw [hdiag, padM_submatrix]
    exact ⟨Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu⟩

/-- A form comparable to a nonnegative form with a constant kernel has the same kernel. -/
theorem constantKernel_of_compare {ι : Type} (A : Finset ι) (D D' : (ι → ℝ) → ℝ) (ε : ℝ)
    (hε : ε < 1) (hD : ∀ f, 0 ≤ D f)
    (hcmp : ∀ f, (1 - ε) * D f ≤ D' f ∧ D' f ≤ (1 + ε) * D f) (hk : constantKernel A D) :
    constantKernel A D' := by
  intro f
  rw [← hk f]
  obtain ⟨h1, h2⟩ := hcmp f
  have h0 := hD f
  constructor
  · intro h
    rw [h] at h1
    nlinarith
  · intro h
    rw [h] at h1 h2
    linarith

set_option maxHeartbeats 1000000 in
/-- **The stage operation on the clearing-phase invariant** (abstract reset correction). -/
theorem stage_end_core {d : ℕ} (hd : 3 ≤ d) (CA cA PA : ℝ) (hCA : 1 ≤ CA) (hcA : 0 < cA)
    (hPA : 0 ≤ PA) :
    ∃ Cmin : ℝ, 1 ≤ Cmin ∧ ∀ C : ℝ, Cmin ≤ C → ∃ t₀ : ℝ, 0 < t₀ ∧
    ∀ {m : ℕ} (n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (j : ℕ) (x : RunRecord d m)
      (D : ClearPhaseData n₀ u E ρ C CA cA PA j x),
      u ∈ Set.Ioc (1 / 4 : ℝ) 1 → n₀ < j → stageScale u (j - 1) m < t₀ →
      ∀ ζ : x.endpoint.active → ℂ, ‖ζ‖ ≤ stageScale u j m ^ (0.35 * delta) →
      (∀ a, resetInverse (x.endpoint.M.submatrix (fun b : x.endpoint.active => b.val)
          (fun b : x.endpoint.active => b.val)) ((fun b : x.endpoint.active => x.r b.val) + ζ)
          (stageScale u j m) a a = ((fun b : x.endpoint.active => x.r b.val) + ζ) a) →
      BoundaryHist n₀ u E ρ C j (resetEndpoint x.endpoint x.r ζ (stageScale u j m))
        (x.r + padV x.endpoint.active ζ) := by
  obtain ⟨C', tA, hC', htA, hCAss⟩ := committed_assembly d hd CA cA PA hCA hcA hPA
  obtain ⟨Cr, a₀, hCr, ha₀, hvar⟩ := AndersonAC.SolS78.reset_variation_proof
    AndersonAC.Blueprint.Packages.ward cA (CA + 1) hcA (by linarith)
  refine ⟨max 1 Cr, le_max_left _ _, fun C hC => ?_⟩
  have hC1 : 1 ≤ C := (le_max_left _ _).trans hC
  have hCrC : Cr ≤ C := (le_max_right _ _).trans hC
  have hδ : (0 : ℝ) < delta := by norm_num [delta]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdν : (d : ℝ) * nu d = delta / 100000 := by
    unfold nu; field_simp
  have he1 : 0 < 0.42 * delta - (d : ℝ) * nu d := by rw [hdν]; norm_num [delta]
  obtain ⟨t1, ht1, hs1⟩ := AndersonAC.SolS78.reset_radius_small _ (1 / C') he1 (by positivity)
  obtain ⟨t2, ht2, hs2⟩ := AndersonAC.SolS78.reset_radius_small (0.35 * delta) a₀
    (by positivity) ha₀
  obtain ⟨t3, ht3, hs3⟩ := AndersonAC.SolS78.reset_radius_small (0.35 * delta) (1 / (2 * C))
    (by positivity) (by positivity)
  obtain ⟨t4, ht4, hs4⟩ := AndersonAC.SolS78.reset_radius_small (0.10 * delta) (1 / (20 * Cr))
    (by positivity) (by positivity)
  refine ⟨min (min tA 1) (min (min t1 t2) (min t3 t4)), by positivity, ?_⟩
  intro m n₀ u E ρ j x D hu hj ht ζ hζ hfix
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hk : n₀ ≤ j := by omega
  simp only [add_tsub_cancel_right] at ht
  set t := stageScale u j m with htdef
  set t' := stageScale u (j + 1) m with ht'def
  obtain ⟨old, rOld, k, I, hist, sweep, hlast, hfrozen, hIC, hIc, hIP⟩ := D
  subst hfrozen
  simp only [add_tsub_cancel_right] at hist sweep
  have ht'pos : 0 < t' := stageScale_pos' hu _ _
  have htt' : t' ≤ t := stageScale_anti hu m (Nat.le_succ j)
  have ht'0 : t' < min (min tA 1) (min (min t1 t2) (min t3 t4)) := htt'.trans_lt ht
  have ht'A : t' < tA := ht'0.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have ht'1 : t' < t1 := ht'0.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have ht'2 : t' < t2 := ht'0.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have ht'3 : t' < t3 := ht'0.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have ht'4 : t' < t4 := ht'0.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  have hs1' : C' * t' ^ (0.42 * delta - (d : ℝ) * nu d) ≤ 1 := by
    have := hs1 t' ht'pos ht'1
    rw [le_div_iff₀ hC'] at this; linarith
  have hs2' := hs2 t' ht'pos ht'2
  have hs3' : C * t' ^ (0.35 * delta) ≤ 1 / 2 := by
    have := hs3 t' ht'pos ht'3
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hs4' : Cr * t' ^ (0.10 * delta) ≤ 1 / 20 := by
    have := hs4 t' ht'pos ht'4
    rw [le_div_iff₀ (by positivity)] at this; linarith
  -- committed assembly at the last committed state
  have hCa := hCAss m k t' (stageScale u n₀ m * t') x.r I hIC hIc hIP ht'A (Fin.last k)
  rw [hlast] at hCa
  obtain ⟨hKfin, hlag, hrow, hker, -, hinv⟩ := hCa
  have hD : IsDampedEndpoint x.endpoint x.r t' := hlast ▸ I.physical (Fin.last k)
  set MA := x.endpoint.M.submatrix (fun a : x.endpoint.active => a.val) (fun a : x.endpoint.active => a.val) with hMA
  set rA : x.endpoint.active → ℂ := fun a => x.r a.val with hrA
  have hfg := g_eq_padM_resetInverse x.endpoint x.r t' hD
  have hcount : Fintype.card (Torus d m) ≤ 2 * x.endpoint.active.card := by
    have := I.activeCount (Fin.last k); rw [hlast] at this; exact this
  haveI hne : Nonempty x.endpoint.active := by
    have hpos : 0 < Fintype.card (Torus d m) := Fintype.card_pos_iff.mpr ⟨0⟩
    have : 0 < x.endpoint.active.card := by omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp this
    exact ⟨⟨a, ha⟩⟩
  have hMAs : ∀ a b, MA a b = MA b a ∧ (MA a b).im = 0 := fun a b => hD.1 a.val b.val
  have hdampI : ∀ i, cA ≤ (x.r i).im ∧ (x.r i).im ≤ CA ∧ ‖x.r i‖ ≤ CA := by
    intro i; have := I.damping i; rw [hIC, hIc] at this; exact this
  have hrA' : ∀ a, cA ≤ (rA a).im ∧ (rA a).im ≤ CA + 1 ∧ ‖rA a‖ ≤ CA + 1 := by
    intro a; obtain ⟨h1, h2, h3⟩ := hdampI a.val
    exact ⟨h1, by linarith, by linarith⟩
  have hgdiag : ∀ a : x.endpoint.active, resetInverse MA rA t' a a = x.endpoint.g a.val a.val := by
    intro a; rw [hfg, padM_val]
  have hgA : ∀ a, (resetInverse MA rA t' a a).im ≤ CA + 1 := by
    intro a
    rw [hgdiag]
    have h1 := hlag a.val a.property
    have h2 : |(x.endpoint.g a.val a.val - x.r a.val).im| ≤
        ‖x.endpoint.g a.val a.val - x.r a.val‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im] at h2
    have h3 := (hdampI a.val).2.1
    have := le_abs_self ((x.endpoint.g a.val a.val).im - (x.r a.val).im)
    linarith
  obtain ⟨hR, hdamp', hCζ⟩ := hvar x.endpoint.active MA rA ζ t' ht'pos hMAs hrA' hgA (hζ.trans hs2') hfix
  -- the reset half
  set new := resetEndpoint x.endpoint x.r ζ t' with hnew
  have hng : new.g = padM x.endpoint.active (resetInverse MA ((fun a => x.r a.val) + ζ) t') := rfl
  have hna : new.active = x.endpoint.active := rfl
  have hp : ∀ i ∈ x.endpoint.active, 0 ≤ (x.r i).im := fun i _ => hcA.le.trans (hdampI i).1
  have hCrζ : Cr * ‖ζ‖ ≤ C * t' ^ (0.35 * delta) :=
    mul_le_mul hCrC hζ (norm_nonneg _) (by linarith)
  have hRS := reset_step x.endpoint.active MA x.r ζ t' Cr x.endpoint new rfl hna hfg hng hR hp hCr.le
    (by linarith) hker
  obtain ⟨hdiagN, hKN, hinvN⟩ := hRS
  -- the stage step
  have hstep : StageStep d m C t t' old new x.r (x.r + padV x.endpoint.active ζ) :=
    { sw := I.state 0
      fin := x.endpoint
      sw_active := sweep.active
      sw_affine := sweep.affine
      sw_K := sweep.K
      fin_nested := by rw [← hlast]; exact assembly_nested I _
      fin_K := by unfold Kn; exact hKfin
      fin_inv := fun y hy => by unfold Xof; exact hinv y hy
      new_active := hna
      r_close := by
        rw [add_sub_cancel_left]
        exact (norm_padV_le _ ζ).trans hζ
      new_K := by unfold Kn; linarith
      new_inv := fun y hy => by
        have hε0 : 0 ≤ Cr * ‖ζ‖ := mul_nonneg hCr.le (norm_nonneg _)
        obtain ⟨h1, h2⟩ := hinvN y hy
        have hX0 := Xof_nonneg x.endpoint x.r t' y
        unfold Xof at hX0 ⊢
        constructor
        · refine le_trans ?_ h1
          apply mul_le_mul_of_nonneg_right _ hX0
          exact inv_anti₀ (by linarith) (by linarith)
        · refine h2.trans ?_
          apply mul_le_mul_of_nonneg_right _ hX0
          exact inv_anti₀ (by linarith) (by linarith) }
  -- the boundary facts at stage j + 1
  have hphys : IsDampedEndpoint new (x.r + padV x.endpoint.active ζ) t' :=
    resetEndpoint_damped x.endpoint x.r ζ t' (cA / 2) hD.1 ht'pos (by positivity)
      (fun a => (hdamp' a).1)
  have hrows : ∀ i, rowFour (normalizedInverse new t') i ≤ t' ^ (1 + delta) := by
    intro i
    have hnorm : normalizedInverse new t' =
        (Real.sqrt t' : ℂ) • padM x.endpoint.active (resetInverse MA (rA + ζ) t') := rfl
    rw [hnorm]
    by_cases hi : i ∈ x.endpoint.active
    · rw [rowFour_smul_padM x.endpoint.active _ _ ⟨i, hi⟩]
      obtain ⟨-, -, -, hr4, -, -⟩ := hR
      have hr4' : rowFour ((Real.sqrt t' : ℂ) • resetInverse MA (rA + ζ) t' -
          (Real.sqrt t' : ℂ) • resetInverse MA rA t') ⟨i, hi⟩ ^ (1 / 4 : ℝ) ≤
          Cr * t' ^ (1 / 4 : ℝ) * ‖ζ‖ := hr4 ⟨i, hi⟩
      have hrow' : rowFour ((Real.sqrt t' : ℂ) • resetInverse MA rA t') ⟨i, hi⟩ <
          0.8 * t' ^ (1 + delta) := by
        have h8 := (hrow i).2
        have he : normalizedInverse x.endpoint t' =
            (Real.sqrt t' : ℂ) • padM x.endpoint.active (resetInverse MA rA t') := by
          rw [normalizedInverse, hfg]
        rw [he, rowFour_smul_padM x.endpoint.active _ _ ⟨i, hi⟩] at h8
        exact h8
      have key := rowFour_reset_le ((Real.sqrt t' : ℂ) • resetInverse MA rA t')
        ((Real.sqrt t' : ℂ) • resetInverse MA (rA + ζ) t') ⟨i, hi⟩ t' Cr ‖ζ‖ ht'pos hζ hCr.le
        hrow' hr4' hs4'
      exact key
    · rw [rowFour_smul_padM_out x.endpoint.active _ _ i hi]
      exact (Real.rpow_pos_of_pos ht'pos _).le
  have hkerN : constantKernel new.active (endpointEnergy new (x.r + padV x.endpoint.active ζ) t') := by
    obtain ⟨-, -, -, -, -, hE⟩ := hR
    have hFin : ∀ f, endpointEnergy x.endpoint x.r t' f =
        wardEnergy Finset.univ (fun a : x.endpoint.active => (x.r a.val).im)
          ((Real.sqrt t' : ℂ) • resetInverse MA (fun a => x.r a.val) t') (fun a : x.endpoint.active => f a.val) := by
      intro f
      unfold endpointEnergy normalizedInverse
      rw [hfg, wardEnergy_padM]
    have hNew : ∀ f, endpointEnergy new (x.r + padV x.endpoint.active ζ) t' f =
        wardEnergy Finset.univ (fun a : x.endpoint.active => (((fun a : x.endpoint.active => x.r a.val) + ζ) a).im)
          ((Real.sqrt t' : ℂ) • resetInverse MA ((fun a => x.r a.val) + ζ) t')
          (fun a : x.endpoint.active => f a.val) := by
      intro f
      unfold endpointEnergy normalizedInverse
      rw [hna, hng, wardEnergy_padM]
      congr 2
      funext a
      simp [padV, a.property]
    refine constantKernel_of_compare _ (endpointEnergy x.endpoint x.r t') _ (Cr * ‖ζ‖)
      (by linarith) (fun f => ?_) (fun f => ?_) hker
    · unfold endpointEnergy
      exact wardEnergy_nonneg x.endpoint.active _ hp _ f
    · rw [hFin, hNew]
      exact hE (fun a : x.endpoint.active => f a.val)
  have hmet : ∀ y z, physicalDistance d m y z / 2 - t' ^ (-1.03 : ℝ) ≤
      terminalDistance (nnGraph d m) (Finset.univ \ new.active) y z := by
    intro y z
    have := I.metric (Fin.last k) y z
    rw [hlast] at this
    exact this
  exact BoundaryHist.extend hk old new x.r (x.r + padV x.endpoint.active ζ) hist ⟨hstep⟩ hphys hdiagN hrows
    hkerN hcount hmet

end AndersonAC.AgentS78
