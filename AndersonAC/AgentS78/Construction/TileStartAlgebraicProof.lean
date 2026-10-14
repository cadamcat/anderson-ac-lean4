import AndersonAC.AgentS78.Construction.TileStartAlgebraic
import AndersonAC.AgentS78.Comparators

/-!
# WP10 tile phase: proof of the algebraic duplicated stage start (v3 proposal)

agent-s78start (2026-10-14). `tileStartAlgebraic_proof d hd : TileStartAlgebraicStatement d`.
Route: `sweep_prestate` (physical S45 state of the active block: broad bounds, `g_ii = r_i`,
symmetry, Ward, constant kernel, `‖K‖ ≤ 1/3`), the live start lift as a mass-one port lift
(`startLive_eq`, `livePortMap_mass`), `S45.duplication` and `S45.duplication_sharp`
(AgentS45 proofs), the §3 charge estimate (`live_fourier`), the port comparison
(`live_comparison` from `initial_comparison_of_stageBounds`).
-/

noncomputable section
set_option autoImplicit false

open scoped BigOperators Matrix.Norms.L2Operator

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

theorem formComparable_mono {P : Type*} {Q R : S45.Form P} {K C : ℝ} (h : S45.formComparable Q R K)
    (hR : ∀ f, 0 ≤ R f) (hK : 0 < K) (hKC : K ≤ C) : S45.formComparable Q R C := by
  intro f
  obtain ⟨h1, h2⟩ := h f
  have hR0 := hR f
  have hC : 0 < C := hK.trans_le hKC
  refine ⟨?_, h2.trans (mul_le_mul_of_nonneg_right hKC hR0)⟩
  calc R f / C ≤ R f / K := div_le_div_of_nonneg_left hR0 hK hKC
    _ ≤ Q f := h1

theorem lamPlus_nonneg (d m : ℕ) (Y : Torus d m → ℝ) : 0 ≤ LamPlus d m Y :=
  inverseEnergy_nonneg_zero _ _ (by simp [gradientEnergy]) Y

theorem power_nonneg' (t e : ℝ) (ht : 0 ≤ t) : 0 ≤ S45.power t e := Real.rpow_nonneg ht e

set_option maxHeartbeats 1000000 in
/-- **The algebraic duplicated stage start on the live ports (v3 proposal), proved.** -/
theorem tileStartAlgebraic_proof (d : ℕ) (hd : 3 ≤ d) : TileStartAlgebraicStatement d := by
  classical
  intro cP CP cL CL C₀ hcP hCP hcL hCL hC₀
  obtain ⟨CF, hCF, hF⟩ := live_fourier (d := d) hd
  set Cb := max CP (1 / cP) with hCbdef
  set c₁ := (max C₀ CL)⁻¹ with hc₁def
  set c₂ := (min cL (1 / (2 * (CP * CP))) / 2)⁻¹ with hc₂def
  set Kc := max (c₂ + 4 * Cb ^ 2) (8 / c₁ + 8 * Cb ^ 2) with hKcdef
  set C' := max (max 1 (2 * Cb)) (max (max CF CL) Kc) with hC'def
  have hT'1 : 1 ≤ C' := le_max_of_le_left (le_max_left _ _)
  have hT'Cb : 2 * Cb ≤ C' := le_max_of_le_left (le_max_right _ _)
  have hT'F : CF ≤ C' := le_max_of_le_right (le_max_of_le_left (le_max_left _ _))
  have hT'L : CL ≤ C' := le_max_of_le_right (le_max_of_le_left (le_max_right _ _))
  have hT'K : Kc ≤ C' := le_max_of_le_right (le_max_right _ _)
  have hCPpos : 0 < CP := hcP.trans_le hCP
  have hCbpos : 0 < Cb := hCPpos.trans_le (le_max_left _ _)
  have hc₁ : 0 < c₁ := inv_pos.mpr (hC₀.trans_le (le_max_left _ _))
  have hc₂ : 0 ≤ c₂ := by
    apply inv_nonneg.mpr
    apply div_nonneg _ (by norm_num)
    exact le_min hcL.le (by positivity)
  have hKc : 0 < Kc := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  refine ⟨C', hT'1, 1 / 2, by norm_num, ?_⟩
  intro C hC
  have hC'1 : 1 ≤ C := hT'1.trans hC
  have hC'F : CF ≤ C := hT'F.trans hC
  have hC'L : CL ≤ C := hT'L.trans hC
  have hC'K : Kc ≤ C := hT'K.trans hC
  have hC'Cb : 2 * Cb ≤ C := hT'Cb.trans hC
  intro m n₀ u P j z hn₀ hu' hu hj0 hj ht0 hSB hD hen hb hsite
  subst hu' hn₀
  set θ := sweepTheta P.u m j with hθdef
  set T := stageScale P.u (j - 1) m with hTdef
  have hts : sweepScale P.u m j = T := sweepScale_eq_stage P.u hj
  have hu0 : 0 < P.u := by linarith [hu.1]
  have hTpos : 0 < T := by
    rw [← hts]; unfold sweepScale stageScale; split_ifs <;> positivity
  have hT1 : T < 1 := by rw [← hts]; linarith
  have hθb := sweepTheta_bounds hu0 (by omega : 0 < j) hj
  have hθ0 : 0 ≤ θ := by linarith [hθb.1]
  have hθ1 : θ ≤ 1 := by linarith [hθb.2]
  have hm : 0 < m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    subst hm0
    have hj1 : j = 1 := by omega
    subst hj1
    have : T = 2 * P.u := by simp [hTdef, stageScale]; ring
    linarith [hu.1]
  have hD' : IsDampedEndpoint z.endpoint z.r T := hts ▸ hD
  -- physical facts
  set e := actEquiv z
  set s := physState z with hsdef
  obtain ⟨hbroad, hfix, hsym, hward, hker, hK⟩ :=
    sweep_prestate (n₀ := P.n₀) z.endpoint z.r hcP hD' hu e hSB
  have hSB' := hSB
  unfold StageBounds at hSB'
  dsimp only at hSB'
  obtain ⟨-, hrowsSB, -, -, hcount, -, hcompSB⟩ := hSB'
  have hrowCap : ∀ x : ℝ, 0 < x → x ^ (1 + S78.delta) = S45.rowCap x := by
    intro x _
    simp only [S45.rowCap, S45.power, S45.delta, S78.delta, Real.rpow_eq_pow]
  have hrows : ∀ k, s.fourthRow T Finset.univ k ≤ S45.rowCap T := by
    intro k
    calc s.fourthRow T Finset.univ k
        = rowFour (normalizedInverse z.endpoint T) (e k).val :=
          (rowFour_eq_S45 z.endpoint z.r T e hD'.2.1 k).symm
      _ ≤ T ^ (1 + S78.delta) := hrowsSB _
      _ = S45.rowCap T := hrowCap T hTpos
  have hp : ∀ k, 0 < s.p k := fun k =>
    lt_of_lt_of_le (one_div_pos.mpr hCbpos) (hbroad k).2.1
  -- the port lift
  set v := livePortMap θ z with hvdef
  have hmass := livePortMap_mass θ z hθ0 hθ1
  have hk : ∀ x, 0 < v.weight x :=
    livePortMap_weight_pos θ z (by linarith [hθb.1]) (by linarith [hθb.2])
  have hw4 : ∀ x, 1 / 4 ≤ v.weight x ^ 4 ∧ v.weight x ^ 4 ≤ 3 / 4 :=
    live_weight4_bounds z ⟨hθb.1, by linarith [hθb.2]⟩
  have hw2 : ∀ x, 1 / 2 ≤ v.weight x ^ 2 ∧ v.weight x ^ 2 ≤ 1 := by
    intro x
    have h4 := hw4 x
    have hsq : v.weight x ^ 4 = (v.weight x ^ 2) ^ 2 := by ring
    rw [hsq] at h4
    have h0 : 0 ≤ v.weight x ^ 2 := sq_nonneg _
    constructor <;> nlinarith
  have hdup := AgentS45.duplication_algebraic v s T hmass hfix
  have hKlive : ‖(v.liftState s).K T‖ ≤ 1 / 3 := by rw [hdup.2.2.1]; exact hK
  have hkerlive := lift_constantKernel v s T hmass hk hfix hker hp
  have hrowslive : ∀ x, (v.liftState s).fourthRow T Finset.univ x ≤ 3 / 4 * S45.rowCap T :=
    lift_rows v s T hmass (3 / 4) (S45.rowCap T) (fun x => (hw4 x).2) hrows
      (power_nonneg' _ _ hTpos.le)
  have hlaglive := lift_lag_zero v s T hfix
  -- physical sharp comparator in S45 form
  have hsharpPhys : ∀ y', S45.neutral y' → s.X T y' ≤
      (1 + S45.power T S45.kappa) * (∑ k, y' k ^ 2 / s.p k ^ 2) +
        CL * T * LamPlus d m (extendFun e y') := by
    intro y' hy'
    set Y := extendFun e y'
    have hYc : (fun k => Y (e k).val) = y' := extendFun_comp e y'
    have hYn : neutral z.endpoint.active Y := by
      refine ⟨fun i hi => by simp [Y, extendFun, hi], ?_⟩
      rw [← sum_active_equiv z.endpoint.active e Y, hYc]; exact hy'
    have h := (hcompSB Y hYn).2.2
    rw [inverseEnergy_eq_S45X z.endpoint z.r T e hsym hward Y, hYc] at h
    have hsum : ∑ i ∈ z.endpoint.active, Y i ^ 2 / (z.r i).im ^ 2 =
        ∑ k, y' k ^ 2 / s.p k ^ 2 := by
      rw [← sum_active_equiv z.endpoint.active e (fun i => Y i ^ 2 / (z.r i).im ^ 2)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show Y (e k).val = y' k from congrFun hYc k]
      rfl
    have hexp : T ^ (0.005 * S78.delta) = S45.power T S45.kappa := by
      simp only [S45.power, S45.kappa, S45.delta, S78.delta, Real.rpow_eq_pow]
      norm_num
    rw [hsum, hexp] at h
    exact h
  have hsharpLive := AgentS45.duplication_sharp_proof v s T (S45.power T S45.kappa) CL
    (fun y' => LamPlus d m (extendFun e y')) hTpos (power_nonneg' _ _ hTpos.le) hCL.le
    hmass hk hfix hp hker hsharpPhys
  -- the comparison
  have hb' : (P.cover j).b = stageScale P.u P.n₀ m * T := by rw [hb, hts]
  have hbpos : 0 < stageScale P.u P.n₀ m * T := mul_pos (stageScale_pos' hu P.n₀ m) hTpos
  have hne : z.endpoint.active.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    rw [h0, Finset.card_empty] at hcount
    have : 0 < Fintype.card (Torus d m) := Fintype.card_pos
    omega
  have hphysComp := initial_comparison_of_stageBounds hm hu z.endpoint z.r hD' hne hcP hcL
    hCL.le hC₀ hSB
  have hE : ∀ g, endpointEnergy z.endpoint z.r T (extendFun e g) = S45.qform (s.D T) g := by
    intro g
    rw [endpointEnergy_eq_S45 z.endpoint z.r T e hsym hward, extendFun_comp]
    rfl
  have hcomp := live_comparison z s T (θ := θ) ⟨hθb.1, by linarith [hθb.2]⟩ hbpos hc₁ hc₂
    hCbpos hfix (fun k => ⟨(hbroad k).2.1, (hbroad k).2.2⟩)
    (fun g => by rw [← hE]; exact (hphysComp _).1)
    (fun g => by rw [← hE]; exact (hphysComp _).2)
  have hcomp' := formComparable_mono hcomp (liveW_nonneg z hbpos) hKc hC'K
  -- assemble the clauses
  have hTκ : 0 ≤ S45.power T S45.kappa := power_nonneg' _ _ hTpos.le
  have hS0 : S45.LiveState.state ⟨liveStart z, (sweepStartLiveState θ z).g⟩ (portR θ z.r) =
      v.liftState s := startLS_state_eq θ z
  have hvalid : (sweepStartMap θ (sweepScale P.u m j) z).sweep.valid
      (sweepScale P.u m j) (portR θ z.r)
      (stageD0 P j (sweepStartMap θ (sweepScale P.u m j) z)) 0 := by
    rw [hts]
    unfold S45.Sequence.valid
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [S45.Sequence.Jrecord, Finset.range_zero, Finset.sum_empty, norm_zero]
      exact power_nonneg' _ _ hTpos.le
    · intro f
      simp only [S45.Sequence.Lrecord, Finset.range_zero, Finset.sum_empty]
      have hq0 : S45.qform (0 : S45.RMat (Port d m)) f = 0 := by simp [S45.qform]
      rw [hq0, abs_zero]
      apply mul_nonneg (power_nonneg' _ _ hTpos.le)
      change 0 ≤ S45.qform (((startLS θ z).ambient (portR θ z.r)).D (sweepScale P.u m j)) f
      rw [hts, ambient_qform_eq]
      simp only [startLS]
      rw [hS0]
      exact hkerlive.2.1 _
    · change ∀ i : (startLS θ z).live,
        ((startLS θ z).state (portR θ z.r)).fourthRow T Finset.univ i ≤ S45.rowCap T
      simp only [startLS]
      rw [hS0]
      intro i
      refine (hrowslive i).trans ?_
      have := power_nonneg' T (1 + S45.delta) hTpos.le
      unfold S45.rowCap; linarith
    · change ∀ i : (startLS θ z).live,
        ‖((startLS θ z).state (portR θ z.r)).lag T i‖ ≤ S45.power T S45.beta
      simp only [startLS]
      rw [hS0]
      intro i
      calc _ = ‖(0 : ℂ)‖ := congrArg norm (hlaglive i)
        _ ≤ _ := by rw [norm_zero]; exact power_nonneg' _ _ hTpos.le
  refine ⟨?_, hvalid⟩
  rw [sweepStartLiveState_eq_startLS]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- start_prestate
    simp only [liveStartState, hts, startLS]
    rw [hS0]
    refine ⟨fun y => LamPlus d m (extendFun e (v.sumCharge y)), 0, ?_, hKlive,
      fun y _ => lamPlus_nonneg d m _, fun y hy => ?_⟩
    · refine
        { scale := ⟨hTpos, hT1⟩
          broad := fun x => ?_
          symmetric := AgentS45.lift_g_isSymm v s hsym
          ward := lift_ward_of_mass v s T hmass hward
          K_cap := hKlive.trans (by norm_num)
          invertible := isUnit_one_sub_of_norm_lt_one (hKlive.trans_lt (by norm_num))
          kernel := hkerlive
          row_cap := fun x => (hrowslive x).trans (by
            have := power_nonneg' T (1 + S45.delta) hTpos.le
            unfold S45.rowCap; linarith)
          lag_cap := fun x => by rw [hlaglive x, norm_zero]; exact power_nonneg' _ _ hTpos.le
          sharp := fun y hy => ?_
          fourier := fun y hy => ?_
          dual_fourier := fun y _ => ?_
          volume := ?_ }
      · obtain ⟨h1, h2, h3⟩ := lift_broad v s Cb hCbpos hw2 (fun k => hbroad k) x
        refine ⟨h1.trans (by linarith), le_trans ?_ h2, h3.trans (by linarith)⟩
        rw [div_le_div_iff₀ (by linarith) (by positivity)]; linarith
      · have h := hsharpLive y hy
        have hSig : 0 ≤ ∑ x, y x ^ 2 / (v.liftState s).p x ^ 2 :=
          Finset.sum_nonneg fun _ _ => by positivity
        have hLam := lamPlus_nonneg d m (extendFun e (v.sumCharge y))
        have h1 : (1 + S45.power T S45.kappa) * (∑ x, y x ^ 2 / (v.liftState s).p x ^ 2) ≤
            (1 + C * S45.power T S45.kappa) * (∑ x, y x ^ 2 / (v.liftState s).p x ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ hSig; nlinarith
        have h2 : CL * T * LamPlus d m (extendFun e (v.sumCharge y)) ≤
            C * T * LamPlus d m (extendFun e (v.sumCharge y)) := by
          apply mul_le_mul_of_nonneg_right _ hLam
          exact mul_le_mul_of_nonneg_right hC'L hTpos.le
        linarith
      · have h := hF m hm z θ y hy
        have h0 : 0 ≤ S45.power (S45.l1 y) (4 / 3) * S45.power (S45.l2sq y) (1 / 3) :=
          mul_nonneg (power_nonneg' _ _ (Finset.sum_nonneg fun _ _ => norm_nonneg _))
            (power_nonneg' _ _ (Finset.sum_nonneg fun _ _ => by positivity))
        calc LamPlus d m (extendFun e (v.sumCharge y))
            ≤ CF * S45.power (S45.l1 y) (4 / 3) * S45.power (S45.l2sq y) (1 / 3) := h
          _ ≤ C * S45.power (S45.l1 y) (4 / 3) * S45.power (S45.l2sq y) (1 / 3) := by
            rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hC'F h0
      · have h0 : 0 ≤ S45.power (S45.l1 y) (4 / 3) * S45.power (S45.l2sq y) (1 / 3) :=
          mul_nonneg (power_nonneg' _ _ (Finset.sum_nonneg fun _ _ => norm_nonneg _))
            (power_nonneg' _ _ (Finset.sum_nonneg fun _ _ => by positivity))
        have hl : 0 ≤ S45.l2sq y := Finset.sum_nonneg fun _ _ => by positivity
        have : 0 ≤ C * T * S45.power (S45.l1 y) (4 / 3) * S45.power (S45.l2sq y) (1 / 3) := by
          rw [mul_assoc]; exact mul_nonneg (by positivity) h0
        show (0 : ℝ) ≤ _
        linarith
      · have h := live_volume hd hm z hcount hT1.le (hts ▸ sweepScale_lower hu m j hj)
        have h0 := power_nonneg' T (1 + S45.delta + S45.kappa) hTpos.le
        refine h.trans ?_
        exact mul_le_mul_of_nonneg_right hC'1 h0
    · have h := hsharpLive y hy
      have hLam := lamPlus_nonneg d m (extendFun e (v.sumCharge y))
      have h2 : CL * T * LamPlus d m (extendFun e (v.sumCharge y)) ≤
          C * T * LamPlus d m (extendFun e (v.sumCharge y)) := by
        apply mul_le_mul_of_nonneg_right _ hLam
        exact mul_le_mul_of_nonneg_right hC'L hTpos.le
      exact h.trans (add_le_add le_rfl h2)
  · -- start_lag
    intro i
    simp only [S45.LiveState.ambientLag, hts, startLS]
    split_ifs with hi
    · rw [hS0, hlaglive]
    · rfl
  · -- start_comparison
    simp only [liveStartState, hts, startLS]
    rw [hS0, hsite, hen, hb']
    exact hcomp'
  · -- start_rows
    intro i
    simp only [liveStartState, hts, startLS]
    rw [hS0]
    exact hrowslive i
  · -- start_reserve_rows
    intro i hi
    simp only [liveStartState, hts, startLS]
    rw [hS0]
    exact live_reserve_rows θ hθ0 hθ1 z s T (S45.rowCap T) hrows i hi

end AndersonAC.AgentS78
