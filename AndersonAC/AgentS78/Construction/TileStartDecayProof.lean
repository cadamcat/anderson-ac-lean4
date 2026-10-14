import AndersonAC.AgentS78.Construction.TileStartDecay
import AndersonAC.AgentS78.Construction.TileStartV3

/-!
# WP10 tile phase: the decay clauses from the prefix Schur identity and Combes–Thomas

agent-s78start (2026-10-14). `tileStartDecay_of_parts : PrefixPhysStatement →
ActiveCTStatement d → TileStartDecayStatement d`: at every prefix (and at the start, the empty
prefix) the live state is the port lift of the inverse of `M_A + diag ζ − t diag(ϑ r)`, whose
damping `t ϑ Im r` lies between `t cP/4` and `t CP`; Combes–Thomas gives the decay, the port
weights are at most one, and the cover distance is the physical distance of the sites.
-/

noncomputable section
set_option autoImplicit false

open scoped BigOperators

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

theorem splitPorts_weight_abs_le_one {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (p : Port d m) :
    ‖(((S45.splitPorts (Torus d m) θ).weight p : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  have h0 : 0 ≤ (S45.splitPorts (Torus d m) θ).weight p := by
    simp only [S45.splitPorts, S45.power]
    split_ifs
    · exact Real.rpow_nonneg hθ0 _
    · exact Real.rpow_nonneg (by linarith) _
  rw [abs_of_nonneg h0]
  simp only [S45.splitPorts, S45.power]
  split_ifs
  · exact Real.rpow_le_one hθ0 hθ1 (by norm_num)
  · exact Real.rpow_le_one (by linarith) (by linarith) (by norm_num)

/-- Entry bound of a lifted prefix entry. -/
theorem lift_entry_le {θ t : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (p p' : Port d m) (G : ℂ) :
    ‖(Real.sqrt t : ℂ) * ((((S45.splitPorts (Torus d m) θ).weight p : ℝ) : ℂ) *
        (((S45.splitPorts (Torus d m) θ).weight p' : ℝ) : ℂ) * G)‖ ≤ ‖(Real.sqrt t : ℂ) * G‖ := by
  have h1 := splitPorts_weight_abs_le_one (d := d) (m := m) hθ0 hθ1 p
  have h2 := splitPorts_weight_abs_le_one (d := d) (m := m) hθ0 hθ1 p'
  rw [show (Real.sqrt t : ℂ) * ((((S45.splitPorts (Torus d m) θ).weight p : ℝ) : ℂ) *
        (((S45.splitPorts (Torus d m) θ).weight p' : ℝ) : ℂ) * G) =
      ((((S45.splitPorts (Torus d m) θ).weight p : ℝ) : ℂ) *
        (((S45.splitPorts (Torus d m) θ).weight p' : ℝ) : ℂ)) * ((Real.sqrt t : ℂ) * G) by ring]
  rw [norm_mul, norm_mul]
  have h3 : 0 ≤ ‖(Real.sqrt t : ℂ) * G‖ := norm_nonneg _
  calc _ ≤ 1 * 1 * ‖(Real.sqrt t : ℂ) * G‖ := by
        apply mul_le_mul_of_nonneg_right _ h3
        exact mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = _ := by ring

/-- Monotonicity of the decay profile in the constant. -/
theorem decay_mono {C₁ C t a dd : ℝ} (hC₁ : 0 < C₁) (hC : C₁ ≤ C) (ht : 0 < t) (ha : 0 ≤ a)
    (hd : 0 ≤ dd) :
    C₁ / Real.sqrt t * Real.exp (-a * dd / C₁) ≤ C / Real.sqrt t * Real.exp (-a * dd / C) := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  apply mul_le_mul (div_le_div_of_nonneg_right hC hs.le) _ (Real.exp_pos _).le
    (div_nonneg (hC₁.le.trans hC) hs.le)
  apply Real.exp_le_exp.mpr
  have hC0 : 0 < C := hC₁.trans_le hC
  rw [neg_mul, neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_left (mul_nonneg ha hd) hC₁ hC

/-- **The decay clauses from (P1) and (P2).** -/
theorem tileStartDecay_of_parts (hP1 : PrefixPhysStatement) (hP2 : ActiveCTStatement d) :
    TileStartDecayStatement d := by
  classical
  intro cP CP cL CL C₀ hcP hCP hcL hCL hC₀
  obtain ⟨C₂, hC₂, t₂, ht₂, h2⟩ := hP2 (cP / 4) CP (by positivity) (by linarith)
  refine ⟨C₂, hC₂, min t₂ (1 / 2), lt_min ht₂ (by norm_num), ?_⟩
  intro C hC m n₀ u E P j z hn₀ hu' hu hj0 hj ht hSB hD hphys hdist
  subst hu' hn₀
  set θ := sweepTheta P.u m j with hθdef
  set t := sweepScale P.u m j with htdef
  have hu0 : 0 < P.u := by linarith [hu.1]
  have htpos : 0 < t := by
    simp only [htdef]; unfold sweepScale stageScale; split_ifs <;> positivity
  have ht2 : t < t₂ := ht.trans_le (min_le_left _ _)
  have hθb := sweepTheta_bounds hu0 (by omega : 0 < j) hj
  have hθ0 : 0 < θ := by linarith [hθb.1]
  have hθ1 : θ < 1 := by linarith [hθb.2]
  have hts : t = stageScale P.u (j - 1) m := sweepScale_eq_stage P.u hj
  have hSB' := hSB
  unfold StageBounds at hSB'
  dsimp only at hSB'
  obtain ⟨hdiag, -, -, -, -, hmet, -⟩ := hSB'
  rw [← hts] at hmet
  have hC₂pos : (0 : ℝ) < C₂ := lt_of_lt_of_le one_pos hC₂
  -- the bound at any prefix
  have key : ∀ (q : S45.Sequence (Port d m)), q.wellFormed t (portR θ z.r) →
      q.state 0 = sweepStartLiveState θ z →
      (∀ k < q.length, ∀ y, q.pivot k = some y → y.2 = false) →
      ∀ k ≤ q.length, ∀ p p' : (q.state k).live,
        ‖((q.state k).state (portR θ z.r)).h t p p'‖ ≤
            C / Real.sqrt t * Real.exp (-t ^ 3 * (P.cover j).dist p.1 p'.1 / C) ∧
        (C * S45.power t (-2) < (P.cover j).dist p.1 p'.1 →
          ‖((q.state k).state (portR θ z.r)).h t p p'‖ ≤
            C / Real.sqrt t * Real.exp (-t * (P.cover j).dist p.1 p'.1 / C)) := by
    intro q hq hq0 hbit k hk p p'
    obtain ⟨ζ, G, hBG, hg⟩ := hP1 d m t θ z q htpos hθ0 hθ1 hD hq hq0 hbit k hk
    -- active sites of live ports
    have hlive_sub : ∀ x ∈ (q.state k).live, x.1 ∈ z.endpoint.active := by
      intro x hx
      have := (mem_live_iff hq hk x).mp hx
      rw [hq0] at this
      have h1 := this.1
      simp only [sweepStartLiveState, Finset.mem_filter, Finset.mem_univ, true_and] at h1
      exact h1
    set ϑ := prefixVartheta θ (q.state k).live
    have hϑ : ∀ i, θ ≤ ϑ i ∧ ϑ i ≤ 1 := by
      intro i; simp only [ϑ, prefixVartheta]; split_ifs <;> constructor <;> linarith
    have hBG' : (z.endpoint.M.submatrix (Subtype.val : z.endpoint.active → Torus d m) Subtype.val +
        Matrix.diagonal (fun i : z.endpoint.active =>
          (((ζ i.val - t * ϑ i.val * (z.r i.val).re) : ℝ) : ℂ) -
            Complex.I * (((t * ϑ i.val * (z.r i.val).im) : ℝ) : ℂ))) *
        G.submatrix Subtype.val Subtype.val = 1 := by
      rw [← hBG]
      congr 1
      rw [add_sub_assoc]
      congr 1
      ext a b
      simp only [Matrix.diagonal_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      split_ifs
      · apply Complex.ext <;> simp <;> ring
      · simp
    have hτ : ∀ i ∈ z.endpoint.active, cP / 4 * t ≤ t * ϑ i * (z.r i).im ∧
        t * ϑ i * (z.r i).im ≤ CP * t := by
      intro i hi
      obtain ⟨-, h1, h2', -⟩ := hdiag i hi
      obtain ⟨hv1, hv2⟩ := hϑ i
      constructor
      · have : cP / 4 ≤ ϑ i * (z.r i).im := by nlinarith [hθb.1]
        nlinarith
      · have : ϑ i * (z.r i).im ≤ CP := by nlinarith
        nlinarith
    have hp1 := hlive_sub p.1 p.2
    have hp2 := hlive_sub p'.1 p'.2
    obtain ⟨hd1, hd2⟩ := h2 m t E z (fun i => ζ i - t * ϑ i * (z.r i).re)
      (fun i => t * ϑ i * (z.r i).im) G htpos ht2 hphys hmet hτ hBG' p.1.1 hp1 p'.1.1 hp2
    have hentry : ((q.state k).state (portR θ z.r)).h t p p' =
        (Real.sqrt t : ℂ) * ((((S45.splitPorts (Torus d m) θ).weight p.1 : ℝ) : ℂ) *
          (((S45.splitPorts (Torus d m) θ).weight p'.1 : ℝ) : ℂ) * G p.1.1 p'.1.1) := by
      simp only [S45.State.h, Matrix.smul_apply, smul_eq_mul, S45.LiveState.state, S45.restrict,
        Matrix.submatrix_apply]
      rw [hg p.1 p'.1 p.2 p'.2]
    have hle := lift_entry_le (t := t) hθ0.le hθ1.le p.1 p'.1 (G p.1.1 p'.1.1)
    rw [← hentry] at hle
    have hdd : (P.cover j).dist p.1 p'.1 = physicalDistance d m p.1.1 p'.1.1 := by
      rw [hdist]; rfl
    have hdist0 : 0 ≤ physicalDistance d m p.1.1 p'.1.1 := by
      unfold physicalDistance; positivity
    rw [hdd]
    refine ⟨hle.trans (hd1.trans (decay_mono hC₂pos hC htpos (by positivity) hdist0)), ?_⟩
    intro hfar
    have hfar' : C₂ * S45.power t (-2) < physicalDistance d m p.1.1 p'.1.1 := by
      have : 0 ≤ S45.power t (-2) := Real.rpow_nonneg htpos.le _
      nlinarith
    exact hle.trans ((hd2 hfar').trans (decay_mono hC₂pos hC htpos htpos.le hdist0))
  -- the empty prefix
  set q₀ := (sweepStartMap θ t z).sweep
  have hq₀ : q₀.wellFormed t (portR θ z.r) :=
    ⟨fun k _ => sweepStartLiveState_masked θ z hD.2.1, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  refine ⟨fun p p' => (key q₀ hq₀ rfl (fun k hk => absurd hk (Nat.not_lt_zero k)) 0 le_rfl p p').1,
    fun p p' => (key q₀ hq₀ rfl (fun k hk => absurd hk (Nat.not_lt_zero k)) 0 le_rfl p p').2, ?_⟩
  intro q hq hq0 hbit k hk _
  exact ⟨fun p p' => (key q hq hq0 hbit k hk p p').1, fun p p' => (key q hq hq0 hbit k hk p p').2⟩

/-- **The duplicated stage start (v3) from the two sub-contracts (P1) and (P2).** -/
theorem tileStartV3_of_parts (hd : 3 ≤ d) (hP1 : PrefixPhysStatement)
    (hP2 : ActiveCTStatement d) : TileStartV3Statement d :=
  tileStartV3_of_decay hd (tileStartDecay_of_parts hP1 hP2)

end AndersonAC.AgentS78
