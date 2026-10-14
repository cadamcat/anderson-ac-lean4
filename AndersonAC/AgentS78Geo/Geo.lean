import AndersonAC.AgentS78.Construction.ClearingTrialH
import AndersonAC.S78Geom.Geometry
import AndersonAC.AgentS78Geo.TrialSchur
import AndersonAC.AgentS78Geo.Lattice
import AndersonAC.AgentS78Geo.TraceExtend
import AndersonAC.AgentS78Geo.Scale
import AndersonAC.AgentS78Geo.Initial

/-!
# WP10 C4b: the geometric local input of the clearing trial

The record hypothesis `geo := clearingGeo d Ctr` (deterministic, about the entering record
only) and the proof of `ClearingGeometryStatement d (ClearingGood d cP CP qlag geo) cP CP`.

`ClearingGeoAt Ctr n₀ u j x`:
* `damped`: `x.endpoint` is a damped endpoint at `t_j` (`g = (M − t_j diag r)^{-1}` on the
  active sites; 06-clearing.tex:19–25; `PathwiseStageInputs.physical`);
* `trace`: a `ClearingGeometry` trace `T` of the earlier successful clearing groups
  (07-assembly.tex:103–115: the terminal set was initially empty; a success adds its core
  and heat pivots) such that
  - `hops`: every entry of `M` between active sites is a direct lattice hop `J` (symmetric,
    `|J| ≤ 1`, supported on nearest neighbours) unless the two sites are at zero collapsed
    distance for the terminal set `geometryTerminals T` (06-clearing.tex:50–54 and 207–216,
    the terminal Schur correction is block supported on active neighbours of a connected
    terminal component; the diagonal is included in the second case);
  - `fresh`: the cores of the earlier index-`j` groups are farther than `R_j` from every
    snapshot component that still has an active site (07-assembly.tex:154–156);
* `componentDiam`: a snapshot component has diameter at most `|C| R_j`
  (07-assembly.tex:202–203).
-/

open MeasureTheory Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section

namespace AndersonAC.AgentS78Geo

open AndersonAC.S78 AndersonAC.S6 AndersonAC.AgentS78
open AndersonAC.S2 (RandomSources sourcesLaw)

variable {d m : ℕ}

/-- The trace clauses of `geo`. -/
structure ClearingTraceOf {n₀ j l : ℕ} {u Ctr : ℝ} (x : RunRecord d m)
    (T : ClearingGeometry d m n₀ j l u Ctr) : Prop where
  hops : ∃ J : Matrix (Torus d m) (Torus d m) ℝ, J.IsSymm ∧ (∀ a b, |J a b| ≤ 1) ∧
    (∀ a b, J a b ≠ 0 → (nnGraph d m).Adj a b) ∧
    ∀ a ∈ x.endpoint.active, ∀ b ∈ x.endpoint.active, x.endpoint.M a b ≠ ((J a b : ℝ) : ℂ) →
      terminalDistance (nnGraph d m) (geometryTerminals T) a b = 0
  fresh : ∀ a, T.index a = j → ∀ C ∈ x.components, (∃ y ∈ C, y ∈ x.endpoint.active) →
    ∀ z ∈ T.core a, ∀ y ∈ C, separationRadius j < physicalDistance d m z y

/-- The record-level clearing geometry (`geo` of C4b). -/
structure ClearingGeoAt (Ctr : ℝ) (n₀ : ℕ) (u : ℝ) (j : ℕ) (x : RunRecord d m) : Prop where
  damped : IsDampedEndpoint x.endpoint x.r (stageScale u j m)
  trace : ∃ l, ∃ T : ClearingGeometry d m n₀ j l u Ctr, ClearingTraceOf x T
  componentDiam : ∀ C ∈ x.components, ∀ y ∈ C, ∀ z ∈ C,
    physicalDistance d m y z ≤ (C.card : ℝ) * separationRadius j

/-- `geo` for `ClearingGood`. -/
def clearingGeo (d : ℕ) (Ctr : ℝ) : ∀ {m : ℕ}, ℕ → ℝ → ℕ → Set (RunRecord d m) :=
  fun {m} n₀ u j => {x : RunRecord d m | ClearingGeoAt Ctr n₀ u j x}

theorem heatLimit_eq (t : ℝ) : AndersonAC.S6.heatLimit t = AndersonAC.S78.heatLimit t := by
  unfold AndersonAC.S6.heatLimit AndersonAC.S78.heatLimit AndersonAC.S6.eh
    AndersonAC.S78.heatExponent AndersonAC.S6.delta AndersonAC.S78.delta
  norm_num

theorem localizationRate_le (d : ℕ) (c : ℝ) (hc : 0 < c) :
    AndersonAC.SolS6.localizationRate d c ≤ c := by
  unfold AndersonAC.SolS6.localizationRate
  have hden : 0 < (4 * (1 + 2 * (d : ℝ))) := by positivity
  have hx : 0 < c / (4 * (1 + 2 * (d : ℝ))) := div_pos hc hden
  refine (Real.log_le_sub_one_of_pos (by linarith)).trans ?_
  have : c / (4 * (1 + 2 * (d : ℝ))) ≤ c := div_le_self hc.le (by nlinarith)
  linarith

/-- **C4b geometry.** -/
theorem clearingGeometry_proof (hd : 3 ≤ d) (cP CP : ℝ) (hcP : 0 < cP) (qlag : ℝ → ℝ)
    (Ctr : ℝ) (hCtr : 1 ≤ Ctr) :
    ClearingGeometryStatement d (ClearingGood d cP CP qlag (clearingGeo d Ctr)) cP CP := by
  obtain ⟨Nu, C', _, hunif⟩ := AndersonAC.SolS78.uniform_clearing_geometry_proof d hd Ctr hCtr
  set a := AndersonAC.SolS6.localizationRate d cP
  obtain ⟨ha, _⟩ := AndersonAC.SolS6.localization_rate_bound d cP hcP
  set c := min a cP
  set K := max (max CP 1) (max ((2 : ℝ) ^ d) (4 / (3 * cP)))
  have hK1 : 1 ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have hKCP : CP ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hK2d : (2 : ℝ) ^ d ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKc : 4 / (3 * cP) ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨c, K, 9, lt_min ha hcP, min_le_right _ _, hKCP, hK1, by norm_num,
    max Nu 9, ?_⟩
  intro n₀ m hN hm u hu E j hj hsched M x hx B hB hBmem hBel order q hhist hresid
  obtain ⟨hgood, hgeo⟩ := hx
  obtain ⟨hdamp, ⟨l, T, hT⟩, hdiam⟩ := hgeo
  obtain ⟨J, hJs, hJ1, hJadj, hhops⟩ := hT.hops
  have hNu : Nu ≤ n₀ := (le_max_left _ _).trans hN
  have hj9 : 9 ≤ j := ((le_max_right _ _).trans hN).trans hj.le
  have hjm2 : j + 2 ≤ m := by unfold clearingScheduled at hsched; omega
  have hm0 : 0 < m := by omega
  have ht : 0 < (stageScale u j m) := stage_t_pos u j m hu hjm2
  have ht1 : (stageScale u j m) ≤ 1 := stage_t_le_one u j m hu hjm2 (by omega)
  have hd1 : 1 ≤ d := by omega
  have hconn : (nnGraph d m).Connected := AndersonAC.SolS78.nnGraph_connected_proof
  -- the damping on the active sites
  have hr : ∀ (ω : RandomSources (Torus d m) M) (i : ActiveSite x), cP ≤ (x.r i.val).im :=
    fun _ i => (hgood.broad i.val i.2).2.1
  -- trial-start structure
  have h0 : ∀ ω (i₁ j₁ : {i // i ∈ (q.state 0 ω).active}),
      (q.state 0 ω).M i₁ j₁ ≠ J (Subtype.val (i₁ : ActiveSite x)) (Subtype.val (j₁ : ActiveSite x)) →
      terminalDistance (nnGraph d m) (geometryTerminals T) (i₁ : ActiveSite x).val
        (j₁ : ActiveSite x).val = 0 := by
    intro ω i₁ j₁ hij
    apply hhops _ (i₁ : ActiveSite x).2 _ (j₁ : ActiveSite x).2
    rw [← trial_initial_M x (stageScale u j m) hdamp hB q ω i₁ j₁]
    exact fun h => hij (Complex.ofReal_injective h)
  set dist : ActiveSite x → ActiveSite x → ℝ := fun a b => physicalDistance d m a.val b.val
  set coll := trialCollapsed q (nnGraph d m) (fun a : ActiveSite x => a.val) (geometryTerminals T)
  have hemb : Function.Injective (fun a : ActiveSite x => a.val) := Subtype.val_injective
  obtain ⟨b0, hb0⟩ := id hB
  refine ⟨coll, ?_⟩
  refine
    { dist_nonneg := fun a b => Nat.cast_nonneg _
      dist_symm := fun a b => physicalDistance_symm _ _
      dist_triangle := fun a b c => AndersonAC.SolS78AnchorTail.physicalDistance_triangle d m _ _ _
      dist_self := fun a => by simp [dist, physicalDistance]
      ell_lower := (stage_ell_bounds u j m hu hjm2).1
      ell_upper := (stage_ell_bounds u j m hu hjm2).2
      core_ball := ?_
      shells := ?_
      volume := ?_
      metric := ?_
      range_geometry := ?_
      resolvent_decay := ?_ }
  · -- core ball
    refine ⟨b0, fun b hb => ?_⟩
    apply stage_core_radius u j m d hu hjm2 hj9 hd1
    have hC := hdiam _ hBmem b0.val (Finset.mem_map_of_mem _ hb0) b.val
      (Finset.mem_map_of_mem _ hb)
    rw [Finset.card_map] at hC
    exact hC.trans (mul_le_mul_of_nonneg_right hBel (by unfold separationRadius; positivity))
  · -- shells
    intro i n
    have h := shell_card hm0 hd1 i.val n
    refine le_trans ?_ (h.trans (mul_le_mul_of_nonneg_right hK2d (by positivity)))
    exact_mod_cast Finset.card_le_card_of_injOn (fun a : ActiveSite x => a.val)
      (fun a ha => by simpa using ha) (fun a _ b _ h => hemb h)
  · -- volume
    intro i L hL
    have h := ball_card i.val L hL
    refine le_trans ?_ (h.trans (mul_le_mul_of_nonneg_right hK2d (by positivity)))
    exact_mod_cast Finset.card_le_card_of_injOn (fun a : ActiveSite x => a.val)
      (fun a ha => by simpa using ha) (fun a _ b _ h => hemb h)
  · -- metric (Lemma 7.2(1),(2) through the extended trace)
    intro k ω hk hloc i i'
    set edits : Finset (Torus d m) := (Finset.range k).image (fun l => (q.pivot l ω).val)
    have hlocs : ∀ y ∈ edits, ∃ z ∈ B.map (Function.Embedding.subtype _),
        physicalDistance d m y z ≤ inspectionRadius j / 2 := by
      intro y hy
      obtain ⟨l', hl', rfl⟩ := Finset.mem_image.mp hy
      have h := hloc l' (Finset.mem_range.mp hl')
      unfold distanceToCore at h
      rw [dif_pos hB] at h
      obtain ⟨b, hb, hbeq⟩ := Finset.exists_mem_eq_inf' hB (dist (q.pivot l' ω))
      rw [hbeq] at h
      exact ⟨b.val, Finset.mem_map_of_mem _ hb, h.le⟩
    have hsize : (edits.card : ℝ) ≤ Ctr * (AndersonAC.S78.heatLimit (stageScale u j m) : ℝ) := by
      have h1 : edits.card ≤ k := Finset.card_image_le.trans (by simp)
      have h2 : k ≤ AndersonAC.S78.heatLimit (stageScale u j m) := by
        rw [← heatLimit_eq]; exact hk.trans (q.finite_stop ω)
      have h3 : (edits.card : ℝ) ≤ (AndersonAC.S78.heatLimit (stageScale u j m) : ℝ) := by exact_mod_cast h1.trans h2
      nlinarith [(Nat.cast_nonneg (AndersonAC.S78.heatLimit (stageScale u j m)) : (0 : ℝ) ≤ _)]
    have hsep : ∀ a', T.index a' = j → ∀ y ∈ T.core a', ∀ z ∈ B.map (Function.Embedding.subtype _),
        separationRadius j < physicalDistance d m y z :=
      fun a' ha' y hy z hz => hT.fresh a' ha' _ hBmem ⟨b0.val, Finset.mem_map_of_mem _ hb0, b0.2⟩
        y hy z hz
    have hrad : ∀ y ∈ B.map (Function.Embedding.subtype _),
        physicalDistance d m b0.val y ≤ (stageScale u j m) ^ (-AndersonAC.S78.nu d) * separationRadius j := by
      intro y hy
      have hC := hdiam _ hBmem b0.val (Finset.mem_map_of_mem _ hb0) y hy
      rw [Finset.card_map] at hC
      exact hC.trans (mul_le_mul_of_nonneg_right hBel (by unfold separationRadius; positivity))
    have helig : ((B.map (Function.Embedding.subtype _)).card : ℝ) ≤ (stageScale u j m) ^ (-AndersonAC.S78.nu d) := by
      rw [Finset.card_map]; exact hBel
    set T' := extendTrace T (B.map (Function.Embedding.subtype _)) edits b0.val (by omega)
      (Finset.mem_map_of_mem _ hb0) helig hrad hsep hsize hlocs
    have hsub := geometryTerminals_extendTrace T (B.map (Function.Embedding.subtype _)) edits
      b0.val (by omega) (Finset.mem_map_of_mem _ hb0) helig hrad hsep hsize hlocs
    have hmet := (hunif m n₀ j (l + 1) u hNu hj.le hsched hu T').1 i.val i'.val
    have hanti := terminalDistance_antitone hconn hsub i.val i'.val
    have hexp : (-(103 / 100 : ℝ)) = (-1.03 : ℝ) := by norm_num
    rw [hexp]
    exact hmet.trans hanti
  · -- range geometry
    intro k ω hk _
    exact ⟨_, trial_exteriorGeometry q hconn (fun a : ActiveSite x => a.val) hemb
      (geometryTerminals T) (fun a b => J a b) (fun a b => hJs.apply b a) hJ1 hJadj d
      nnGraph_degree_le h0 cP hcP hr ht k ω hk⟩
  · -- resolvent decay
    intro k ω hk _ i i'
    have h := trial_resolvent_decay q hconn (fun a : ActiveSite x => a.val) hemb
      (geometryTerminals T) (fun a b => J a b) (fun a b => hJs.apply b a) hJ1 hJadj d
      nnGraph_degree_le h0 cP hcP hr ht ht1 k ω hk.le i i'
    refine h.trans ?_
    have hcoll : 0 ≤ coll k ω i i' := terminalDistance_nonneg _ _ _ _
    have hca : c ≤ a := min_le_left _ _
    apply mul_le_mul (div_le_div_of_nonneg_right hKc (Real.sqrt_nonneg _)) _ (Real.exp_pos _).le
      (by positivity)
    apply Real.exp_le_exp.mpr
    have : c * (stageScale u j m) * coll k ω i i' ≤ a * (stageScale u j m) * coll k ω i i' := by
      apply mul_le_mul_of_nonneg_right _ hcoll
      exact mul_le_mul_of_nonneg_right hca ht.le
    linarith

end AndersonAC.AgentS78Geo
