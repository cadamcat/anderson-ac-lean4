import AndersonAC.AgentS78.Construction.TileCoreA2

/-!
# monitor bounds transfer of the S45 increment table to the padded tile monitors

Step identities (the candidate step increments of the included prefix are the S45 single
deletion increments of the current live state), the padding/dilation operator facts, and
`tileMonitorBounds2_proof : ∀ d C, 1 ≤ C → TileMonitorBoundsStatement2 d C`.
-/

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources sourcesLaw signValue binarySuffix)
open Matrix

section StepIdentitiesAndTransfer

lemma sum_dite_mem_eq_coe {ι α : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid α]
    (S : Finset ι) (f : ∀ u ∈ S, α) :
    (∑ u : ι, if hu : u ∈ S then f u hu else 0) = ∑ u : S, f u.1 u.2 := by
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun u _ hu => dif_neg hu),
    ← Finset.sum_coe_sort S]
  exact Finset.sum_congr rfl fun u _ => dif_pos u.2

theorem restrictLive_self_ambient_eq {P_port : Type*} [Fintype P_port] [DecidableEq P_port]
    (a : S45.LiveState P_port) (r : P_port → ℂ) :
    ((a.restrictLive a.live).ambient (S45.restrictDamping a.live r)) = a.state r := by
  apply state_ext
  · ext u v
    have hu : u ∈ (a.restrictLive a.live).live :=
      (S45.LiveState.mem_restrictLive a.live a u).mpr u.2
    have hv : v ∈ (a.restrictLive a.live).live :=
      (S45.LiveState.mem_restrictLive a.live a v).mpr v.2
    change S45.mask (a.restrictLive a.live).live (a.restrictLive a.live).g u v = _
    simp only [S45.mask, S45.pad, hu, hv, ↓reduceDIte]
    rfl
  · ext u; rfl

theorem stepLive_state_eq_reindex {d m : ℕ}
    (t : ℝ) (r : Port d m → ℂ) (a : S45.LiveState (Port d m)) (p_cand : Port d m) (z : ℝ)
    (hal2 : p_cand ∈ a.live) :
    (stepLive t r a p_cand z).state r =
      AgentS45.State.reindex
        (stepLiveEquiv hal2 (rfl : (stepLive t r a p_cand z).live = a.live.erase p_cand))
        (S45.deleteState t (a.state r) ⟨p_cand, hal2⟩ z) := by
  apply state_ext
  · ext i j
    change (stepLive t r a p_cand z).g i.1 j.1 = _
    simp [stepLive, AgentS45.State.reindex, stepLiveEquiv, S45.deleteState, S45.LiveState.state,
      S45.restrict, S45.mask, S45.pad, Matrix.submatrix_apply, stepDen]
    have hi := Finset.mem_erase.mp (i.2 : i.1 ∈ a.live.erase p_cand)
    have hj := Finset.mem_erase.mp (j.2 : j.1 ∈ a.live.erase p_cand)
    rw [dif_pos ⟨hi.1, hi.2⟩, dif_pos ⟨hj.1, hj.2⟩]
    rfl
  · ext i; rfl

/-- The lag is invariant under reindexing (no invertibility needed). -/
theorem reindex_lag_a2 {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (s : S45.State ι) (t : ℝ) (i : κ) :
    (AgentS45.State.reindex e s).lag t i = s.lag t (e i) := by
  have hK : 1 - (AgentS45.State.reindex e s).K t = (1 - s.K t).submatrix e e := by
    rw [AgentS45.State.reindex_K]
    ext a b
    simp [Matrix.one_apply, e.injective.eq_iff]
  have hraw : (AgentS45.State.reindex e s).rawLag = s.rawLag ∘ e := rfl
  simp only [S45.State.lag, S45.State.P]
  rw [hK, Matrix.inv_submatrix_equiv, hraw, Matrix.submatrix_mulVec_equiv]
  simp [Function.comp_def]

theorem candidate_stepLag_eq {d m : ℕ} (P : TilePlan d m) (j : ℕ) (x : RunRecord d m)
    (q : S45.Sequence (Port d m)) (site : Torus d m) (z : ℝ)
    (hal2 : ((site, false) : Port d m) ∈ (q.state q.length).live) (u : Port d m) :
    let t := sweepScale P.u m j
    let r := portR (sweepTheta P.u m j) x.r
    let L_curr := (q.state q.length).live
    let sk := (q.state q.length).state r
    (candidate P j x q site z).stepLag t r q.length u =
      if hu : u ∈ L_curr then S45.lagInc t sk ⟨(site, false), hal2⟩ z ⟨u, hu⟩ else 0 := by
  classical
  dsimp only
  set t := sweepScale P.u m j
  set r := portR (sweepTheta P.u m j) x.r
  set a := q.state q.length
  set L_curr := a.live
  set sk := a.state r
  set p_cand : Port d m := (site, false)
  set b := stepLive t r a p_cand z
  have hb_live : b.live = L_curr.erase p_cand := rfl
  have hc_k : (candidate P j x q site z).state q.length = a := by
    simp [candidate, extendSeq, a]
  have hc_succ : (candidate P j x q site z).state (q.length + 1) = b := by
    simp [candidate, extendSeq, b, a, p_cand, t, r]
  unfold S45.Sequence.stepLag
  rw [hc_k, hc_succ]
  by_cases hu : u ∈ L_curr
  · rw [dif_pos hu]
    by_cases hup : u = p_cand
    · have hub : u ∉ b.live := by rw [hb_live, hup]; exact Finset.notMem_erase _ _
      have hus : (⟨u, hu⟩ : L_curr) ∉ S45.survivors ⟨p_cand, hal2⟩ := by
        simp [S45.survivors, Subtype.ext_iff, hup]
      simp [hub, S45.lagInc, hus]
      intro h
      exact absurd h hus
    · have hub : u ∈ b.live := by rw [hb_live]; exact Finset.mem_erase.mpr ⟨hup, hu⟩
      have hus : (⟨u, hu⟩ : L_curr) ∈ S45.survivors ⟨p_cand, hal2⟩ := by
        simp [S45.survivors, Subtype.ext_iff, hup]
      have hlag : (b.state r).lag t ⟨u, hub⟩ =
          (S45.deleteState t sk ⟨p_cand, hal2⟩ z).lag t ⟨⟨u, hu⟩, hus⟩ := by
        have hre := stepLive_state_eq_reindex t r a p_cand z hal2
        rw [hre]
        exact reindex_lag_a2 (stepLiveEquiv hal2 hb_live)
          (S45.deleteState t sk ⟨p_cand, hal2⟩ z) t ⟨u, hub⟩
      simp only [hub, ↓reduceIte, S45.LiveState.ambientLag, S45.lagInc]
      split_ifs with h1 h2
      all_goals first
        | (exact absurd hu h1)
        | (exact absurd hus h2)
        | (exact congrArg₂ (· - ·) hlag rfl)
  · rw [dif_neg hu]
    have hub : u ∉ b.live := fun h => hu (Finset.mem_of_mem_erase (hb_live ▸ h))
    simp [hub]

lemma sqrt_mul_schur_sub (s g_uv c g_ux g_xv d_den : ℂ) (hs : s ≠ 0) :
    s * (g_uv - c * g_ux * g_xv / d_den) =
      s * g_uv - (c / (s * d_den)) * (s * g_ux) * (s * g_xv) := by
  by_cases hd : d_den = 0
  · simp [hd]
  · field_simp [hs, hd]

theorem candidate_stepRow_eq {d m : ℕ} (P : TilePlan d m) (j : ℕ) (x : RunRecord d m)
    (q : S45.Sequence (Port d m)) (site : Torus d m) (z : ℝ)
    (htpos : 0 < sweepScale P.u m j)
    (hal2 : ((site, false) : Port d m) ∈ (q.state q.length).live)
    (cols : Finset (Port d m)) (u : Port d m) :
    let t := sweepScale P.u m j
    let r := portR (sweepTheta P.u m j) x.r
    let L_curr := (q.state q.length).live
    let sk := (q.state q.length).state r
    let cols_live : Finset L_curr := Finset.univ.filter (fun v : L_curr => v.1 ∈ cols)
    (candidate P j x q site z).stepRow t r cols q.length u =
      if hu : u ∈ L_curr then
        S45.fourthProxy t sk cols_live ⟨u, hu⟩ ⟨(site, false), hal2⟩ z / S45.rowCap t
      else 0 := by
  classical
  dsimp only
  set t := sweepScale P.u m j
  set r := portR (sweepTheta P.u m j) x.r
  set a := q.state q.length
  set L_curr := a.live
  set sk := a.state r
  set p_cand : Port d m := (site, false)
  set p_live : L_curr := ⟨p_cand, hal2⟩
  set b := stepLive t r a p_cand z
  set cols_live : Finset L_curr := Finset.univ.filter (fun v : L_curr => v.1 ∈ cols)
  have hb_live : b.live = L_curr.erase p_cand := rfl
  have hc_k : (candidate P j x q site z).state q.length = a := by
    simp [candidate, extendSeq, a]
  have hc_succ : (candidate P j x q site z).state (q.length + 1) = b := by
    simp [candidate, extendSeq, b, a, p_cand, t, r]
  unfold S45.Sequence.stepRow
  rw [hc_k, hc_succ]
  by_cases hu : u ∈ L_curr
  · rw [dif_pos hu]
    by_cases hup : u = p_cand
    · have hub : u ∉ b.live := by rw [hb_live, hup]; exact Finset.notMem_erase _ _
      have hu_eq : (⟨u, hu⟩ : L_curr) = p_live := Subtype.ext hup
      simp [hub, S45.fourthProxy, hu_eq]
    · have hub : u ∈ b.live := by rw [hb_live]; exact Finset.mem_erase.mpr ⟨hup, hu⟩
      have hu_ne : (⟨u, hu⟩ : L_curr) ≠ p_live := fun h => hup (congrArg Subtype.val h)
      simp only [hub, ↓reduceIte, S45.fourthProxy, hu_ne]
      congr 1
      have hmap : cols ∩ b.live = (cols_live.erase p_live).map ⟨Subtype.val, Subtype.val_injective⟩ := by
        ext v
        simp [cols_live, hb_live, p_live, Finset.mem_erase, Subtype.ext_iff,
          and_comm, and_left_comm, and_assoc]
      rw [hmap, Finset.sum_map]
      refine Finset.sum_congr rfl fun v hv => ?_
      have hvb : v.1 ∈ b.live := by
        rw [hb_live]
        exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hv).1 (Subtype.ext h), v.2⟩
      have hha : (a.ambient r).h t u v.1 = sk.h t ⟨u, hu⟩ v := by
        change (Real.sqrt t : ℂ) * S45.mask a.live a.g u v.1 = (Real.sqrt t : ℂ) * a.g u v.1
        rw [mask_apply, dif_pos (show u ∈ a.live from hu), dif_pos (show v.1 ∈ a.live from v.2)]
      have hhb : (b.ambient r).h t u v.1 =
          sk.h t ⟨u, hu⟩ v - S45.gamma t sk p_live z * sk.h t ⟨u, hu⟩ p_live * sk.h t p_live v := by
        have hs_ne : (Real.sqrt t : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr htpos)
        change (Real.sqrt t : ℂ) * (S45.mask b.live b.g u v.1) = _
        have hbg : S45.mask b.live b.g u v.1 =
            a.g u v.1 - ((z : ℂ) + t * r p_cand) * a.g u p_cand * a.g p_cand v.1 /
              (1 + ((z : ℂ) + t * r p_cand) * a.g p_cand p_cand) := by
          rw [mask_apply, dif_pos hub, dif_pos hvb]
          change S45.mask (a.live.erase p_cand) _ u v.1 = _
          have hu2 : u ∈ a.live.erase p_cand := hub
          have hv2 : v.1 ∈ a.live.erase p_cand := hvb
          simp only [S45.mask, S45.pad, hu2, hv2, ↓reduceDIte, S45.restrict,
            Matrix.submatrix_apply]
          rfl
        rw [hbg]
        exact sqrt_mul_schur_sub (Real.sqrt t : ℂ) (a.g u v.1)
          ((z : ℂ) + t * r p_cand) (a.g u p_cand) (a.g p_cand v.1)
          (1 + ((z : ℂ) + t * r p_cand) * a.g p_cand p_cand) hs_ne
      change ‖S45.State.h t (b.ambient r) u v.1‖ ^ 4 - ‖S45.State.h t (a.ambient r) u v.1‖ ^ 4 = _
      rw [hha, hhb]
  · rw [dif_neg hu]
    have hub : u ∉ b.live := fun h => hu (Finset.mem_of_mem_erase (hb_live ▸ h))
    simp [hub]

theorem candidate_stepJ_eq {d m : ℕ} (P : TilePlan d m) (j : ℕ) (x : RunRecord d m)
    (q : S45.Sequence (Port d m)) (site : Torus d m) (z : ℝ)
    (hal2 : ((site, false) : Port d m) ∈ (q.state q.length).live) :
    let t := sweepScale P.u m j
    let r := portR (sweepTheta P.u m j) x.r
    let L_curr := (q.state q.length).live
    let sk := (q.state q.length).state r
    (candidate P j x q site z).stepJ t r q.length =
      S45.pad L_curr (S45.Jinc t sk ⟨(site, false), hal2⟩ z) := by
  classical
  dsimp only
  set t := sweepScale P.u m j
  set r := portR (sweepTheta P.u m j) x.r
  set c := candidate P j x q site z
  set a := q.state q.length
  set L_curr := a.live
  set sk := a.state r
  set p_cand : Port d m := (site, false)
  set p_live : L_curr := ⟨p_cand, hal2⟩
  set b := stepLive t r a p_cand z
  have hb_live : b.live = L_curr.erase p_cand := rfl
  have hc_piv : c.pivot q.length = some p_cand := by simp [c, candidate, extendSeq, p_cand]
  have hc_sc : c.scalar q.length = z := by simp [c, candidate, extendSeq]
  have hc_k : c.state q.length = a := by simp [c, candidate, extendSeq, a]
  have hc_succ : c.state (q.length + 1) = b := by simp [c, candidate, extendSeq, b, a, p_cand, t, r]
  have hJinc := S45.Sequence.Jinc_restrictLive q L_curr t r q.length p_cand hal2 z
  have hamb : (((q.restrictLive L_curr).state q.length).ambient
      (S45.restrictDamping L_curr r)) = sk := by
    change ((a.restrictLive a.live).ambient (S45.restrictDamping a.live r)) = a.state r
    exact restrictLive_self_ambient_eq a r
  rw [hamb] at hJinc
  ext u v
  unfold S45.Sequence.stepJ
  rw [hc_piv, hc_sc, hc_k, hc_succ]
  dsimp only
  rw [mask_apply, S45_pad_apply]
  by_cases huv : u ∈ L_curr ∧ v ∈ L_curr
  · rw [dif_pos huv]
    have hentry : S45.Jinc t (a.ambient r) p_cand z u v =
        S45.Jinc t sk p_live z ⟨u, huv.1⟩ ⟨v, huv.2⟩ :=
      congrFun (congrFun hJinc ⟨u, huv.1⟩) ⟨v, huv.2⟩
    rw [← hentry]
    by_cases hub : u ∈ b.live
    · by_cases hvb : v ∈ b.live
      · rw [dif_pos hub, dif_pos hvb]
      · rw [dif_pos hub, dif_neg hvb]
        have hvp : v = p_cand := by
          by_contra hne
          exact hvb (Finset.mem_erase.mpr ⟨hne, huv.2⟩)
        rw [hvp]
        simp [S45.Jinc, S45.pad, S45.survivors]
    · rw [dif_neg hub]
      have hup : u = p_cand := by
        by_contra hne
        exact hub (Finset.mem_erase.mpr ⟨hne, huv.1⟩)
      rw [hup]
      simp [S45.Jinc, S45.pad, S45.survivors]
  · rw [dif_neg huv]
    by_cases hub : u ∈ b.live
    · have hvb : v ∉ b.live := fun hvb =>
        huv ⟨Finset.mem_of_mem_erase (hub : u ∈ a.live.erase p_cand),
          Finset.mem_of_mem_erase (hvb : v ∈ a.live.erase p_cand)⟩
      rw [dif_pos hub, dif_neg hvb]
    · rw [dif_neg hub]

theorem Linc_row_sum_a2 {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℝ) (s : S45.State ι)
    (x : ι) (ξ : ℝ) : S45.Linc t s x ξ *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  ext i
  have h := AgentS45.pad_row_sum (S45.survivors x) (S45.laplacian (S45.Ledge t s x ξ))
    (fun i => AgentS45.laplacian_row_sum _ i) i
  simpa [Matrix.mulVec, dotProduct, S45.Linc] using h

theorem Linc_ambient_offDiag_a2 {P_port : Type*} [Fintype P_port] [DecidableEq P_port]
    (q : S45.Sequence P_port) (S : Finset P_port) (t : ℝ) (r : P_port → ℂ) (k : ℕ)
    (x : P_port) (hxS : x ∈ S) (ξ : ℝ) (a b : S) (hab : a ≠ b) :
    S45.Linc t ((q.state k).ambient r) x ξ a.1 b.1 =
      S45.Linc t (((q.restrictLive S).state k).ambient (S45.restrictDamping S r)) ⟨x, hxS⟩ ξ a b := by
  have hab1 : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
  by_cases hpa : a.1 ∈ S45.survivors x
  · have hpa' : a ∈ S45.survivors ⟨x, hxS⟩ :=
      (S45.Sequence.surv_mem_restrictLive S x hxS a).mpr hpa
    by_cases hpb : b.1 ∈ S45.survivors x
    · have hpb' : b ∈ S45.survivors ⟨x, hxS⟩ :=
        (S45.Sequence.surv_mem_restrictLive S x hxS b).mpr hpb
      have hne1 : (⟨a.1, hpa⟩ : S45.survivors x) ≠ ⟨b.1, hpb⟩ :=
        fun h => hab1 (Subtype.mk.inj h)
      have hne2 : (⟨a, hpa'⟩ : S45.survivors ⟨x, hxS⟩) ≠ ⟨b, hpb'⟩ :=
        fun h => hab (Subtype.mk.inj h)
      simp only [S45.Linc, S45.pad, hpa, hpb, hpa', hpb', ↓reduceDIte,
        S45.laplacian, hne1, hne2, ↓reduceIte, neg_inj]
      have hγ := S45.Sequence.gamma_restrictLive q S t r k x hxS ξ
      have hh_ab := S45.LiveState.ambient_h_restrictLive S (q.state k) r t a b
      have hh_ax := S45.LiveState.ambient_h_restrictLive S (q.state k) r t a ⟨x, hxS⟩
      have hh_xb := S45.LiveState.ambient_h_restrictLive S (q.state k) r t ⟨x, hxS⟩ b
      have hF_ax := S45.LiveState.ambient_F_restrictLive S (q.state k) r t a ⟨x, hxS⟩
      have hF_xb := S45.LiveState.ambient_F_restrictLive S (q.state k) r t ⟨x, hxS⟩ b
      have hF_xx := S45.LiveState.ambient_F_restrictLive S (q.state k) r t ⟨x, hxS⟩ ⟨x, hxS⟩
      have hq_xx : (((q.state k).restrictLive S).ambient (S45.restrictDamping S r)).q ⟨x, hxS⟩ =
          ((q.state k).ambient r).q x := by
        change ((((q.state k).restrictLive S).ambient (S45.restrictDamping S r)).g ⟨x, hxS⟩
          ⟨x, hxS⟩).im = (((q.state k).ambient r).g x x).im
        rw [S45.LiveState.restrictLive_ambient_g S (q.state k) r ⟨x, hxS⟩ ⟨x, hxS⟩]
      rw [S45.Sequence.restrictLive_state_eq S q k] at hγ ⊢
      simp only [S45.Ledge, S45.LiveState.ambient_p_restrictLive,
        hγ, hh_ab, hh_ax, hh_xb, hF_ax, hF_xb, hF_xx, hq_xx]
    · have hpb' : b ∉ S45.survivors ⟨x, hxS⟩ :=
        fun h => hpb ((S45.Sequence.surv_mem_restrictLive S x hxS b).mp h)
      simp [S45.Linc, S45.pad, hpa, hpb, hpa', hpb']
  · have hpa' : a ∉ S45.survivors ⟨x, hxS⟩ :=
      fun h => hpa ((S45.Sequence.surv_mem_restrictLive S x hxS a).mp h)
    simp [S45.Linc, S45.pad, hpa, hpa']

theorem pad_mulVec_one_eq_zero {P_port : Type*} [Fintype P_port] [DecidableEq P_port]
    (S : Finset P_port) (A : S45.RMat S) (hA : A *ᵥ (fun _ => (1 : ℝ)) = 0) :
    S45.pad S A *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  ext u
  simp only [Matrix.mulVec, dotProduct, mul_one, Pi.zero_apply, S45.pad]
  by_cases hu : u ∈ S
  · simp only [hu, ↓reduceDIte]
    rw [sum_dite_mem_eq_coe S (fun v hv => A ⟨u, hu⟩ ⟨v, hv⟩)]
    have h := congrFun hA ⟨u, hu⟩
    simpa [Matrix.mulVec, dotProduct] using h
  · simp [hu]

theorem candidate_stepL_eq {d m : ℕ} (P : TilePlan d m) (j : ℕ) (x : RunRecord d m)
    (q : S45.Sequence (Port d m)) (site : Torus d m) (z : ℝ)
    (hal2 : ((site, false) : Port d m) ∈ (q.state q.length).live) :
    let t := sweepScale P.u m j
    let r := portR (sweepTheta P.u m j) x.r
    let L_curr := (q.state q.length).live
    let sk := (q.state q.length).state r
    (candidate P j x q site z).stepL t r q.length =
      S45.pad L_curr (S45.Linc t sk ⟨(site, false), hal2⟩ z) := by
  classical
  dsimp only
  set t := sweepScale P.u m j
  set r := portR (sweepTheta P.u m j) x.r
  set c := candidate P j x q site z
  set a := q.state q.length
  set L_curr := a.live
  set sk := a.state r
  set p_cand : Port d m := (site, false)
  set p_live : L_curr := ⟨p_cand, hal2⟩
  set b := stepLive t r a p_cand z
  have hb_live : b.live = L_curr.erase p_cand := rfl
  have hc_piv : c.pivot q.length = some p_cand := by simp [c, candidate, extendSeq, p_cand]
  have hc_sc : c.scalar q.length = z := by simp [c, candidate, extendSeq]
  have hc_k : c.state q.length = a := by simp [c, candidate, extendSeq, a]
  have hc_succ : c.state (q.length + 1) = b := by simp [c, candidate, extendSeq, b, a, p_cand, t, r]
  have hmul2 : S45.pad L_curr (S45.Linc t sk p_live z) *ᵥ (fun _ => (1 : ℝ)) = 0 :=
    pad_mulVec_one_eq_zero L_curr _ (Linc_row_sum_a2 t sk p_live z)
  have hmul1 : c.stepL t r q.length *ᵥ (fun _ => (1 : ℝ)) = 0 := by
    ext u
    simp only [Matrix.mulVec, dotProduct, mul_one, Pi.zero_apply, S45.Sequence.stepL,
      hc_piv, hc_sc, hc_k, hc_succ]
    by_cases hub : u ∈ b.live
    · have hrow_amb := congrFun (Linc_row_sum_a2 t (a.ambient r) p_cand z) u
      simp only [Matrix.mulVec, dotProduct, mul_one, Pi.zero_apply] at hrow_amb
      rw [← hrow_amb]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hvb : v ∈ b.live
      · simp [S45.mask, S45.pad, S45.restrict, hub, hvb]
      · simp only [S45.mask, S45.pad, hub, hvb, ↓reduceDIte]
        have hu_er : u ∈ L_curr.erase p_cand := hb_live ▸ hub
        have hu_surv : u ∈ S45.survivors p_cand := by
          simp [S45.survivors, (Finset.mem_erase.mp hu_er).1]
        by_cases hvp : v = p_cand
        · subst hvp
          simp [S45.Linc, S45.pad, S45.survivors]
        · have hv_surv : v ∈ S45.survivors p_cand := by simp [S45.survivors, hvp]
          have hv_nL : v ∉ L_curr := fun hvL => hvb (hb_live ▸ Finset.mem_erase.mpr ⟨hvp, hvL⟩)
          have hne_uv : (⟨u, hu_surv⟩ : S45.survivors p_cand) ≠ ⟨v, hv_surv⟩ :=
            fun h => hv_nL (by
              have huv' : u = v := congrArg Subtype.val h
              rw [← huv']
              exact (Finset.mem_erase.mp hu_er).2)
          have hv_nL' : v ∉ a.live := hv_nL
          have hh_zero : ∀ w : Port d m, (a.ambient r).h t w v = 0 := fun w => by
            simp [S45.LiveState.ambient, S45.State.h, S45.mask, S45.pad, S45.restrict, hv_nL']
          have hF_zero : (a.ambient r).F t p_cand v = 0 := by
            simp [S45.State.F, S45.entryAbsSquare, hh_zero p_cand]
          simp [S45.Linc, S45.pad, hu_surv, hv_surv, S45.laplacian, hne_uv, S45.Ledge,
            hh_zero u, hh_zero p_cand, hF_zero]
    · simp [S45.mask, S45.pad, hub]
  have hamb : (((q.restrictLive L_curr).state q.length).ambient
      (S45.restrictDamping L_curr r)) = sk := by
    change ((a.restrictLive a.live).ambient (S45.restrictDamping a.live r)) = a.state r
    exact restrictLive_self_ambient_eq a r
  refine matrix_eq_of_offDiag_and_mulVec_one _ _ hmul1 hmul2 (fun u v huv => ?_)
  unfold S45.Sequence.stepL
  rw [hc_piv, hc_sc, hc_k, hc_succ]
  dsimp only
  rw [mask_apply, S45_pad_apply]
  by_cases huvL : u ∈ L_curr ∧ v ∈ L_curr
  · rw [dif_pos huvL]
    have hoff := Linc_ambient_offDiag_a2 q L_curr t r q.length p_cand hal2 z ⟨u, huvL.1⟩
      ⟨v, huvL.2⟩ (fun h => huv (congrArg Subtype.val h))
    rw [hamb] at hoff
    have hentry : S45.Linc t (a.ambient r) p_cand z u v =
        S45.Linc t sk p_live z ⟨u, huvL.1⟩ ⟨v, huvL.2⟩ := hoff
    rw [← hentry]
    by_cases hub : u ∈ b.live
    · by_cases hvb : v ∈ b.live
      · rw [dif_pos hub, dif_pos hvb]
      · rw [dif_pos hub, dif_neg hvb]
        have hvp : v = p_cand := by
          by_contra hne
          exact hvb (Finset.mem_erase.mpr ⟨hne, huvL.2⟩)
        rw [hvp]
        simp [S45.Linc, S45.pad, S45.survivors]
    · rw [dif_neg hub]
      have hup : u = p_cand := by
        by_contra hne
        exact hub (Finset.mem_erase.mpr ⟨hne, huvL.1⟩)
      rw [hup]
      simp [S45.Linc, S45.pad, S45.survivors]
  · rw [dif_neg huvL]
    by_cases hub : u ∈ b.live
    · have hvb : v ∉ b.live := fun hvb =>
        huvL ⟨Finset.mem_of_mem_erase (hub : u ∈ a.live.erase p_cand),
          Finset.mem_of_mem_erase (hvb : v ∈ a.live.erase p_cand)⟩
      rw [dif_pos hub, dif_neg hvb]
    · rw [dif_neg hub]

theorem pullback_pad {P_port H : Type*} [Fintype P_port] [DecidableEq P_port] [Fintype H]
    (S : Finset P_port) (B : Matrix P_port H ℝ) (M : S45.RMat S) :
    S45.pullback B (S45.pad S M) = S45.pullback (fun a : S => fun j => B a.1 j) M := by
  ext j1 j2
  simp only [S45.pullback, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∀ u : P_port,
      (∑ v : P_port, B v j1 * S45.pad S M v u) * B u j2 =
        if hu : u ∈ S then (∑ v : S, B v.1 j1 * M v ⟨u, hu⟩) * B u j2 else 0 := by
    intro u
    by_cases hu : u ∈ S
    · rw [dif_pos hu]
      congr 1
      have h2 : (fun v : P_port => B v j1 * S45.pad S M v u) =
          (fun v : P_port => if hv : v ∈ S then B v j1 * M ⟨v, hv⟩ ⟨u, hu⟩ else 0) := by
        funext v
        by_cases hv : v ∈ S <;> simp [S45.pad, hu, hv]
      rw [h2, sum_dite_mem_eq_coe S (fun v hv => B v j1 * M ⟨v, hv⟩ ⟨u, hu⟩)]
    · rw [dif_neg hu]
      have h0 : (∑ v : P_port, B v j1 * S45.pad S M v u) = 0 := by
        refine Finset.sum_eq_zero fun v _ => ?_
        by_cases hv : v ∈ S <;> simp [S45.pad, hu, hv]
      rw [h0, zero_mul]
  simp only [h1]
  exact sum_dite_mem_eq_coe S (fun u hu => (∑ v : S, B v.1 j1 * M v ⟨u, hu⟩) * B u j2)

/-! ### Padding, compression, and dilation algebra -/

theorem padInto_eq_inclMat_mul {α : Type} [Fintype α] [DecidableEq α]
    (D : ℕ) (e : α → Fin D) (he : Function.Injective e) (A : S45.CMat α) :
    padInto D e A = inclMat e * A * (inclMat e)ᴴ := by
  have hsupp : ∀ a b, (∀ x, e x ≠ a) ∨ (∀ x, e x ≠ b) → padInto D e A a b = 0 := by
    intro a b h; rcases h with h | h <;> simp [padInto, h]
  have hpad := inclMat_pad e he (padInto D e A) hsupp
  rw [padInto_submatrix D e he A] at hpad
  exact hpad.symm

theorem padInto_sq {α : Type} [Fintype α] [DecidableEq α]
    (D : ℕ) (e : α → Fin D) (he : Function.Injective e) (A : S45.CMat α) :
    (padInto D e A) ^ 2 = padInto D e (A ^ 2) := by
  rw [sq, sq, padInto_eq_inclMat_mul D e he A, padInto_eq_inclMat_mul D e he (A * A)]
  calc (inclMat e * A * (inclMat e)ᴴ) * (inclMat e * A * (inclMat e)ᴴ)
      = inclMat e * A * ((inclMat e)ᴴ * inclMat e) * A * (inclMat e)ᴴ := by
        simp only [Matrix.mul_assoc]
    _ = inclMat e * (A * A) * (inclMat e)ᴴ := by
        rw [inclMat_conj_mul e he, Matrix.mul_one]
        simp only [Matrix.mul_assoc]

theorem padInto_sum {α ι : Type} [Fintype α] [DecidableEq α]
    (D : ℕ) (e : α → Fin D) (s : Finset ι) (f : ι → S45.CMat α) :
    padInto D e (∑ i ∈ s, f i) = ∑ i ∈ s, padInto D e (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [padInto_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, padInto_add, ih]

theorem inclMat_mul_conjTranspose_le_one {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (f : κ → ι) (hf : Function.Injective f) :
    inclMat f * (inclMat f)ᴴ ≤ (1 : Matrix ι ι ℂ) := by
  rw [Matrix.le_iff]
  set P := inclMat f * (inclMat f)ᴴ
  have hPH : Pᴴ = P := by
    dsimp [P]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hP2 : P * P = P := by
    dsimp [P]
    calc (inclMat f * (inclMat f)ᴴ) * (inclMat f * (inclMat f)ᴴ)
        = inclMat f * ((inclMat f)ᴴ * inclMat f) * (inclMat f)ᴴ := by simp only [Matrix.mul_assoc]
      _ = P := by rw [inclMat_conj_mul f hf, Matrix.mul_one]
  have hproj : (1 - P)ᴴ * (1 - P) = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
    calc (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP2]; abel
  rw [← hproj]
  exact Matrix.posSemidef_conjTranspose_mul_self (1 - P)

theorem padInto_le_smul_one {α : Type} [Fintype α] [DecidableEq α]
    (D : ℕ) (e : α → Fin D) (he : Function.Injective e)
    {A : S45.CMat α} {R : ℝ} (hR : 0 ≤ R) (hA : A ≤ R • (1 : S45.CMat α)) :
    padInto D e A ≤ R • (1 : S45.CMat (Fin D)) := by
  rw [padInto_eq_inclMat_mul D e he A]
  have h1 : inclMat e * A * (inclMat e)ᴴ ≤ R • (inclMat e * (inclMat e)ᴴ) := by
    rw [Matrix.le_iff] at hA ⊢
    have hconj := hA.conjTranspose_mul_mul_same (inclMat e)ᴴ
    have heq : ((inclMat e)ᴴ)ᴴ * (R • (1 : S45.CMat α) - A) * (inclMat e)ᴴ =
        R • (inclMat e * (inclMat e)ᴴ) - inclMat e * A * (inclMat e)ᴴ := by
      rw [Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    rwa [heq] at hconj
  have h2 : R • (inclMat e * (inclMat e)ᴴ) ≤ R • (1 : S45.CMat (Fin D)) :=
    smul_le_smul_of_nonneg_left (inclMat_mul_conjTranspose_le_one e he) hR
  exact h1.trans h2

abbrev compressJ {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (L_curr : Finset (Port d m)) (A : S45.CMat L_curr) : S45.CMat (innerPorts P j T) :=
  S45.restrict (S45.pad L_curr A) (innerPorts P j T)

theorem pad_eq_inclMat_mul {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (A : S45.CMat S) :
    S45.pad S A = inclMat (Subtype.val : S → ι) * A * (inclMat (Subtype.val : S → ι))ᴴ := by
  have hsupp : ∀ i j : ι, (∀ k : S, k.1 ≠ i) ∨ (∀ k : S, k.1 ≠ j) → S45.pad S A i j = 0 := by
    intro i j h
    rcases h with h | h
    · have hi : i ∉ S := fun hi => h ⟨i, hi⟩ rfl
      simp [S45.pad, hi]
    · have hj : j ∉ S := fun hj => h ⟨j, hj⟩ rfl
      simp [S45.pad, hj]
  have hsub : (S45.pad S A).submatrix (Subtype.val : S → ι) Subtype.val = A := by
    ext a b; simp [S45.pad, a.2, b.2]
  have hpad := inclMat_pad (Subtype.val : S → ι) Subtype.val_injective (S45.pad S A) hsupp
  rw [hsub] at hpad
  exact hpad.symm

theorem compressJ_norm_le {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (L_curr : Finset (Port d m)) (A : S45.CMat L_curr) :
    ‖compressJ P j T L_curr A‖ ≤ ‖A‖ := by
  have h1 : ‖compressJ P j T L_curr A‖ ≤ ‖S45.pad L_curr A‖ :=
    submatrix_norm_le (Subtype.val : innerPorts P j T → Port d m) Subtype.val_injective _
  have hsupp : ∀ i j : Port d m, (∀ k : L_curr, k.1 ≠ i) ∨ (∀ k : L_curr, k.1 ≠ j) →
      S45.pad L_curr A i j = 0 := by
    intro i j h
    rcases h with h | h
    · have hi : i ∉ L_curr := fun hi => h ⟨i, hi⟩ rfl
      simp [S45.pad, hi]
    · have hj : j ∉ L_curr := fun hj => h ⟨j, hj⟩ rfl
      simp [S45.pad, hj]
  have hsub : (S45.pad L_curr A).submatrix (Subtype.val : L_curr → Port d m) Subtype.val = A := by
    ext a b; simp [S45.pad, a.2, b.2]
  have h2 := norm_submatrix_of_support (Subtype.val : L_curr → Port d m) Subtype.val_injective
    (S45.pad L_curr A) hsupp
  rw [hsub] at h2
  exact h1.trans h2.symm.le

theorem compressJ_add {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (L_curr : Finset (Port d m)) (A B : S45.CMat L_curr) :
    compressJ P j T L_curr (A + B) = compressJ P j T L_curr A + compressJ P j T L_curr B := by
  ext a b
  simp only [compressJ, S45.restrict, Matrix.submatrix_apply, Matrix.add_apply, S45.pad]
  split_ifs <;> simp

theorem compressJ_zero {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (L_curr : Finset (Port d m)) :
    compressJ P j T L_curr 0 = 0 := by
  ext a b
  simp only [compressJ, S45.restrict, Matrix.submatrix_apply, Matrix.zero_apply, S45.pad]
  split_ifs <;> rfl

theorem compressJ_sum {d m : ℕ} {ι : Type*} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (L_curr : Finset (Port d m))
    (s : Finset ι) (f : ι → S45.CMat L_curr) :
    compressJ P j T L_curr (∑ i ∈ s, f i) = ∑ i ∈ s, compressJ P j T L_curr (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [compressJ_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, compressJ_add, ih]

theorem compressJ_le_smul_one {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (L_curr : Finset (Port d m)) {A : S45.CMat L_curr} {R : ℝ}
    (hR : 0 ≤ R) (hA : A ≤ R • (1 : S45.CMat L_curr)) :
    compressJ P j T L_curr A ≤ R • (1 : S45.CMat (innerPorts P j T)) := by
  have hpad : S45.pad L_curr A ≤ R • (1 : S45.CMat (Port d m)) := by
    rw [pad_eq_inclMat_mul L_curr A]
    have h1 : inclMat (Subtype.val : L_curr → Port d m) * A *
        (inclMat (Subtype.val : L_curr → Port d m))ᴴ ≤
        R • (inclMat (Subtype.val : L_curr → Port d m) *
          (inclMat (Subtype.val : L_curr → Port d m))ᴴ) := by
      rw [Matrix.le_iff] at hA ⊢
      have hconj := hA.conjTranspose_mul_mul_same (inclMat (Subtype.val : L_curr → Port d m))ᴴ
      have heq : ((inclMat (Subtype.val : L_curr → Port d m))ᴴ)ᴴ *
          (R • (1 : S45.CMat L_curr) - A) * (inclMat (Subtype.val : L_curr → Port d m))ᴴ =
          R • (inclMat (Subtype.val : L_curr → Port d m) *
            (inclMat (Subtype.val : L_curr → Port d m))ᴴ) -
            inclMat (Subtype.val : L_curr → Port d m) * A *
              (inclMat (Subtype.val : L_curr → Port d m))ᴴ := by
        rw [Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul,
          Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      rwa [heq] at hconj
    exact h1.trans (smul_le_smul_of_nonneg_left
      (inclMat_mul_conjTranspose_le_one Subtype.val Subtype.val_injective) hR)
  unfold compressJ S45.restrict
  rw [← inclMat_block (Subtype.val : innerPorts P j T → Port d m) (S45.pad L_curr A)]
  rw [Matrix.le_iff] at hpad ⊢
  have hconj := hpad.conjTranspose_mul_mul_same (inclMat (Subtype.val : innerPorts P j T → Port d m))
  have heq : (inclMat (Subtype.val : innerPorts P j T → Port d m))ᴴ *
      (R • (1 : S45.CMat (Port d m)) - S45.pad L_curr A) *
      inclMat (Subtype.val : innerPorts P j T → Port d m) =
      R • (1 : S45.CMat (innerPorts P j T)) -
        (inclMat (Subtype.val : innerPorts P j T → Port d m))ᴴ * S45.pad L_curr A *
          inclMat (Subtype.val : innerPorts P j T → Port d m) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      inclMat_conj_mul Subtype.val Subtype.val_injective]
  rwa [heq] at hconj

theorem submatrix_mul_conjTranspose_le {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (f : κ → ι) (hf : Function.Injective f) (M : Matrix ι ι ℂ) :
    (M.submatrix f f) * (M.submatrix f f)ᴴ ≤ (M * Mᴴ).submatrix f f := by
  rw [← inclMat_block f M, ← inclMat_block f (M * Mᴴ), Matrix.le_iff]
  set E := inclMat f
  have hdiff : Eᴴ * (M * Mᴴ) * E - (Eᴴ * M * E) * (Eᴴ * M * E)ᴴ =
      (Mᴴ * E)ᴴ * (1 - E * Eᴴ) * (Mᴴ * E) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [hdiff]
  exact (Matrix.le_iff.mp (inclMat_mul_conjTranspose_le_one f hf)).conjTranspose_mul_mul_same (Mᴴ * E)

theorem compressJ_mul_conjTranspose_le {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (L_curr : Finset (Port d m)) (A : S45.CMat L_curr) :
    (compressJ P j T L_curr A) * (compressJ P j T L_curr A)ᴴ ≤
      compressJ P j T L_curr (A * Aᴴ) := by
  have hpad : (S45.pad L_curr A) * (S45.pad L_curr A)ᴴ = S45.pad L_curr (A * Aᴴ) := by
    rw [pad_eq_inclMat_mul L_curr A, pad_eq_inclMat_mul L_curr (A * Aᴴ)]
    set E := inclMat (Subtype.val : L_curr → Port d m)
    have hEH : (E * A * Eᴴ)ᴴ = E * Aᴴ * Eᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [hEH]
    calc (E * A * Eᴴ) * (E * Aᴴ * Eᴴ)
        = E * A * (Eᴴ * E) * Aᴴ * Eᴴ := by simp only [Matrix.mul_assoc]
      _ = E * (A * Aᴴ) * Eᴴ := by
          rw [inclMat_conj_mul Subtype.val Subtype.val_injective, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  unfold compressJ S45.restrict
  rw [← hpad]
  exact submatrix_mul_conjTranspose_le Subtype.val Subtype.val_injective (S45.pad L_curr A)

theorem compressJ_conjTranspose_mul_le {d m : ℕ} (P : TilePlan d m) (j : ℕ)
    (T : Fin (P.cover j).cover.count) (L_curr : Finset (Port d m)) (A : S45.CMat L_curr) :
    (compressJ P j T L_curr A)ᴴ * (compressJ P j T L_curr A) ≤
      compressJ P j T L_curr (Aᴴ * A) := by
  have hconj : (compressJ P j T L_curr A)ᴴ = compressJ P j T L_curr Aᴴ := by
    ext a b
    simp only [compressJ, S45.restrict, Matrix.conjTranspose_apply, Matrix.submatrix_apply, S45.pad]
    split_ifs <;> simp
  have h := compressJ_mul_conjTranspose_le P j T L_curr Aᴴ
  rw [Matrix.conjTranspose_conjTranspose, ← hconj, Matrix.conjTranspose_conjTranspose] at h
  exact h

theorem posSemidef_map_ofReal {H : Type*} [Fintype H] [DecidableEq H]
    {M : S45.RMat H} (hM : M.PosSemidef) :
    (M.map (fun a : ℝ => (a : ℂ))).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hM ⊢
  obtain ⟨hH, hpos⟩ := hM
  have hsym : ∀ i j, M j i = M i j := fun i j => by
    have := congrFun (congrFun hH i) j
    simpa [Matrix.conjTranspose_apply] using this
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    simp [Matrix.conjTranspose_apply, hsym]
  · set u : H → ℝ := fun i => (x i).re
    set v : H → ℝ := fun i => (x i).im
    have hu := hpos u
    have hv := hpos v
    simp only [star_trivial] at hu hv
    have hre : (star x ⬝ᵥ (M.map (fun a : ℝ => (a : ℂ)) *ᵥ x)).re =
        u ⬝ᵥ (M *ᵥ u) + v ⬝ᵥ (M *ᵥ v) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Complex.re_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.star_apply, Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, u, v]
      ring
    have him : (star x ⬝ᵥ (M.map (fun a : ℝ => (a : ℂ)) *ᵥ x)).im = 0 := by
      have hexp : (star x ⬝ᵥ (M.map (fun a : ℝ => (a : ℂ)) *ᵥ x)).im =
          ∑ i, ∑ j, M i j * ((x i).re * (x j).im - (x i).im * (x j).re) := by
        simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Complex.im_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [Pi.star_apply, Complex.star_def, Complex.mul_im, Complex.mul_re,
          Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
        ring
      rw [hexp]
      have h2 : (∑ i, ∑ j, M i j * ((x i).re * (x j).im - (x i).im * (x j).re)) =
          -∑ i, ∑ j, M i j * ((x i).re * (x j).im - (x i).im * (x j).re) := by
        conv_lhs => rw [Finset.sum_comm]
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hsym]
        ring
      linarith
    rw [Complex.nonneg_iff]
    exact ⟨by rw [hre]; exact add_nonneg hu hv, him.symm⟩

theorem real_sq_sum_le_complex {H ι : Type*} [Fintype H] [DecidableEq H]
    (s : Finset ι) (X : ι → S45.RMat H) (R : ℝ)
    (h : (∑ i ∈ s, (X i) ^ 2) ≤ R • (1 : S45.RMat H)) :
    (∑ i ∈ s, ((X i).map (fun a : ℝ => (a : ℂ))) ^ 2) ≤ R • (1 : S45.CMat H) := by
  rw [Matrix.le_iff] at h ⊢
  have hpsd := posSemidef_map_ofReal h
  have heq : (R • (1 : S45.RMat H) - ∑ i ∈ s, (X i) ^ 2).map (fun a : ℝ => (a : ℂ)) =
      R • (1 : S45.CMat H) - ∑ i ∈ s, ((X i).map (fun a : ℝ => (a : ℂ))) ^ 2 := by
    ext a b
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.sum_apply, sq, Matrix.mul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    split_ifs <;> simp
  rwa [heq] at hpsd

theorem real_map_complex_norm_le {H : Type*} [Fintype H] [DecidableEq H]
    (A : S45.RMat H) :
    ‖A.map (fun a : ℝ => (a : ℂ))‖ ≤ ‖A‖ := by
  set Y : S45.CMat H := A.map (fun a : ℝ => (a : ℂ)) with hY
  have key : ∀ x : EuclideanSpace ℂ H,
      ‖(EuclideanSpace.equiv H ℂ).symm (Y *ᵥ x)‖ ≤ ‖A‖ * ‖x‖ := by
    intro x
    let u : EuclideanSpace ℝ H := (EuclideanSpace.equiv H ℝ).symm (fun i => (x i).re)
    let v : EuclideanSpace ℝ H := (EuclideanSpace.equiv H ℝ).symm (fun i => (x i).im)
    have hu := Matrix.l2_opNorm_mulVec A u
    have hv := Matrix.l2_opNorm_mulVec A v
    have hcomp : ∀ i, ‖(Y *ᵥ x) i‖ ^ 2 = ((A *ᵥ u) i) ^ 2 + ((A *ᵥ v) i) ^ 2 := by
      intro i
      have hre : ((Y *ᵥ x) i).re = (A *ᵥ u) i := by
        simp [hY, u, v, Matrix.mulVec, dotProduct, Complex.re_sum]
      have him : ((Y *ᵥ x) i).im = (A *ᵥ v) i := by
        simp [hY, u, v, Matrix.mulVec, dotProduct, Complex.im_sum]
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
      ring
    have hY2 : ‖(EuclideanSpace.equiv H ℂ).symm (Y *ᵥ x)‖ ^ 2 =
        ‖(EuclideanSpace.equiv H ℝ).symm (A *ᵥ u)‖ ^ 2 +
          ‖(EuclideanSpace.equiv H ℝ).symm (A *ᵥ v)‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      change ‖(Y *ᵥ x) i‖ ^ 2 = ‖(A *ᵥ u) i‖ ^ 2 + ‖(A *ᵥ v) i‖ ^ 2
      rw [hcomp i, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    have hx2 : ‖x‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      change ‖x i‖ ^ 2 = ‖(x i).re‖ ^ 2 + ‖(x i).im‖ ^ 2
      rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_apply]
      ring
    have hA0 := norm_nonneg A
    have hsq : ‖(EuclideanSpace.equiv H ℂ).symm (Y *ᵥ x)‖ ^ 2 ≤ (‖A‖ * ‖x‖) ^ 2 := by
      rw [hY2, mul_pow, hx2]
      have h1 := pow_le_pow_left₀ (norm_nonneg _) hu 2
      have h2 := pow_le_pow_left₀ (norm_nonneg _) hv 2
      rw [mul_pow] at h1 h2
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  rw [← Matrix.l2_opNorm_toEuclideanCLM Y]
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) key

theorem posSemidef_fromBlocks_diag_a2 {P H : Type*} [Fintype P] [Fintype H]
    [DecidableEq P] [DecidableEq H] (A : S45.CMat P) (D : S45.CMat H)
    (hA : A.PosSemidef) (hD : D.PosSemidef) :
    (Matrix.fromBlocks A 0 0 D : Matrix (P ⊕ H) (P ⊕ H) ℂ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨Matrix.IsHermitian.fromBlocks hA.1 (by simp) hD.1, ?_⟩
  intro x
  have hsplit : star x ⬝ᵥ (Matrix.fromBlocks A 0 0 D *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) +
        star (x ∘ Sum.inr) ⬝ᵥ (D *ᵥ (x ∘ Sum.inr)) := by
    rw [Matrix.fromBlocks_mulVec]
    simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type]
  rw [hsplit]
  exact add_nonneg (hA.dotProduct_mulVec_nonneg _) (hD.dotProduct_mulVec_nonneg _)

theorem fromBlocks_le_smul_one {P H : Type*} [Fintype P] [DecidableEq P]
    [Fintype H] [DecidableEq H] {M1 : S45.CMat P} {M2 : S45.CMat H} {R : ℝ}
    (h1 : M1 ≤ R • (1 : S45.CMat P)) (h2 : M2 ≤ R • (1 : S45.CMat H)) :
    Matrix.fromBlocks M1 0 0 M2 ≤ R • (1 : S45.CMat (P ⊕ H)) := by
  rw [Matrix.le_iff] at h1 h2 ⊢
  have heq : R • (1 : S45.CMat (P ⊕ H)) - Matrix.fromBlocks M1 0 0 M2 =
      Matrix.fromBlocks (R • (1 : S45.CMat P) - M1) 0 0 (R • (1 : S45.CMat H) - M2) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply]
  rw [heq]
  exact posSemidef_fromBlocks_diag_a2 _ _ h1 h2

theorem scalarDilation_sq (u : ℂ) :
    (scalarDilation u) ^ 2 = (‖u‖ ^ 2) • (1 : S45.CMat (Fin 2)) := by
  have hnorm : u * star u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hnorm' : star u * u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by rw [mul_comm]; exact hnorm
  have hone : (‖u‖ ^ 2) • (1 : S45.CMat (Fin 2)) =
      !![((‖u‖ ^ 2 : ℝ) : ℂ), 0; 0, ((‖u‖ ^ 2 : ℝ) : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, Complex.real_smul]
  rw [hone, pow_two, scalarDilation, Matrix.mul_fin_two]
  simp only [mul_zero, zero_mul, add_zero, zero_add, hnorm, hnorm']

theorem scalarDilation_norm_le (u : ℂ) : ‖scalarDilation u‖ ≤ ‖u‖ := by
  have h1 := Matrix.l2_opNorm_conjTranspose_mul_self (scalarDilation u)
  rw [(scalarDilation_isHermitian u).eq, ← sq, scalarDilation_sq u, norm_smul,
    Real.norm_of_nonneg (sq_nonneg ‖u‖)] at h1
  have h_one : ‖(1 : S45.CMat (Fin 2))‖ ≤ 1 := by
    rw [Matrix.cstar_norm_def, map_one]
    exact ContinuousLinearMap.norm_id_le
  have hsq : ‖scalarDilation u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    calc ‖scalarDilation u‖ ^ 2 = ‖scalarDilation u‖ * ‖scalarDilation u‖ := sq _
      _ = ‖u‖ ^ 2 * ‖(1 : S45.CMat (Fin 2))‖ := h1.symm
      _ ≤ ‖u‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left h_one (sq_nonneg _)
      _ = ‖u‖ ^ 2 := mul_one _
  exact nonneg_le_nonneg_of_sq_le_sq (norm_nonneg u) (by linarith)

theorem scalarBlock_sq_eq (a : ℝ) :
    (scalarBlock a) ^ 2 = scalarBlock (a ^ 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sq, scalarBlock, Matrix.mul_apply, Fin.sum_univ_two]

theorem scalarBlock_sq_le (a : ℝ) :
    (scalarBlock a) ^ 2 ≤ (|a| ^ 2) • (1 : S45.CMat (Fin 2)) := by
  rw [Matrix.le_iff]
  let B : S45.CMat (Fin 2) := !![0, 0; 0, (a : ℂ)]
  have heq : (|a| ^ 2) • (1 : S45.CMat (Fin 2)) - (scalarBlock a) ^ 2 = Bᴴ * B := by
    rw [sq_abs, pow_two (scalarBlock a), scalarBlock, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
        Complex.real_smul, Matrix.one_apply, sq]
  rw [heq]
  exact Matrix.posSemidef_conjTranspose_mul_self B

theorem scalarBlock_norm_le (a : ℝ) : ‖scalarBlock a‖ ≤ |a| := by
  have hdiag : scalarBlock a = Matrix.diagonal ![(a : ℂ), 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [scalarBlock]
  rw [hdiag, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (abs_nonneg a)).mpr fun i => ?_
  fin_cases i <;> simp

end StepIdentitiesAndTransfer

end AndersonAC.AgentS78
