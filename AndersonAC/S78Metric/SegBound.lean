import AndersonAC.S78Metric.Range
import AndersonAC.S78Metric.Count
import AndersonAC.S78Metric.Segments
import AndersonAC.S78Metric.SegOrder
import AndersonAC.S78Metric.Intervals

open scoped BigOperators ENNReal Topology
open MeasureTheory Filter
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace AndersonAC.SolS78

variable {ι : Type} [DecidableEq ι] [Fintype ι]
variable {κ : Type} [Fintype κ]

/-- Segment lower bound: (k-1)*L ≤ old cost, where k = hit groups. -/
theorem seg_lower_bound {G : SimpleGraph ι} (T : Finset ι) (O : κ → Finset ι)
    {c μ R ℓ : ℝ} {M : ℕ} (hc : 0 < c) (hμ : 0 ≤ μ)
    (hold : ∀ u v, c * (G.dist u v : ℝ) - μ ≤ terminalDistance G T u v)
    (hsep : ∀ a a', a ≠ a' → ∀ u ∈ O a, ∀ v ∈ O a', R - 2 * ℓ ≤ (G.dist u v : ℝ))
    (hmargin : 2 * (M : ℝ) < c * (R - 2 * ℓ) - μ)
    (ys : List ι) (hchain : ys.IsChain G.Adj) :
    let L := sepL c μ R ℓ
    let S := Finset.univ.filter (fun a => ∃ x ∈ ys, x ∈ O a)
    ((S.card - 1 : ℕ) : ℝ) * L ≤ ((pathCost T ys : ℕ) : ℝ) := by
  simp only
  by_cases hk : (Finset.univ.filter (fun a => ∃ x ∈ ys, x ∈ O a)).card ≤ 1
  · have : ((Finset.univ.filter (fun a => ∃ x ∈ ys, x ∈ O a)).card - 1 : ℕ) = 0 := by
      omega
    rw [this]
    simp
  · push Not at hk
    have hdisj : ∀ a b : κ, a ≠ b → Disjoint (O a) (O b) :=
      fun a b h => groups_disjoint hc hμ hsep hmargin h
    have hinj : Function.Injective (repIdx O ys) :=
      repIdx_injective O ys hdisj
    have hk2 : 2 ≤ (hitSet O ys).card := by
      have hEq : (Finset.univ.filter (fun a => ∃ x ∈ ys, x ∈ O a)).card =
          (hitSet O ys).card := rfl
      omega
    have hFcard : ((hitSet O ys).attach.image (repIdx O ys)).card =
        (hitSet O ys).card := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
    -- ordered enumeration of image
    have hFord : ∀ j : Fin (hitSet O ys).card,
        ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard j ∈
          (hitSet O ys).attach.image (repIdx O ys) := by
      intro j
      exact Finset.orderEmbOfFin_mem _ _ _
    -- representative groups in order
    have hex : ∀ j : Fin (hitSet O ys).card,
        ∃ a : ↥(hitSet O ys), repIdx O ys a =
          ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard j := by
      intro j
      have hmem := hFord j
      rw [Finset.mem_image] at hmem
      obtain ⟨a, _, heq⟩ := hmem
      exact ⟨a, heq⟩
    -- choice of preimages
    have hgrp : ∀ j : Fin (hitSet O ys).card, ∃ a : ↥(hitSet O ys),
        repIdx O ys a =
          ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard j :=
      hex
    let grp : Fin (hitSet O ys).card → ↥(hitSet O ys) :=
      fun j => Classical.choose (hex j)
    have hgrp_eq : ∀ j : Fin (hitSet O ys).card, repIdx O ys (grp j) =
        ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard j := by
      intro j
      exact Classical.choose_spec (hex j)
    -- strictly increasing indices
    have hplt : ∀ j : Fin ((hitSet O ys).card - 1),
        ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
          ⟨j.val, by omega⟩ <
        ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
          ⟨j.val + 1, by omega⟩ := by
      intro j
      have hj1 : (⟨j.val, by omega⟩ : Fin (hitSet O ys).card) <
          (⟨j.val + 1, by omega⟩ : Fin (hitSet O ys).card) := by
        rw [Fin.mk_lt_mk]
        exact Nat.lt_succ_self _
      exact (OrderEmbedding.lt_iff_lt _).mpr hj1
    -- sublists between consecutive representatives: IsChain + head
    have hsub_chain : ∀ j : Fin ((hitSet O ys).card - 1),
        (((List.drop
          (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val, by omega⟩) ys).take
          (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val + 1, by omega⟩ -
          ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val, by omega⟩ + 1)).IsChain G.Adj) := by
      intro j
      exact ((hchain.drop _).take _)
    have hsub_head : ∀ j : Fin ((hitSet O ys).card - 1),
        (((List.drop
          (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val, by omega⟩) ys).take
          (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val + 1, by omega⟩ -
          ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val, by omega⟩ + 1)).head? =
          ys[((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val, by omega⟩]?) := by
      intro j
      simp [List.head?_take, List.head?_drop]
    -- last of sublist
    have hsub_last : ∀ j : Fin ((hitSet O ys).card - 1),
        (((List.drop
          (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val, by omega⟩) ys).take
          (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val + 1, by omega⟩ -
          ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val, by omega⟩ + 1)).getLast? =
          ys[((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val + 1, by omega⟩]?) := by
      intro j
      have hpq := hplt j
      have hp_lt : ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
          ⟨j.val, by omega⟩ < ys.length := by
        have hrep_eq := hgrp_eq ⟨j.val, by omega⟩
        obtain ⟨h_lt, _⟩ := repIdx_spec O ys (grp ⟨j.val, by omega⟩)
        rw [hrep_eq] at h_lt
        exact h_lt
      have hq_lt : ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
          ⟨j.val + 1, by omega⟩ < ys.length := by
        have hrep_eq := hgrp_eq ⟨j.val + 1, by omega⟩
        obtain ⟨h_lt, _⟩ := repIdx_spec O ys (grp ⟨j.val + 1, by omega⟩)
        rw [hrep_eq] at h_lt
        exact h_lt
      have hp_le : ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
          ⟨j.val, by omega⟩ ≤
          ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
          ⟨j.val + 1, by omega⟩ := le_of_lt hpq
      have hne : (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
          ⟨j.val + 1, by omega⟩ -
        ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
          ⟨j.val, by omega⟩ + 1) ≠ 0 := by omega
      have htake_len : ((List.drop
          (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val, by omega⟩) ys).take
          (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val + 1, by omega⟩ -
          ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val, by omega⟩ + 1)).length =
          (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val + 1, by omega⟩ -
          ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val, by omega⟩ + 1) := by
        have hlen_drop : ((List.drop
            (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
              ⟨j.val, by omega⟩) ys).length =
            ys.length -
              (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
                ⟨j.val, by omega⟩)) := List.length_drop
        have hle : (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val + 1, by omega⟩ -
          ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val, by omega⟩ + 1) ≤
          ys.length -
            (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
              ⟨j.val, by omega⟩) := by
          omega
        simp [List.length_take, hlen_drop, min_eq_left hle]
      have hlt2 : (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val + 1, by omega⟩ -
          ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val, by omega⟩) <
          (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val + 1, by omega⟩ -
          ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val, by omega⟩ + 1) := Nat.lt_succ_self _
      have hadd : (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val, by omega⟩) +
            ((((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
              ⟨j.val + 1, by omega⟩ -
            ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
              ⟨j.val, by omega⟩)) =
          ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val + 1, by omega⟩ :=
        Nat.add_sub_cancel' hp_le
      have hsub2 : (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val + 1, by omega⟩ -
          ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val, by omega⟩ + 1) - 1 =
          (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val + 1, by omega⟩ -
          ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val, by omega⟩) :=
        Nat.add_sub_cancel _ _
      rw [List.getLast?_eq_getElem?, htake_len, hsub2, List.getElem?_take,
        if_pos hlt2, List.getElem?_drop, hadd]
    -- per-segment lower bound
    have hseg : ∀ j : Fin ((hitSet O ys).card - 1),
        sepL c μ R ℓ ≤
          ((pathCost T
            ((List.drop
              (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
                ⟨j.val, by omega⟩) ys).take
              (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
                ⟨j.val + 1, by omega⟩ -
              ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
                ⟨j.val, by omega⟩ + 1)) : ℕ) : ℝ) := by
      intro j
      have hpq := hplt j
      have haj_ne : grp ⟨j.val, by omega⟩ ≠ grp ⟨j.val + 1, by omega⟩ := by
        intro heq
        have hrep : repIdx O ys (grp ⟨j.val, by omega⟩) =
            repIdx O ys (grp ⟨j.val + 1, by omega⟩) := by rw [heq]
        rw [hgrp_eq, hgrp_eq] at hrep
        exact ne_of_lt hpq hrep
      have hval_ne : ((grp ⟨j.val, by omega⟩ : ↥(hitSet O ys)) : κ) ≠
          ((grp ⟨j.val + 1, by omega⟩ : ↥(hitSet O ys)) : κ) := by
        intro heq
        exact haj_ne (Subtype.ext heq)
      -- endpoints via getElem? (using hsub_head/last + repIdx_spec)
      have hchain_j := hsub_chain j
      have hhead_j := hsub_head j
      have hlast_j := hsub_last j
      -- representative vertices in groups via getElem?
      have hmem_j : ∃ u : ι, u ∈ O ((grp ⟨j.val, by omega⟩ : ↥(hitSet O ys)) : κ) ∧
          (((List.drop
            (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
              ⟨j.val, by omega⟩) ys).take
            (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
              ⟨j.val + 1, by omega⟩ -
            ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
              ⟨j.val, by omega⟩ + 1)).head? = some u) := by
        have hhead_eq := hsub_head j
        have hrep_eq := hgrp_eq ⟨j.val, by omega⟩
        obtain ⟨h_lt, h_mem⟩ := repIdx_spec O ys (grp ⟨j.val, by omega⟩)
        have hopt_eq : ys[((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val, by omega⟩]? =
            ys[repIdx O ys (grp ⟨j.val, by omega⟩)]? := by
          rw [hrep_eq]
        have hrep_opt : ys[repIdx O ys (grp ⟨j.val, by omega⟩)]? =
            some (ys[repIdx O ys (grp ⟨j.val, by omega⟩)]'h_lt) :=
          List.getElem?_eq_getElem h_lt
        have hys_opt : ys[((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val, by omega⟩]? =
            some (ys[repIdx O ys (grp ⟨j.val, by omega⟩)]'h_lt) := by
          rw [hopt_eq, hrep_opt]
        have hS_head := hhead_eq.trans hys_opt
        exact ⟨_, h_mem, hS_head⟩
      -- last endpoint symmetrically
      have hmem_j' : ∃ v : ι, v ∈ O ((grp ⟨j.val + 1, by omega⟩ : ↥(hitSet O ys)) : κ) ∧
          (((List.drop
            (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
              ⟨j.val, by omega⟩) ys).take
            (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
              ⟨j.val + 1, by omega⟩ -
            ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
              ⟨j.val, by omega⟩ + 1)).getLast? = some v) := by
        have hlast_eq := hsub_last j
        have hrep_eq := hgrp_eq ⟨j.val + 1, by omega⟩
        obtain ⟨h_lt, h_mem⟩ := repIdx_spec O ys (grp ⟨j.val + 1, by omega⟩)
        have hopt_eq : ys[((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val + 1, by omega⟩]? =
            ys[repIdx O ys (grp ⟨j.val + 1, by omega⟩)]? := by
          rw [hrep_eq]
        have hrep_opt : ys[repIdx O ys (grp ⟨j.val + 1, by omega⟩)]? =
            some (ys[repIdx O ys (grp ⟨j.val + 1, by omega⟩)]'h_lt) :=
          List.getElem?_eq_getElem h_lt
        have hys_opt : ys[((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
            ⟨j.val + 1, by omega⟩]? =
            some (ys[repIdx O ys (grp ⟨j.val + 1, by omega⟩)]'h_lt) := by
          rw [hopt_eq, hrep_opt]
        -- S.getLast? = ys[q]? via hlast_eq? Actually hlast_eq states S.getLast? = ys[q]?
        -- hlast_eq : S.getLast? = ys[q]? where q = orderEmb... ⟨j.val+1,...⟩
        -- hys_opt : ys[q]? = some v, so S.getLast? = some v via transitivity
        have hS_last := hlast_eq.trans hys_opt
        exact ⟨_, h_mem, hS_last⟩
      obtain ⟨u, hu, hhead⟩ := hmem_j
      obtain ⟨v, hv, hlast⟩ := hmem_j'
      have hold_seg := oldCost_ge_of_hold T c μ hold hchain_j hhead hlast
      have hsep_le := sepL_le_dist (G := G) (O := O) (μ := μ) hc hsep hval_ne hu hv
      linarith
    -- sum of subcosts ≤ total
    have hsum_le : ∑ j : Fin ((hitSet O ys).card - 1),
        pathCost T
          ((List.drop
            (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
              ⟨j.val, by omega⟩) ys).take
            (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
              ⟨j.val + 1, by omega⟩ -
            ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
              ⟨j.val, by omega⟩ + 1)) ≤
        pathCost T ys := by
      have hedge : ∀ j : Fin ((hitSet O ys).card - 1),
          pathCost T
            ((List.drop
              (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
                ⟨j.val, by omega⟩) ys).take
              (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
                ⟨j.val + 1, by omega⟩ -
              ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
                ⟨j.val, by omega⟩ + 1)) =
            edgeSum T
              ((List.drop
                (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
                  ⟨j.val, by omega⟩) ys).take
                (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
                  ⟨j.val + 1, by omega⟩ -
                ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
                  ⟨j.val, by omega⟩ + 1)) := by
        intro j
        exact pathCost_eq_edgeSum T _
      simp_rw [hedge]
      have hbound : ∀ j : Fin (hitSet O ys).card,
          ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard j < ys.length := by
        intro j
        obtain ⟨hj, _⟩ := repIdx_spec O ys (grp j)
        rwa [hgrp_eq] at hj
      have hint := sum_ordered_intervals_le (hitSet O ys).card ys.length (by omega)
        (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard) hbound
        (edgeAt T ys)
      simp_rw [edgeSum_sublist T ys _ _ (le_of_lt (hplt _)) (hbound _)]
      rw [pathCost_eq_edgeSum]
      exact hint
    -- final (k-1)*L bound via hseg + hsum_le
    have hfinal : (((hitSet O ys).card - 1 : ℕ) : ℝ) * sepL c μ R ℓ ≤
        ((pathCost T ys : ℕ) : ℝ) := by
      have hsumL : ∑ _j : Fin ((hitSet O ys).card - 1), sepL c μ R ℓ ≤
          ∑ j : Fin ((hitSet O ys).card - 1),
            ((pathCost T
              ((List.drop
                (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
                  ⟨j.val, by omega⟩) ys).take
                (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
                  ⟨j.val + 1, by omega⟩ -
                ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
                  ⟨j.val, by omega⟩ + 1)) : ℕ) : ℝ) :=
        Finset.sum_le_sum (fun j _ => hseg j)
      have hsum_eq : ∑ _j : Fin ((hitSet O ys).card - 1), sepL c μ R ℓ =
          (((hitSet O ys).card - 1 : ℕ) : ℝ) * sepL c μ R ℓ := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
      have hcast_le : ((∑ j : Fin ((hitSet O ys).card - 1),
          pathCost T
            ((List.drop
              (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
                ⟨j.val, by omega⟩) ys).take
              (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
                ⟨j.val + 1, by omega⟩ -
              ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
                ⟨j.val, by omega⟩ + 1)) : ℕ) : ℝ) ≤
          ((pathCost T ys : ℕ) : ℝ) :=
        Nat.cast_le.mpr hsum_le
      have hcast_eq : ((∑ j : Fin ((hitSet O ys).card - 1),
          pathCost T
            ((List.drop
              (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
                ⟨j.val, by omega⟩) ys).take
              (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
                ⟨j.val + 1, by omega⟩ -
              ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
                ⟨j.val, by omega⟩ + 1)) : ℕ) : ℝ) =
          ∑ j : Fin ((hitSet O ys).card - 1),
            ((pathCost T
              ((List.drop
                (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
                  ⟨j.val, by omega⟩) ys).take
                (((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
                  ⟨j.val + 1, by omega⟩ -
                ((hitSet O ys).attach.image (repIdx O ys)).orderEmbOfFin hFcard
                  ⟨j.val, by omega⟩ + 1)) : ℕ) : ℝ) := by
        rw [Nat.cast_sum]
      linarith
    exact hfinal

end AndersonAC.SolS78
