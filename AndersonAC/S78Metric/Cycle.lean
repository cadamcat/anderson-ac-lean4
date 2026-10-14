import AndersonAC.S78Metric.Chain

open scoped BigOperators ENNReal Topology
open MeasureTheory Filter
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace AndersonAC.SolS78

variable {ι : Type} [DecidableEq ι]

/-- Auxiliary strong induction: every chain contains a Nodup subchain with no larger
new cost. The sublist relation guarantees vertex inclusion for later counting. -/
theorem exists_nodup_subchain_aux (T' : Finset ι) (G : SimpleGraph ι) (n : ℕ) :
    ∀ (u v : ι) (xs : List ι), xs.IsChain G.Adj → xs.head? = some u →
      xs.getLast? = some v → xs.length ≤ n →
      ∃ ys : List ι, ys.IsChain G.Adj ∧ ys.head? = some u ∧ ys.getLast? = some v ∧
        ys.Nodup ∧ ys.Sublist xs ∧ pathCost T' ys ≤ pathCost T' xs := by
  induction n with
  | zero =>
    intro u v xs hchain hhead hlast hlen
    have : xs = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    subst this
    simp at hhead
  | succ n ih =>
    intro u v xs hchain hhead hlast hlen
    by_cases hnodup : xs.Nodup
    · exact ⟨xs, hchain, hhead, hlast, hnodup, List.Sublist.refl xs, le_rfl⟩
    · cases xs with
      | nil => simp_all
      | cons x ys =>
        cases ys with
        | nil => simp_all
        | cons y ys0 =>
          have htail_chain : (y :: ys0).IsChain G.Adj := by
            have h := hchain
            simp only [List.isChain_cons_cons] at h
            exact h.2
          have hx_eq : x = u := by
            have hxh : ((x :: y :: ys0 : List ι).head? = some x) := rfl
            have h2 : (some x : Option ι) = some u := hxh.symm.trans hhead
            exact Option.some_inj.mp h2
          by_cases hxmem : x ∈ (y :: ys0)
          · -- head cycle: splice it out
            obtain ⟨pre, suf, hys_eq⟩ := exists_pre_suf_of_mem hxmem
            have hys_eq' : (y :: ys0) = pre ++ (x :: suf) := by
              calc (y :: ys0) = pre ++ [x] ++ suf := hys_eq
                _ = pre ++ (x :: suf) := by simp
            have hxs'_chain : (x :: suf).IsChain G.Adj := by
              have h1 : (pre ++ (x :: suf)).IsChain G.Adj := by
                rw [← hys_eq']; exact htail_chain
              exact List.IsChain.right_of_append h1
            have hxs'_head : (x :: suf).head? = some u := by
              simp [hx_eq]
            have hxs'_last : (x :: suf).getLast? = some v := by
              have hne1 : (x :: suf) ≠ [] := by simp
              have hne2 : (y :: ys0) ≠ [] := by simp
              have h1 : ((y :: ys0)).getLast? = ((x :: suf)).getLast? := by
                conv_lhs => rw [hys_eq']
                exact List.getLast?_append_of_ne_nil pre hne1
              have h2 : ((x :: y :: ys0)).getLast? = ((y :: ys0)).getLast? := by
                have hxy : (x :: y :: ys0 : List ι) = [x] ++ (y :: ys0) := rfl
                rw [hxy]
                exact List.getLast?_append_of_ne_nil [x] hne2
              rw [← h1, ← h2]
              exact hlast
            have hxs'_sub : (x :: suf).Sublist (x :: y :: ys0) := by
              have hsuf_sub : suf.Sublist (y :: ys0) := by
                rw [hys_eq']
                have h1 : suf.Sublist (x :: suf) := by
                  have h1' : suf.Sublist ([x] ++ suf) :=
                    List.sublist_append_right [x] suf
                  simpa using h1'
                have h2 : (x :: suf).Sublist (pre ++ (x :: suf)) :=
                  List.sublist_append_right pre (x :: suf)
                exact h1.trans h2
              exact List.Sublist.cons_cons x hsuf_sub
            have hxs'_len : (x :: suf).length < (x :: y :: ys0).length := by
              have hlen_y : (y :: ys0).length = pre.length + (x :: suf).length := by
                rw [hys_eq', List.length_append]
              simp only [List.length_cons] at hlen_y ⊢
              omega
            have hxs'_le : (x :: suf).length ≤ n := by omega
            obtain ⟨zs, hzs_chain, hzs_head, hzs_last, hzs_nodup, hzs_sub, hzs_cost⟩ :=
              ih u v (x :: suf) hxs'_chain hxs'_head hxs'_last hxs'_le
            refine ⟨zs, hzs_chain, hzs_head, hzs_last, hzs_nodup,
              hzs_sub.trans hxs'_sub, ?_⟩
            have hcost1 : pathCost T' (x :: suf) ≤ pathCost T' (x :: y :: ys0) := by
              have h1 : pathCost T' (y :: ys0) =
                  pathCost T' pre + bridgeCost T' pre (x :: suf) + pathCost T' (x :: suf) := by
                conv_lhs => rw [hys_eq']
                exact pathCost_append T' pre (x :: suf)
              have h2 : pathCost T' (x :: y :: ys0) =
                  pathCost T' [x] + bridgeCost T' [x] (y :: ys0) + pathCost T' (y :: ys0) := by
                have hxy : (x :: y :: ys0 : List ι) = [x] ++ (y :: ys0) := rfl
                rw [hxy]
                exact pathCost_append T' [x] (y :: ys0)
              omega
            omega
          · -- head fresh: recurse on tail, then prepend
            have hnodup_tail_false : ¬(y :: ys0).Nodup := by
              intro h
              have hnd : (x :: y :: ys0 : List ι).Nodup :=
                List.nodup_cons.mpr ⟨hxmem, h⟩
              contradiction
            have htail_head : (y :: ys0).head? = some y := rfl
            have htail_last : (y :: ys0).getLast? = some v := by
              have hne : (y :: ys0 : List ι) ≠ [] := by simp
              have h2 : ((x :: y :: ys0 : List ι)).getLast? = ((y :: ys0)).getLast? := by
                have hxy : (x :: y :: ys0 : List ι) = [x] ++ (y :: ys0) := rfl
                rw [hxy]
                exact List.getLast?_append_of_ne_nil [x] hne
              rw [← h2]; exact hlast
            have htail_len : (y :: ys0).length ≤ n := by
              simp only [List.length_cons] at hlen ⊢
              omega
            obtain ⟨zs, hzs_chain, hzs_head, hzs_last, hzs_nodup, hzs_sub, hzs_cost⟩ :=
              ih y v (y :: ys0) htail_chain htail_head htail_last htail_len
            have hzs_ne : zs ≠ [] := by
              intro h; rw [h] at hzs_head; simp at hzs_head
            obtain ⟨z, zs0, hzs_eq⟩ := List.exists_cons_of_ne_nil hzs_ne
            have hz_head : z = y := by
              have h1 : ((z :: zs0 : List ι).head? = some z) := rfl
              rw [← hzs_eq] at h1
              rw [hzs_head] at h1
              exact Option.some_inj.mp h1.symm
            rw [hz_head] at hzs_eq
            have hadj : G.Adj x y := by
              have h := hchain
              simp only [List.isChain_cons_cons] at h
              exact h.1
            have hxs''_chain : (x :: y :: zs0).IsChain G.Adj := by
              have hzc : (y :: zs0).IsChain G.Adj := by
                rw [← hzs_eq]; exact hzs_chain
              simp only [List.isChain_cons_cons]
              exact ⟨hadj, hzc⟩
            have hxs''_head : (x :: y :: zs0).head? = some u := by
              simp [hx_eq]
            have hxs''_last : (x :: y :: zs0).getLast? = some v := by
              have h1 : ((x :: y :: zs0 : List ι)).getLast? = ((y :: zs0)).getLast? := by
                have hxy : (x :: y :: zs0 : List ι) = [x] ++ (y :: zs0) := rfl
                rw [hxy]
                exact List.getLast?_append_of_ne_nil [x] (by simp)
              rw [h1, ← hzs_eq]
              exact hzs_last
            have hx_notin : x ∉ (y :: zs0) := by
              intro hmem
              have hmem_sub : x ∈ (y :: ys0) :=
                List.Sublist.mem hmem (by rw [← hzs_eq]; exact hzs_sub)
              contradiction
            have hxs''_nodup : (x :: y :: zs0).Nodup :=
              List.nodup_cons.mpr ⟨hx_notin, by rw [← hzs_eq]; exact hzs_nodup⟩
            have hxs''_sub : (x :: y :: zs0).Sublist (x :: y :: ys0) := by
              have hsub : (y :: zs0).Sublist (y :: ys0) := by
                rw [← hzs_eq]; exact hzs_sub
              exact List.Sublist.cons_cons x hsub
            have hxs''_cost : pathCost T' (x :: y :: zs0) ≤ pathCost T' (x :: y :: ys0) := by
              have e1 : pathCost T' (x :: y :: zs0) =
                  edgeCost T' x y + pathCost T' (y :: zs0) :=
                pathCost_cons_cons T' x y zs0
              have e2 : pathCost T' (x :: y :: ys0) =
                  edgeCost T' x y + pathCost T' (y :: ys0) :=
                pathCost_cons_cons T' x y ys0
              have hzs_cost' : pathCost T' (y :: zs0) ≤ pathCost T' (y :: ys0) := by
                have h1 : pathCost T' zs ≤ pathCost T' (y :: ys0) := hzs_cost
                rw [hzs_eq] at h1
                exact h1
              omega
            exact ⟨x :: y :: zs0, hxs''_chain, hxs''_head, hxs''_last,
              hxs''_nodup, hxs''_sub, hxs''_cost⟩

/-- Every chain contains a Nodup subchain with no larger new cost. -/
theorem exists_nodup_subchain (T' : Finset ι) (G : SimpleGraph ι)
    (u v : ι) (xs : List ι) (hchain : xs.IsChain G.Adj)
    (hhead : xs.head? = some u) (hlast : xs.getLast? = some v) :
    ∃ ys : List ι, ys.IsChain G.Adj ∧ ys.head? = some u ∧ ys.getLast? = some v ∧
      ys.Nodup ∧ ys.Sublist xs ∧ pathCost T' ys ≤ pathCost T' xs :=
  exists_nodup_subchain_aux T' G xs.length u v xs hchain hhead hlast le_rfl

end AndersonAC.SolS78
