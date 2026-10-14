import AndersonAC.S78WRec.LeafBound

open scoped BigOperators

noncomputable section

namespace AndersonAC.SolS78

open AndersonAC.S78
open AndersonAC.S78WRec

theorem witness_recursion_proof (d : ℕ) (hd : 3 ≤ d) :
    ∃ N : ℕ, ∃ C : ℝ, 1 ≤ C ∧ ∀ m n₀ j c, N ≤ n₀ → n₀ < j →
      clearingScheduled j m → 0 < c →
      witnessMass d m n₀ j c ≤
        recursionBound d n₀ j c C (fun r => witnessMass d m n₀ r c) := by
  classical
  obtain ⟨N, hchildrenDisjoint⟩ := witness_children_disjoint_proof d hd
  let C := recursionConstant d
  refine ⟨N, C, ?_, ?_⟩
  · exact recursionConstant_ge_one d
  · intro m n₀ j c hN hnj hclear hc
    have hm : 1 ≤ m := by
      unfold clearingScheduled at hclear
      omega
    have hballC (x : Torus d m) :
        (witnessBall d m j x).card ≤ C * witnessRadius j ^ d := by
      have hball := witnessBall_card_real_le d m j x hm
      have hkind : (3 : ℝ) ^ d ≤ C := by
        have htypes : (1 : ℝ) ≤ (Fintype.card BirthType : ℝ) := by
          have hp : 0 < Fintype.card BirthType := Fintype.card_pos_iff.mpr ⟨BirthType.tile⟩
          exact_mod_cast (Nat.succ_le_iff.mpr hp)
        dsimp [C, recursionConstant]
        calc
          (3 : ℝ) ^ d = 1 * (3 : ℝ) ^ d := by ring
          _ ≤ (Fintype.card BirthType : ℝ) * (3 : ℝ) ^ d :=
            mul_le_mul_of_nonneg_right htypes (by positivity)
      have hrad : 0 ≤ witnessRadius j := by
        unfold witnessRadius
        positivity
      exact hball.trans (mul_le_mul_of_nonneg_right hkind (pow_nonneg hrad d))
    have hpoint (x : Torus d m) :
        (∑ L ∈ witnessFamily d m n₀ j x, witnessWeight c L) ≤
          recursionBound d n₀ j c C (fun r => witnessMass d m n₀ r c) := by
      calc
        (∑ L ∈ witnessFamily d m n₀ j x, witnessWeight c L) ≤
            ∑ code ∈ treeCodeSet d m n₀ j x,
              witnessWeight c (treeCodeOutput code) :=
          witnessFamily_sum_le_treeCodeSet_sum c
        _ = (∑ a ∈ leafCodeSet d m n₀ j x, birthBound c a.val.scale) +
            ∑ b ∈ branchCodeSet d m n₀ j x,
              witnessWeight c (treeCodeOutput (.inr b)) :=
          treeCodeSet_sum_eq d m n₀ j x c
        _ ≤ C * (j : ℝ) * witnessRadius j ^ d *
              birthBound c (max n₀ (historyEarlier d j)) +
            (if n₀ ≤ historyEarlier d j then
              (C * witnessRadius j ^ d *
                witnessMass d m n₀ (historyEarlier d j) c) ^ historyChildren d j
             else 0) := by
          exact add_le_add
            (leafCodeSet_sum_le d m n₀ j x c hc hm)
            (branchCode_sum_le d m n₀ j x c C N hN hchildrenDisjoint (hballC x))
        _ = recursionBound d n₀ j c C (fun r => witnessMass d m n₀ r c) := by
          simp [recursionBound]
    change sSup (Set.range fun x : Torus d m =>
        ∑ L ∈ witnessFamily d m n₀ j x, witnessWeight c L) ≤ _
    apply csSup_le
    · exact ⟨_, ⟨(0 : Torus d m), rfl⟩⟩
    · rintro _ ⟨x, rfl⟩
      exact hpoint x

end AndersonAC.SolS78
