import AndersonAC.S78WRec.Partition
import AndersonAC.S78WRec.TorusBall
import AndersonAC.S78WSupp.WitnessSupport

open scoped BigOperators

noncomputable section

namespace AndersonAC.S78WRec

open AndersonAC.S78

lemma childChoice_sum_eq (d m n₀ r : ℕ) (x : Torus d m) (c : ℝ) :
    (∑ L : ChildChoice d m n₀ r x, witnessWeight c L.val) =
      ∑ L ∈ witnessFamily d m n₀ r x, witnessWeight c L := by
  classical
  calc
    (∑ L : ChildChoice d m n₀ r x, witnessWeight c L.val) =
        ∑ L ∈ (witnessFamily d m n₀ r x).attach, witnessWeight c L.val := by simp
    _ = ∑ L ∈ witnessFamily d m n₀ r x, witnessWeight c L := Finset.sum_attach _ _

lemma witnessFamily_sum_le_mass (d m n₀ r : ℕ) (x : Torus d m) (c : ℝ) :
    (∑ L ∈ witnessFamily d m n₀ r x, witnessWeight c L) ≤ witnessMass d m n₀ r c := by
  classical
  let f : Torus d m → ℝ := fun y =>
    ∑ L ∈ witnessFamily d m n₀ r y, witnessWeight c L
  have hbdd : BddAbove (Set.range f) := (Set.finite_range f).bddAbove
  exact le_csSup hbdd ⟨x, rfl⟩

lemma witnessMass_nonneg (d m n₀ r : ℕ) (c : ℝ) :
    0 ≤ witnessMass d m n₀ r c := by
  have hsum : 0 ≤ ∑ L ∈ witnessFamily d m n₀ r (0 : Torus d m), witnessWeight c L := by
    exact Finset.sum_nonneg fun L _ => witnessWeight_nonneg c L
  exact hsum.trans (witnessFamily_sum_le_mass d m n₀ r 0 c)

lemma witnessWeight_biUnion_eq_prod {d m k : ℕ} (c : ℝ)
    (L : Fin k → Finset (BirthLabel (Torus d m)))
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set (Fin k)) L) :
    witnessWeight c (Finset.univ.biUnion L) = ∏ i, witnessWeight c (L i) := by
  classical
  change (∏ a ∈ Finset.univ.biUnion L, birthBound c a.scale) =
    ∏ i, ∏ a ∈ L i, birthBound c a.scale
  have hpair : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin k))) L := by
    simpa using hdisj
  rw [Finset.prod_biUnion hpair]

def branchNearSet (d m n₀ j : ℕ) (x : Torus d m) :
    Finset (BranchCode d m n₀ j) := by
  classical
  exact Finset.univ.filter fun b =>
    ∀ i, physicalDistance d m x (b.1 i) ≤ witnessRadius j / 2

def centerOptionSet (d m j : ℕ) (x : Torus d m) :
    Finset (Fin (historyChildren d j) → Torus d m) := by
  classical
  exact Finset.univ.filter fun centers =>
    ∀ i, physicalDistance d m x (centers i) ≤ witnessRadius j / 2

lemma childFunction_sum_eq (d m n₀ j : ℕ) (c : ℝ)
    (centers : Fin (historyChildren d j) → Torus d m) :
    (∑ children : (i : Fin (historyChildren d j)) →
        ChildChoice d m n₀ (historyEarlier d j) (centers i),
      ∏ i, witnessWeight c (children i).val) =
      ∏ i, ∑ L ∈ witnessFamily d m n₀ (historyEarlier d j) (centers i),
        witnessWeight c L := by
  classical
  let f : (i : Fin (historyChildren d j)) →
      ChildChoice d m n₀ (historyEarlier d j) (centers i) → ℝ :=
    fun _ child => witnessWeight c child.val
  calc
    (∑ children : (i : Fin (historyChildren d j)) →
        ChildChoice d m n₀ (historyEarlier d j) (centers i),
      ∏ i, witnessWeight c (children i).val) =
        ∏ i, ∑ child : ChildChoice d m n₀ (historyEarlier d j) (centers i),
          witnessWeight c child.val := by
            exact (Fintype.prod_sum f).symm
    _ = ∏ i, ∑ L ∈ witnessFamily d m n₀ (historyEarlier d j) (centers i),
          witnessWeight c L := by
            apply Finset.prod_congr rfl
            intro i hi
            exact childChoice_sum_eq d m n₀ (historyEarlier d j) (centers i) c

lemma branchNear_sum_eq (d m n₀ j : ℕ) (x : Torus d m) (c : ℝ) :
    (∑ b ∈ branchNearSet d m n₀ j x,
      ∏ i, witnessWeight c ((b.2 i).val)) =
      ∑ centers ∈ centerOptionSet d m j x,
        ∏ i, ∑ L ∈ witnessFamily d m n₀ (historyEarlier d j) (centers i),
          witnessWeight c L := by
  classical
  let near (centers : Fin (historyChildren d j) → Torus d m) :=
    ∀ i, physicalDistance d m x (centers i) ≤ witnessRadius j / 2
  let f : (centers : Fin (historyChildren d j) → Torus d m) →
      ((i : Fin (historyChildren d j)) →
        ChildChoice d m n₀ (historyEarlier d j) (centers i)) → ℝ :=
    fun centers children => if near centers then
      ∏ i, witnessWeight c (children i).val else 0
  calc
    (∑ b ∈ branchNearSet d m n₀ j x,
        ∏ i, witnessWeight c ((b.2 i).val)) =
      ∑ b : BranchCode d m n₀ j, f b.1 b.2 := by
        change (∑ b ∈ Finset.univ.filter (fun b : BranchCode d m n₀ j => near b.1),
          ∏ i, witnessWeight c ((b.2 i).val)) = _
        rw [Finset.sum_filter]
    _ = ∑ centers, ∑ children, f centers children := Fintype.sum_sigma' f
    _ = ∑ centers,
        if near centers then
          ∏ i, ∑ L ∈ witnessFamily d m n₀ (historyEarlier d j) (centers i),
            witnessWeight c L else 0 := by
          apply Finset.sum_congr rfl
          intro centers _
          by_cases hn : near centers
          · simp [f, hn, childFunction_sum_eq]
          · simp [f, hn]
    _ = ∑ centers ∈ centerOptionSet d m j x,
          ∏ i, ∑ L ∈ witnessFamily d m n₀ (historyEarlier d j) (centers i),
            witnessWeight c L := by
          simp [centerOptionSet, Finset.sum_filter, near]

lemma branchCode_weight_eq (d m n₀ j : ℕ) (c : ℝ)
    (b : BranchCode d m n₀ j)
    (hpair : Set.PairwiseDisjoint (Set.univ : Set (Fin (historyChildren d j)))
      (fun i => (b.2 i).val)) :
    witnessWeight c (treeCodeOutput (.inr b)) =
      ∏ i, witnessWeight c ((b.2 i).val) := by
  simpa [treeCodeOutput] using
    witnessWeight_biUnion_eq_prod c (fun i => (b.2 i).val) hpair

lemma childFamily_product_le_mass_pow (d m n₀ j : ℕ) (c : ℝ)
    (centers : Fin (historyChildren d j) → Torus d m) :
    (∏ i, ∑ L ∈ witnessFamily d m n₀ (historyEarlier d j) (centers i),
      witnessWeight c L) ≤
      (witnessMass d m n₀ (historyEarlier d j) c) ^ historyChildren d j := by
  have hsumNonneg (i : Fin (historyChildren d j)) :
      0 ≤ ∑ L ∈ witnessFamily d m n₀ (historyEarlier d j) (centers i),
        witnessWeight c L :=
    Finset.sum_nonneg fun L _ => witnessWeight_nonneg c L
  calc
    (∏ i, ∑ L ∈ witnessFamily d m n₀ (historyEarlier d j) (centers i),
        witnessWeight c L) ≤
        ∏ i, witnessMass d m n₀ (historyEarlier d j) c := by
          apply Finset.prod_le_prod₀
          · intro i hi
            exact hsumNonneg i
          · intro i hi
            exact witnessFamily_sum_le_mass d m n₀ (historyEarlier d j) (centers i) c
    _ = (witnessMass d m n₀ (historyEarlier d j) c) ^ historyChildren d j := by simp

lemma branchCode_sum_le (d m n₀ j : ℕ) (x : Torus d m) (c C : ℝ)
    (N : ℕ) (hN : N ≤ n₀)
    (hchildrenDisjoint : ∀ (m' n₀' r : ℕ) (x' y' : Torus d m')
      (L K : Finset (BirthLabel (Torus d m'))), N ≤ n₀' →
      IsWitness d m' n₀' r x' L → IsWitness d m' n₀' r y' K →
      3 * witnessRadius r < physicalDistance d m' x' y' → Disjoint L K)
    (hball : ((witnessBall d m j x).card : ℝ) ≤ C * witnessRadius j ^ d) :
    (∑ b ∈ branchCodeSet d m n₀ j x,
      witnessWeight c (treeCodeOutput (.inr b))) ≤
      if n₀ ≤ historyEarlier d j then
        (C * witnessRadius j ^ d * witnessMass d m n₀ (historyEarlier d j) c) ^
          historyChildren d j
      else 0 := by
  classical
  by_cases hr : n₀ ≤ historyEarlier d j
  · let r := historyEarlier d j
    have hsubset : branchCodeSet d m n₀ j x ⊆ branchNearSet d m n₀ j x := by
      intro b hb
      have hvalid := (Finset.mem_filter.mp hb).2
      rcases hvalid with ⟨_, _, _, hnear, _⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnear⟩
    have hpair (b : BranchCode d m n₀ j)
        (hb : b ∈ branchCodeSet d m n₀ j x) :
        Set.PairwiseDisjoint (Set.univ : Set (Fin (historyChildren d j)))
          (fun i => (b.2 i).val) := by
      have hvalid := (Finset.mem_filter.mp hb).2
      rcases hvalid with ⟨_, _, _, _, hsep⟩
      intro i _ l _ hil
      apply hchildrenDisjoint m n₀ r (b.1 i) (b.1 l) (b.2 i).val (b.2 l).val hN
      · exact witness_of_mem_family (b.2 i).property
      · exact witness_of_mem_family (b.2 l).property
      · simpa [r] using hsep i l hil
    have hsumEq :
        (∑ b ∈ branchCodeSet d m n₀ j x,
          witnessWeight c (treeCodeOutput (.inr b))) =
        ∑ b ∈ branchCodeSet d m n₀ j x,
          ∏ i, witnessWeight c ((b.2 i).val) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact branchCode_weight_eq d m n₀ j c b (hpair b hb)
    have hbranch :
        (∑ b ∈ branchCodeSet d m n₀ j x,
          witnessWeight c (treeCodeOutput (.inr b))) ≤
        ∑ b ∈ branchNearSet d m n₀ j x,
          ∏ i, witnessWeight c ((b.2 i).val) := by
      rw [hsumEq]
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro b hb _
      exact Finset.prod_nonneg fun i hi => witnessWeight_nonneg c ((b.2 i).val)
    rw [branchNear_sum_eq] at hbranch
    have hinner (centers : Fin (historyChildren d j) → Torus d m) :
        (∏ i, ∑ L ∈ witnessFamily d m n₀ r (centers i), witnessWeight c L) ≤
          (witnessMass d m n₀ r c) ^ historyChildren d j := by
      simpa [r] using childFamily_product_le_mass_pow d m n₀ j c centers
    have hsumConst :
        (∑ centers ∈ centerOptionSet d m j x,
          ∏ i, ∑ L ∈ witnessFamily d m n₀ r (centers i), witnessWeight c L) ≤
        (centerOptionSet d m j x).card * (witnessMass d m n₀ r c) ^ historyChildren d j := by
      calc
        _ ≤ ∑ centers ∈ centerOptionSet d m j x,
            (witnessMass d m n₀ r c) ^ historyChildren d j :=
          Finset.sum_le_sum fun centers hcenters => hinner centers
        _ = _ := by simp
    have hcenterCard :
        ((centerOptionSet d m j x).card : ℝ) =
          (witnessBall d m j x).card ^ historyChildren d j := by
      have hcenterSet : centerOptionSet d m j x =
          Fintype.piFinset (fun _ : Fin (historyChildren d j) => witnessBall d m j x) := by
        ext centers
        simp [centerOptionSet, Fintype.mem_piFinset, witnessBall]
      have hcard : (centerOptionSet d m j x).card =
          (witnessBall d m j x).card ^ historyChildren d j := by
        rw [hcenterSet, Fintype.card_piFinset_const]
      exact_mod_cast hcard
    have hmass : 0 ≤ witnessMass d m n₀ r c := witnessMass_nonneg d m n₀ r c
    have hbase : (witnessBall d m j x).card * witnessMass d m n₀ r c ≤
        C * witnessRadius j ^ d * witnessMass d m n₀ r c :=
      mul_le_mul_of_nonneg_right hball hmass
    have hpow :
        ((witnessBall d m j x).card * witnessMass d m n₀ r c) ^ historyChildren d j ≤
        (C * witnessRadius j ^ d * witnessMass d m n₀ r c) ^ historyChildren d j :=
      pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hmass) hbase _
    calc
      (∑ b ∈ branchCodeSet d m n₀ j x,
        witnessWeight c (treeCodeOutput (.inr b))) ≤
        (centerOptionSet d m j x).card * (witnessMass d m n₀ r c) ^ historyChildren d j :=
          hbranch.trans hsumConst
      _ = ((witnessBall d m j x).card * witnessMass d m n₀ r c) ^ historyChildren d j := by
        rw [hcenterCard, ← mul_pow]
      _ ≤ if n₀ ≤ historyEarlier d j then
            (C * witnessRadius j ^ d * witnessMass d m n₀ (historyEarlier d j) c) ^
              historyChildren d j else 0 := by
        simpa [hr, r] using hpow
  · have hempty : branchCodeSet d m n₀ j x = ∅ := by
      ext b
      simp [branchCodeSet, treeCodeValid, hr]
    simp [hr, hempty]

end AndersonAC.S78WRec
