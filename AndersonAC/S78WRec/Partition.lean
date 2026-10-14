import AndersonAC.S78WRec.Recursion

open scoped BigOperators

noncomputable section

namespace AndersonAC.S78WRec

open AndersonAC.S78

abbrev LabelCode (d m j : ℕ) :=
  {a : BirthLabel (Torus d m) // a ∈ possibleLabels d m j}

abbrev ChildChoice (d m n₀ r : ℕ) (x : Torus d m) :=
  {L : Finset (BirthLabel (Torus d m)) // L ∈ witnessFamily d m n₀ r x}

abbrev BranchCode (d m n₀ j : ℕ) :=
  Σ centers : Fin (historyChildren d j) → Torus d m,
    (i : Fin (historyChildren d j)) →
      ChildChoice d m n₀ (historyEarlier d j) (centers i)

abbrev TreeCode (d m n₀ j : ℕ) := LabelCode d m j ⊕ BranchCode d m n₀ j

def treeCodeValid (d m n₀ j : ℕ) (x : Torus d m) : TreeCode d m n₀ j → Prop
  | .inl a =>
      n₀ < j ∧ n₀ < a.val.scale ∧ a.val.scale ≤ j ∧ historyEarlier d j < a.val.scale ∧
        physicalDistance d m x a.val.anchor ≤ witnessRadius j / 2
  | .inr b =>
      n₀ < j ∧ n₀ ≤ historyEarlier d j ∧ historyEarlier d j < j ∧
        (∀ i, physicalDistance d m x (b.1 i) ≤ witnessRadius j / 2) ∧
        (∀ i l, i ≠ l → 3 * witnessRadius (historyEarlier d j) <
          physicalDistance d m (b.1 i) (b.1 l))

def treeCodeOutput {d m n₀ j : ℕ} : TreeCode d m n₀ j → Finset (BirthLabel (Torus d m))
  | .inl a => {a.val}
  | .inr b => Finset.univ.biUnion (fun i => (b.2 i).val)

def treeCodeSet (d m n₀ j : ℕ) (x : Torus d m) : Finset (TreeCode d m n₀ j) := by
  classical
  exact Finset.univ.filter (treeCodeValid d m n₀ j x)

def leafCodeSet (d m n₀ j : ℕ) (x : Torus d m) : Finset (LabelCode d m j) := by
  classical
  exact Finset.univ.filter (fun a => treeCodeValid d m n₀ j x (.inl a))

def branchCodeSet (d m n₀ j : ℕ) (x : Torus d m) : Finset (BranchCode d m n₀ j) := by
  classical
  exact Finset.univ.filter (fun b => treeCodeValid d m n₀ j x (.inr b))

lemma treeCodeSet_eq_image_union (d m n₀ j : ℕ) (x : Torus d m)
    [DecidableEq (LabelCode d m j)] [DecidableEq (BranchCode d m n₀ j)]
    [DecidableEq (TreeCode d m n₀ j)] :
    treeCodeSet d m n₀ j x =
      (leafCodeSet d m n₀ j x).image Sum.inl ∪
        (branchCodeSet d m n₀ j x).image Sum.inr := by
  classical
  ext code
  cases code with
  | inl a => simp [treeCodeSet, leafCodeSet, branchCodeSet]
  | inr b => simp [treeCodeSet, leafCodeSet, branchCodeSet]

lemma witness_of_mem_family {d m n₀ j : ℕ} {x : Torus d m}
    {L : Finset (BirthLabel (Torus d m))}
    (h : L ∈ witnessFamily d m n₀ j x) : IsWitness d m n₀ j x L := by
  classical
  simp only [witnessFamily, Finset.mem_filter, Finset.mem_powerset] at h
  exact h.2

lemma valid_treeCode_isWitness {d m n₀ j : ℕ} {x : Torus d m}
    {code : TreeCode d m n₀ j} (h : treeCodeValid d m n₀ j x code) :
    IsWitness d m n₀ j x (treeCodeOutput code) := by
  cases code with
  | inl a =>
      rcases h with ⟨hj, hs₀, hs₁, hs₂, hn⟩
      exact IsWitness.leaf j x a.val hj ⟨hs₀, hs₁, hs₂⟩ hn
  | inr b =>
      rcases b with ⟨centers, children⟩
      rcases h with ⟨hj, hr, hdec, hn, hs⟩
      have hw : ∀ i, IsWitness d m n₀ (historyEarlier d j) (centers i)
          (children i).val := fun i => witness_of_mem_family (children i).property
      exact IsWitness.branch j x hj hr hdec centers (fun i => (children i).val) hn hs hw

lemma treeCode_mem_set {d m n₀ j : ℕ} {x : Torus d m}
    {code : TreeCode d m n₀ j} (h : treeCodeValid d m n₀ j x code) :
    code ∈ treeCodeSet d m n₀ j x := by
  classical
  simp [treeCodeSet, h]

lemma treeCode_output_mem_family {d m n₀ j : ℕ} {x : Torus d m}
    {code : TreeCode d m n₀ j} (h : treeCodeValid d m n₀ j x code) :
    treeCodeOutput code ∈ witnessFamily d m n₀ j x :=
  witness_mem_family (valid_treeCode_isWitness h)

lemma exists_treeCode_of_witness {d m n₀ j : ℕ} {x : Torus d m}
    {L : Finset (BirthLabel (Torus d m))}
    (h : IsWitness d m n₀ j x L) :
    ∃ code ∈ treeCodeSet d m n₀ j x, treeCodeOutput code = L := by
  cases h with
  | leaf j x a hj hs hn =>
      have hscale : a ∈ possibleLabels d m j := label_mem_possibleLabels a hs.2.1
      refine ⟨.inl ⟨a, hscale⟩, treeCode_mem_set ?_, rfl⟩
      exact ⟨hj, hs.1, hs.2.1, hs.2.2, hn⟩
  | branch j x hj hr hdec centers leaves hn hs hc =>
      let children : (i : Fin (historyChildren d j)) →
          ChildChoice d m n₀ (historyEarlier d j) (centers i) :=
        fun i => ⟨leaves i, witness_mem_family (hc i)⟩
      refine ⟨.inr ⟨centers, children⟩, treeCode_mem_set ?_, ?_⟩
      · exact ⟨hj, hr, hdec, hn, hs⟩
      · simp [treeCodeOutput, children]

lemma exists_treeCode_of_mem_family {d m n₀ j : ℕ} {x : Torus d m}
    {L : Finset (BirthLabel (Torus d m))}
    (h : L ∈ witnessFamily d m n₀ j x) :
    ∃ code ∈ treeCodeSet d m n₀ j x, treeCodeOutput code = L :=
  exists_treeCode_of_witness (witness_of_mem_family h)

lemma treeCodeSet_sum_eq (d m n₀ j : ℕ) (x : Torus d m) (c : ℝ) :
    (∑ code ∈ treeCodeSet d m n₀ j x, witnessWeight c (treeCodeOutput code)) =
      (∑ a ∈ leafCodeSet d m n₀ j x, birthBound c a.val.scale) +
        ∑ b ∈ branchCodeSet d m n₀ j x,
          witnessWeight c (treeCodeOutput (.inr b)) := by
  classical
  have hdisj : Disjoint
      ((leafCodeSet d m n₀ j x).image Sum.inl)
      ((branchCodeSet d m n₀ j x).image Sum.inr) := by
    apply Finset.disjoint_left.mpr
    intro code hleft hright
    rcases Finset.mem_image.mp hleft with ⟨a, _, rfl⟩
    rcases Finset.mem_image.mp hright with ⟨b, _, heq⟩
    cases heq
  have hinjL : Set.InjOn (Sum.inl : LabelCode d m j → TreeCode d m n₀ j)
      (leafCodeSet d m n₀ j x) := by
    intro a _ b _ h
    exact Sum.inl.inj h
  have hinjB : Set.InjOn (Sum.inr : BranchCode d m n₀ j → TreeCode d m n₀ j)
      (branchCodeSet d m n₀ j x) := by
    intro a _ b _ h
    exact Sum.inr.inj h
  rw [treeCodeSet_eq_image_union, Finset.sum_union hdisj,
    Finset.sum_image hinjL, Finset.sum_image hinjB]
  simp [treeCodeOutput, witnessWeight]

lemma witnessFamily_sum_le_treeCodeSet_sum {d m n₀ j : ℕ} {x : Torus d m}
    (c : ℝ) :
    (∑ L ∈ witnessFamily d m n₀ j x, witnessWeight c L) ≤
      ∑ code ∈ treeCodeSet d m n₀ j x, witnessWeight c (treeCodeOutput code) := by
  classical
  let F := witnessFamily d m n₀ j x
  let enc : {L : Finset (BirthLabel (Torus d m)) // L ∈ F} → TreeCode d m n₀ j :=
    fun L => Classical.choose (exists_treeCode_of_mem_family L.property)
  have hspec (L : {L : Finset (BirthLabel (Torus d m)) // L ∈ F}) :
      enc L ∈ treeCodeSet d m n₀ j x ∧ treeCodeOutput (enc L) = L.val :=
    Classical.choose_spec (exists_treeCode_of_mem_family L.property)
  have hinj : Set.InjOn enc F.attach := by
    intro a ha b hb hab
    have hval := congrArg treeCodeOutput hab
    rw [(hspec a).2, (hspec b).2] at hval
    exact Subtype.ext hval
  have hsum := sum_map_le_of_injOn F.attach (treeCodeSet d m n₀ j x) enc
    (fun L _ => (hspec L).1) hinj
    (fun code => witnessWeight c (treeCodeOutput code))
    (fun code _ => witnessWeight_nonneg c (treeCodeOutput code))
  calc
    (∑ L ∈ F, witnessWeight c L) =
        ∑ L ∈ F.attach, witnessWeight c L.val := by rw [← Finset.sum_attach]
    _ = ∑ L ∈ F.attach, witnessWeight c (treeCodeOutput (enc L)) := by
      apply Finset.sum_congr rfl
      intro L hL
      rw [(hspec L).2]
    _ ≤ ∑ code ∈ treeCodeSet d m n₀ j x,
        witnessWeight c (treeCodeOutput code) := hsum

end AndersonAC.S78WRec
