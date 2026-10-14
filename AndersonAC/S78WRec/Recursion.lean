import AndersonAC.S78.Definitions

open scoped BigOperators

noncomputable section

namespace AndersonAC.S78WRec

open AndersonAC.S78

lemma birthBound_pos (c : ℝ) (j : ℕ) : 0 < birthBound c j := by
  exact Real.exp_pos _

lemma witnessWeight_pos {ι : Type} (c : ℝ) (L : Finset (BirthLabel ι)) :
    0 < witnessWeight c L := by
  classical
  unfold witnessWeight
  apply Finset.prod_pos
  intro a ha
  exact birthBound_pos c a.scale

lemma witnessWeight_nonneg {ι : Type} (c : ℝ) (L : Finset (BirthLabel ι)) :
    0 ≤ witnessWeight c L := (witnessWeight_pos c L).le

lemma birthBound_antitone_of_pos {c : ℝ} (hc : 0 < c) {a b : ℕ} (hab : a ≤ b) :
    birthBound c b ≤ birthBound c a := by
  unfold birthBound
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hab) hc.le

lemma sum_map_le_of_injOn {α β : Type} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (e : α → β)
    (he : ∀ a ∈ s, e a ∈ t) (hinj : Set.InjOn e s)
    (g : β → ℝ) (hg : ∀ b ∈ t, 0 ≤ g b) :
    (∑ a ∈ s, g (e a)) ≤ ∑ b ∈ t, g b := by
  classical
  calc
    (∑ a ∈ s, g (e a)) = ∑ b ∈ s.image e, g b := (Finset.sum_image hinj).symm
    _ ≤ ∑ b ∈ t, g b :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr he)
        (fun b hb _ => hg b hb)

lemma witnessWeight_union_of_disjoint {ι : Type} [DecidableEq ι] (c : ℝ)
    (L K : Finset (BirthLabel ι)) (hLK : Disjoint L K) :
    witnessWeight c (L ∪ K) = witnessWeight c L * witnessWeight c K := by
  classical
  rw [witnessWeight, Finset.prod_union hLK]
  rfl

lemma witness_scale_le {d m n₀ j : ℕ} {x : Torus d m}
    {L : Finset (BirthLabel (Torus d m))}
    (h : IsWitness d m n₀ j x L) :
    ∀ a ∈ L, a.scale ≤ j := by
  induction h with
  | leaf j x a hj hs hnear =>
      intro b hb
      simp only [Finset.mem_singleton] at hb
      subst b
      exact hs.2.1
  | @branch j x hj hr hdec centers leaves hnear hsep children ih =>
      intro a ha
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at ha
      obtain ⟨i, hai⟩ := ha
      exact (ih i a hai).trans hdec.le

lemma label_mem_possibleLabels {d m j : ℕ} (a : BirthLabel (Torus d m))
    (ha : a.scale ≤ j) : a ∈ possibleLabels d m j := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨((a.scale, a.kind), a.anchor), ?_, ?_⟩
  · simp [ha]
  · cases a
    rfl

lemma witness_mem_family {d m n₀ j : ℕ} {x : Torus d m}
    {L : Finset (BirthLabel (Torus d m))}
    (h : IsWitness d m n₀ j x L) :
    L ∈ witnessFamily d m n₀ j x := by
  classical
  simp only [witnessFamily, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · intro a ha
    exact label_mem_possibleLabels a (witness_scale_le h a ha)
  · exact h

end AndersonAC.S78WRec
