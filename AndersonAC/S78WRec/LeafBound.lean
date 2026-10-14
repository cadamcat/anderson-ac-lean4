import AndersonAC.S78WRec.WitnessRecursion

open scoped BigOperators

noncomputable section

namespace AndersonAC.S78WRec

open AndersonAC.S78

def recursionConstant (d : ℕ) : ℝ :=
  (Fintype.card BirthType : ℝ) * (3 : ℝ) ^ d

lemma recursionConstant_ge_one (d : ℕ) : 1 ≤ recursionConstant d := by
  have htypes : (1 : ℝ) ≤ (Fintype.card BirthType : ℝ) := by
    have hpos : 0 < Fintype.card BirthType := Fintype.card_pos_iff.mpr ⟨BirthType.tile⟩
    exact_mod_cast (Nat.succ_le_iff.mpr hpos)
  have hpow : (1 : ℝ) ≤ (3 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  dsimp [recursionConstant]
  calc
    1 = 1 * 1 := by ring
    _ ≤ (Fintype.card BirthType : ℝ) * (3 : ℝ) ^ d :=
      mul_le_mul htypes hpow (by norm_num) (by positivity)

lemma witnessBall_card_real_le (d m j : ℕ) (x : Torus d m) (hm : 1 ≤ m) :
    ((witnessBall d m j x).card : ℝ) ≤ (3 : ℝ) ^ d * witnessRadius j ^ d := by
  have hconn := nnGraph_connected d m hm
  have hnat := witnessBall_card_le d m j x hconn
  have hcast : ((witnessBall d m j x).card : ℝ) ≤
      ((3 * 4 ^ (10 * j)) ^ d : ℝ) := by
    exact_mod_cast hnat
  calc
    ((witnessBall d m j x).card : ℝ) ≤ ((3 * 4 ^ (10 * j)) ^ d : ℝ) := hcast
    _ = (3 : ℝ) ^ d * witnessRadius j ^ d := by
      simp [witnessRadius, mul_pow]

lemma leafCodeSet_card_le (d m n₀ j : ℕ) (x : Torus d m) :
    (leafCodeSet d m n₀ j x).card ≤
      j * Fintype.card BirthType * (witnessBall d m j x).card := by
  classical
  let choices : Finset ((ℕ × BirthType) × Torus d m) :=
    (Finset.Ico 1 (j + 1) ×ˢ (Finset.univ : Finset BirthType)) ×ˢ
      witnessBall d m j x
  let encode : LabelCode d m j → (ℕ × BirthType) × Torus d m :=
    fun a => ((a.val.scale, a.val.kind), a.val.anchor)
  have hmaps : Set.MapsTo encode (leafCodeSet d m n₀ j x) choices := by
    intro a ha
    have hv := (Finset.mem_filter.mp ha).2
    rcases hv with ⟨_, hn₀, hscale, _, hnear⟩
    apply Finset.mem_product.mpr
    refine ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnear⟩⟩
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩, Finset.mem_univ _⟩
    · have hpos : 0 < a.val.scale := by omega
      exact Nat.one_le_iff_ne_zero.mpr hpos.ne'
    · exact Nat.lt_succ_of_le hscale
  have hinj : Set.InjOn encode (leafCodeSet d m n₀ j x) := by
    intro a ha b hb heq
    rcases a with ⟨a, ha'⟩
    rcases b with ⟨b, hb'⟩
    apply Subtype.ext
    cases a with
    | mk aScale aKind aAnchor =>
      cases b with
      | mk bScale bKind bAnchor =>
        simp [encode, Prod.mk.injEq] at heq
        rcases heq with ⟨⟨rfl, rfl⟩, rfl⟩
        rfl
  calc
    (leafCodeSet d m n₀ j x).card ≤ choices.card :=
      Finset.card_le_card_of_injOn encode hmaps hinj
    _ = j * Fintype.card BirthType * (witnessBall d m j x).card := by
      simp [choices]

lemma leafCodeSet_sum_le (d m n₀ j : ℕ) (x : Torus d m) (c : ℝ)
    (hc : 0 < c) (hm : 1 ≤ m) :
    (∑ a ∈ leafCodeSet d m n₀ j x, birthBound c a.val.scale) ≤
      recursionConstant d * (j : ℝ) * witnessRadius j ^ d *
        birthBound c (max n₀ (historyEarlier d j)) := by
  classical
  let C := recursionConstant d
  let r := historyEarlier d j
  let p := birthBound c (max n₀ r)
  have hpoint : ∀ a ∈ leafCodeSet d m n₀ j x,
      birthBound c a.val.scale ≤ p := by
    intro a ha
    rcases (Finset.mem_filter.mp ha).2 with ⟨_, hn₀, hscale, hearlier, _⟩
    apply birthBound_antitone_of_pos hc
    exact le_of_lt (max_lt_iff.mpr ⟨hn₀, hearlier⟩)
  have hsum :
      (∑ a ∈ leafCodeSet d m n₀ j x, birthBound c a.val.scale) ≤
        ((leafCodeSet d m n₀ j x).card : ℝ) * p := by
    calc
      _ ≤ ∑ a ∈ leafCodeSet d m n₀ j x, p :=
        Finset.sum_le_sum fun a ha => hpoint a ha
      _ = _ := by simp
  have hcard : ((leafCodeSet d m n₀ j x).card : ℝ) ≤
      (j : ℝ) * (Fintype.card BirthType : ℝ) * (witnessBall d m j x).card := by
    exact_mod_cast leafCodeSet_card_le d m n₀ j x
  have hball := witnessBall_card_real_le d m j x hm
  have hcard' : ((leafCodeSet d m n₀ j x).card : ℝ) ≤
      C * (j : ℝ) * witnessRadius j ^ d := by
    calc
      _ ≤ (j : ℝ) * (Fintype.card BirthType : ℝ) *
          ((3 : ℝ) ^ d * witnessRadius j ^ d) := by
            have hmul :
                (j : ℝ) * (Fintype.card BirthType : ℝ) * (witnessBall d m j x).card ≤
                  (j : ℝ) * (Fintype.card BirthType : ℝ) *
                    ((3 : ℝ) ^ d * witnessRadius j ^ d) := by
              exact mul_le_mul_of_nonneg_left hball (by positivity)
            exact hcard.trans hmul
      _ = C * (j : ℝ) * witnessRadius j ^ d := by
        dsimp [C, recursionConstant]
        ring
  calc
    (∑ a ∈ leafCodeSet d m n₀ j x, birthBound c a.val.scale) ≤
        ((leafCodeSet d m n₀ j x).card : ℝ) * p := hsum
    _ ≤ C * (j : ℝ) * witnessRadius j ^ d * p :=
      mul_le_mul_of_nonneg_right hcard' (birthBound_pos c _).le

end AndersonAC.S78WRec
