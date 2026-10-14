import AndersonAC.S3WCube.Proof

/-! Reflection energy control and the cube embedding for Lemma 3.3. -/

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace AndersonAC.AgentS3
open AndersonAC.S3

/-- The folded cube point of a torus site. -/
def foldPt {d l : ℕ} [NeZero (2 * l)] (x : Torus d (2 * l)) : Cube d l :=
  fun j => ⟨foldCoordinate l (x j), by
    have hx := (x j).val_lt
    unfold foldCoordinate
    split_ifs <;> omega⟩

lemma reflected_eq_foldPt {d l : ℕ} (hl : 0 < l) [NeZero (2 * l)]
    (v : Cube d l → ℂ) (x : Torus d (2 * l)) :
    reflected hl v x = v (foldPt x) - cubeMean v := rfl

lemma val_add_one_cases {n : ℕ} [NeZero n] (hn : 2 ≤ n) (c : ZMod n) :
    ((c + 1).val = c.val + 1 ∧ c.val + 1 < n) ∨
      ((c + 1).val = 0 ∧ c.val + 1 = n) := by
  have hc := c.val_lt
  have h1 : (1 : ZMod n).val = 1 := by
    rw [ZMod.val_one_eq_one_mod]
    exact Nat.mod_eq_of_lt (by omega)
  rw [ZMod.val_add, h1]
  rcases Nat.lt_or_ge (c.val + 1) n with h | h
  · exact Or.inl ⟨Nat.mod_eq_of_lt h, h⟩
  · have he : c.val + 1 = n := by omega
    refine Or.inr ⟨?_, he⟩
    rw [he, Nat.mod_self]

lemma fold_succ_cases {l : ℕ} (hl : 0 < l) [NeZero (2 * l)] (c : ZMod (2 * l)) :
    foldCoordinate l (c + 1) = foldCoordinate l c ∨
      foldCoordinate l (c + 1) = foldCoordinate l c + 1 ∨
      foldCoordinate l (c + 1) + 1 = foldCoordinate l c := by
  have hc := c.val_lt
  rcases val_add_one_cases (n := 2 * l) (by omega) c with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  · unfold foldCoordinate
    rw [h1]
    split_ifs <;> omega

lemma foldPt_add_basisStep_ne {d l : ℕ} [NeZero (2 * l)]
    (x : Torus d (2 * l)) {j k : Fin d} (hkj : k ≠ j) :
    foldPt (x + basisStep j) k = foldPt x k := by
  apply Fin.ext
  simp [foldPt, basisStep, hkj]

lemma foldPt_add_basisStep_self {d l : ℕ} [NeZero (2 * l)]
    (x : Torus d (2 * l)) (j : Fin d) :
    (foldPt (x + basisStep j) j).val = foldCoordinate l (x j + 1) := by
  simp [foldPt, basisStep]

lemma foldPt_adjacent {d l : ℕ} (hl : 0 < l) [NeZero (2 * l)]
    (x : Torus d (2 * l)) (j : Fin d) (hne : foldPt (x + basisStep j) ≠ foldPt x) :
    cubeAdjacent (foldPt x) (foldPt (x + basisStep j)) := by
  refine ⟨j, fun k hk => (foldPt_add_basisStep_ne x hk).symm, ?_⟩
  have hj : foldPt (x + basisStep j) j ≠ foldPt x j := by
    intro h
    apply hne
    funext k
    by_cases hk : k = j
    · subst hk; exact h
    · exact foldPt_add_basisStep_ne x hk
  have hjv : foldCoordinate l (x j + 1) ≠ foldCoordinate l (x j) := by
    intro h
    apply hj
    apply Fin.ext
    rw [foldPt_add_basisStep_self]
    simpa [foldPt] using h
  have hxv : ((foldPt x j).val : ℕ) = foldCoordinate l (x j) := rfl
  rw [foldPt_add_basisStep_self, hxv]
  rcases fold_succ_cases hl (x j) with h | h | h
  · exact absurd h hjv
  · rw [h]; push_cast; simp
  · rw [← h]; push_cast; simp

lemma foldPt_step_injOn {d l : ℕ} [NeZero (2 * l)] (x : Torus d (2 * l)) :
    Set.InjOn (fun j : Fin d => foldPt (x + basisStep j))
      {j | foldPt (x + basisStep j) ≠ foldPt x} := by
  intro j hj k hk hjk
  by_contra hne
  have hj' : foldPt (x + basisStep j) j ≠ foldPt x j := by
    intro h
    apply hj
    funext i
    by_cases hi : i = j
    · subst hi; exact h
    · exact foldPt_add_basisStep_ne x hi
  apply hj'
  have h1 : foldPt (x + basisStep k) j = foldPt x j :=
    foldPt_add_basisStep_ne x hne
  simpa [hjk] using h1

/-- The sum of nearest-neighbour terms at a cube point. -/
def cubeNeighbourSum {d l : ℕ} (v : Cube d l → ℂ) (y : Cube d l) : ℝ :=
  ∑ y', if cubeAdjacent y y' then ‖v y - v y'‖ ^ 2 else 0

lemma cubeNeighbourSum_nonneg {d l : ℕ} (v : Cube d l → ℂ) (y : Cube d l) :
    0 ≤ cubeNeighbourSum v y := by
  unfold cubeNeighbourSum
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

lemma cubeEnergy_eq_neighbour {d l : ℕ} (v : Cube d l → ℂ) :
    cubeEnergy v = (1 / 2) * ∑ y, cubeNeighbourSum v y := rfl

lemma cubeEnergy_nonneg {d l : ℕ} (v : Cube d l → ℂ) : 0 ≤ cubeEnergy v := by
  rw [cubeEnergy_eq_neighbour]
  exact mul_nonneg (by norm_num)
    (Finset.sum_nonneg (fun y _ => cubeNeighbourSum_nonneg v y))

lemma step_sum_le_neighbour {d l : ℕ} (hl : 0 < l) [NeZero (2 * l)]
    (v : Cube d l → ℂ) (x : Torus d (2 * l)) :
    (∑ j : Fin d, ‖v (foldPt (x + basisStep j)) - v (foldPt x)‖ ^ 2) ≤
      cubeNeighbourSum v (foldPt x) := by
  set y := foldPt x
  set φ : Fin d → Cube d l := fun j => foldPt (x + basisStep j)
  set g : Cube d l → ℝ := fun y' => ‖v y - v y'‖ ^ 2
  set J : Finset (Fin d) := Finset.univ.filter (fun j => φ j ≠ y)
  have hterm : ∀ j, ‖v (φ j) - v y‖ ^ 2 = g (φ j) := by
    intro j; simp only [g]; rw [norm_sub_rev]
  have h1 : (∑ j : Fin d, ‖v (φ j) - v y‖ ^ 2) = ∑ j ∈ J, g (φ j) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with h
    · exact hterm j
    · push Not at h
      rw [h]; simp
  have hinj : Set.InjOn φ J := by
    intro a ha b hb hab
    exact foldPt_step_injOn x (by simpa [J] using ha) (by simpa [J] using hb) hab
  have h2 : (∑ j ∈ J, g (φ j)) = ∑ y' ∈ J.image φ, g y' :=
    (Finset.sum_image (fun a ha b hb hab => hinj ha hb hab)).symm
  have hsub : J.image φ ⊆ Finset.univ.filter (fun y' => cubeAdjacent y y') := by
    intro y' hy'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact foldPt_adjacent hl x j (by simpa [J] using hj)
  have h3 : (∑ y' ∈ J.image φ, g y') ≤
      ∑ y' ∈ Finset.univ.filter (fun y' => cubeAdjacent y y'), g y' :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have h4 : (∑ y' ∈ Finset.univ.filter (fun y' => cubeAdjacent y y'), g y') =
      cubeNeighbourSum v y := by
    rw [Finset.sum_filter]
    unfold cubeNeighbourSum
    rfl
  calc (∑ j : Fin d, ‖v (foldPt (x + basisStep j)) - v (foldPt x)‖ ^ 2)
      = ∑ j : Fin d, ‖v (φ j) - v y‖ ^ 2 := rfl
    _ = ∑ j ∈ J, g (φ j) := h1
    _ = ∑ y' ∈ J.image φ, g y' := h2
    _ ≤ _ := h3
    _ = _ := h4

lemma foldPt_sum_real {d l : ℕ} (hl : 0 < l) [NeZero (2 * l)]
    (f : Cube d l → ℝ) :
    (∑ x : Torus d (2 * l), f (foldPt x)) = (2 : ℝ) ^ d * ∑ y, f y := by
  calc
    (∑ x : Torus d (2 * l), f (foldPt x))
        = ∑ x : Torus d (2 * l), f (foldPiEquiv hl x).1 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [foldPiEquiv_fst]
          rfl
    _ = ∑ p : Cube d l × (Fin d → Fin 2), f p.1 := by
          refine Fintype.sum_equiv (foldPiEquiv hl) _ _ (fun x => ?_)
          rfl
    _ = (2 : ℝ) ^ d * ∑ y, f y := by
          rw [Fintype.sum_prod_type]
          simp [Fintype.card_fin, Finset.sum_const, Finset.mul_sum]

/-- Reflected gradient energy is controlled by the cube energy (with a factor-two loss). -/
theorem reflected_gradientEnergy_le {d l : ℕ} (hl : 0 < l) [NeZero (2 * l)]
    (v : Cube d l → ℂ) :
    gradientEnergy (reflected hl v) ≤ (2 : ℝ) ^ (d + 1) * cubeEnergy v := by
  unfold gradientEnergy
  have hstep : ∀ x : Torus d (2 * l), ∀ j : Fin d,
      reflected hl v (x + basisStep j) - reflected hl v x =
        v (foldPt (x + basisStep j)) - v (foldPt x) := by
    intro x j
    rw [reflected_eq_foldPt, reflected_eq_foldPt]
    ring
  simp_rw [hstep]
  calc
    (∑ x : Torus d (2 * l), ∑ j : Fin d,
        ‖v (foldPt (x + basisStep j)) - v (foldPt x)‖ ^ 2)
        ≤ ∑ x : Torus d (2 * l), cubeNeighbourSum v (foldPt x) :=
          Finset.sum_le_sum (fun x _ => step_sum_le_neighbour hl v x)
    _ = (2 : ℝ) ^ d * ∑ y, cubeNeighbourSum v y := foldPt_sum_real hl _
    _ = (2 : ℝ) ^ (d + 1) * cubeEnergy v := by
          rw [cubeEnergy_eq_neighbour, pow_succ]
          ring

/-- The cube embedded in the first orthant of the doubled torus. -/
def cubeEmbed {d l : ℕ} (x : Cube d l) : Torus d (2 * l) :=
  fun j => ((x j).val : ZMod (2 * l))

lemma foldPt_cubeEmbed {d l : ℕ} [NeZero (2 * l)] (x : Cube d l) :
    foldPt (cubeEmbed x) = x := by
  funext j
  apply Fin.ext
  have hlt : (x j).val < 2 * l := by have := (x j).isLt; omega
  have hval : ((x j).val : ZMod (2 * l)).val = (x j).val := ZMod.val_cast_of_lt hlt
  simp only [foldPt, cubeEmbed, foldCoordinate, hval]
  simp [(x j).isLt]

lemma cubeEmbed_injective {d l : ℕ} [NeZero (2 * l)] :
    Function.Injective (cubeEmbed (d := d) (l := l)) := by
  intro x y h
  rw [← foldPt_cubeEmbed x, ← foldPt_cubeEmbed y, h]

lemma reflected_cubeEmbed {d l : ℕ} (hl : 0 < l) [NeZero (2 * l)]
    (v : Cube d l → ℂ) (x : Cube d l) :
    reflected hl v (cubeEmbed x) = v x - cubeMean v := by
  rw [reflected_eq_foldPt, foldPt_cubeEmbed]

lemma sum_cubeEmbed_le {d l : ℕ} [NeZero (2 * l)]
    (g : Torus d (2 * l) → ℝ) (hg : ∀ x, 0 ≤ g x) :
    (∑ x : Cube d l, g (cubeEmbed x)) ≤ ∑ y, g y := by
  classical
  rw [← Finset.sum_image (fun a _ b _ hab => cubeEmbed_injective hab)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun y _ _ => hg y)

end AndersonAC.AgentS3
