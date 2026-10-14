import AndersonAC.AgentS78.Construction.StagePhaseTrace

/-!
# The Schur support of the committed matrix after a DONE clearing. `clearingDoneHops_proof : ClearingDoneHopsStatement d`. Along the block, with
`E = terminal ∪ (active ∖ provisional active)` (the sites eliminated so far), every entry of the
provisional matrix `Mnum` between committed active sites differs from the lattice hop `J` only at
zero terminal distance for `E`: an elimination at `p` changes `(a, b)` only through
`Mnum a p · Mnum p b ≠ 0`, and each nonzero factor gives terminal distance `0` to `p ∈ E`
(a lattice hop to a terminal, or the invariant); then the triangle inequality. At DONE the
eliminated sites are the removed sites `core ∪ inspected`, contained in the new terminal set.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.AgentS78Geo (terminalDistance_triangle terminalDistance_adj_terminal
  terminalDistance_antitone terminalDistance_self terminalDistance_nonneg)
open AndersonAC.S2 (RandomSources Query Answer)

variable {d m : ℕ}

/-- The hop invariant of a provisional matrix on the committed active set. -/
def HopInv (x : RunRecord d m) (J : Matrix (Torus d m) (Torus d m) ℝ) (A : Finset (Torus d m))
    (M : Matrix (Torus d m) (Torus d m) ℝ) : Prop :=
  ∀ a ∈ x.endpoint.active, ∀ b ∈ x.endpoint.active, M a b ≠ J a b →
    terminalDistance (nnGraph d m) (x.terminal ∪ (x.endpoint.active \ A)) a b = 0

/-- One elimination keeps the hop invariant. -/
theorem hopInv_elim (x : RunRecord d m) (J : Matrix (Torus d m) (Torus d m) ℝ)
    (hJ : ∀ a b, J a b ≠ 0 → (nnGraph d m).Adj a b) (sc : ClearScratch d m) (p : Torus d m)
    (hp : p ∈ x.endpoint.active) (t : ℝ) (r : Torus d m → ℂ) (ξ : ℝ)
    (h : HopInv x J sc.active sc.Mnum) :
    HopInv x J (sc.active.erase p) (elimStep (d := d) (m := m) t r sc p ξ).1 := by
  have hconn : (nnGraph d m).Connected := AndersonAC.SolS78.nnGraph_connected_proof
  set E := x.terminal ∪ (x.endpoint.active \ sc.active)
  set E' := x.terminal ∪ (x.endpoint.active \ sc.active.erase p)
  have hEE' : E ⊆ E' := by
    apply Finset.union_subset_union (Finset.Subset.refl _)
    exact Finset.sdiff_subset_sdiff (Finset.Subset.refl _) (Finset.erase_subset _ _)
  have hpE' : p ∈ E' :=
    Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hp, Finset.notMem_erase _ _⟩)
  have hzero : ∀ a b, terminalDistance (nnGraph d m) E a b = 0 →
      terminalDistance (nnGraph d m) E' a b = 0 := fun a b hab =>
    le_antisymm ((terminalDistance_antitone hconn hEE' a b).trans hab.le)
      (terminalDistance_nonneg _ _ _ _)
  -- a nonzero entry to `p` gives terminal distance zero to `p`
  have hto : ∀ a ∈ x.endpoint.active, sc.Mnum a p ≠ 0 →
      terminalDistance (nnGraph d m) E' a p = 0 := by
    intro a ha hap
    by_cases hJap : sc.Mnum a p = J a p
    · exact terminalDistance_adj_terminal _ _ (hJ a p (hJap ▸ hap)) (Or.inr hpE')
    · exact hzero a p (h a ha p hp hJap)
  have hfrom : ∀ b ∈ x.endpoint.active, sc.Mnum p b ≠ 0 →
      terminalDistance (nnGraph d m) E' p b = 0 := by
    intro b hb hpb
    by_cases hJpb : sc.Mnum p b = J p b
    · exact terminalDistance_adj_terminal _ _ (hJ p b (hJpb ▸ hpb)) (Or.inl hpE')
    · exact hzero p b (h p hp b hb hJpb)
  intro a ha b hb hab
  unfold elimStep schurStepM at hab
  dsimp only at hab
  by_cases hab' : a = b
  · subst hab'; exact terminalDistance_self _ _ _
  by_cases hp' : a = p ∨ b = p
  · rw [if_pos hp', if_neg hab'] at hab
    rcases hp' with rfl | rfl
    · exact terminalDistance_adj_terminal _ _ (hJ a b (fun h0 => hab h0.symm)) (Or.inl hpE')
    · exact terminalDistance_adj_terminal _ _ (hJ a b (fun h0 => hab h0.symm)) (Or.inr hpE')
  rw [if_neg hp'] at hab
  by_cases hold : sc.Mnum a b = J a b
  · have hprod : sc.Mnum a p * sc.Mnum p b ≠ 0 := by
      intro h0
      apply hab
      rw [h0, zero_div, sub_zero, hold]
    have h1 := hto a ha (left_ne_zero_of_mul hprod)
    have h2 := hfrom b hb (right_ne_zero_of_mul hprod)
    exact le_antisymm ((terminalDistance_triangle hconn _ a p b).trans (by rw [h1, h2]; norm_num))
      (terminalDistance_nonneg _ _ _ _)
  · exact hzero a b (h a ha b hb hold)

/-- Every update keeps the provisional data or eliminates one committed active site. -/
theorem clr_update_shape (n₀ j : ℕ) (u : ℝ) (s : RunRecord d m × ClearScratch d m)
    (a : Answer (Torus d m)) :
    ((clearingUpdate (d := d) (m := m) n₀ j u s a).2.active = s.2.active ∧
      (clearingUpdate (d := d) (m := m) n₀ j u s a).2.Mnum = s.2.Mnum) ∨
    ∃ p ξ, (p ∈ coupledActive s.1 ∨ (s.2.corePhase = true ∧ p ∈ s.2.coreLeft)) ∧
      (clearingUpdate (d := d) (m := m) n₀ j u s a).2.active = s.2.active.erase p ∧
      (clearingUpdate (d := d) (m := m) n₀ j u s a).2.Mnum =
        (elimStep (d := d) (m := m) (stageScale u j m) s.1.r s.2 p ξ).1 := by
  unfold clearingUpdate
  dsimp only
  split
  · exact Or.inl ⟨rfl, rfl⟩
  cases hact : actionOf (d := d) (m := m) j u s.1 s.2 with
  | fail po => exact Or.inl ⟨rfl, rfl⟩
  | coreReady => exact Or.inl ⟨rfl, rfl⟩
  | finish => exact Or.inl ⟨rfl, rfl⟩
  | coreQuery p hcp =>
    exact Or.inr ⟨p, _, Or.inr ⟨hcp, actionOf_coreQuery_mem j u s.1 s.2 p hcp hact⟩, rfl, rfl⟩
  | heat p hg =>
    dsimp only
    split_ifs
    all_goals exact Or.inr ⟨p, _, Or.inl hg.1, rfl, rfl⟩

/-- **The Schur support of the committed matrix.** -/
theorem clearingDoneHops_proof (d : ℕ) : ClearingDoneHopsStatement d := by
  intro m n₀ j u y x J hJ hDx hhops hcompl hab s hs hne hf hdn a ha b hb hab'
  have hconn : (nnGraph d m).Connected := AndersonAC.SolS78.nnGraph_connected_proof
  -- the hop invariant along the block
  have key : ∀ s', BlockReach (clearingBlock (d := d) (m := m) n₀ j u y) x s' →
      HopInv x J s'.2.active s'.2.Mnum := by
    intro s' h
    induction h with
    | enter =>
      intro a ha b hb hne'
      show terminalDistance (nnGraph d m) (x.terminal ∪ (x.endpoint.active \ x.endpoint.active)) a b = 0
      rw [Finset.sdiff_self, Finset.union_empty]
      apply hhops a ha b hb
      intro h0
      apply hne'
      have : (x.endpoint.M a b).re = J a b := by rw [h0]; simp
      exact this
    | step s₁ a₁ hs₁ _ ih =>
      have hx1 := (clr_reach n₀ j u y x s₁ hs₁).1
      have hI := clrInv_reach n₀ j u y x hDx s₁ hs₁
      rcases clr_update_shape n₀ j u s₁ a₁ with ⟨h1, h2⟩ | ⟨p, ξ, hp, h1, h2⟩
      · show HopInv x J (clearingUpdate (d := d) (m := m) n₀ j u s₁ a₁).2.active
          (clearingUpdate (d := d) (m := m) n₀ j u s₁ a₁).2.Mnum
        rw [h1, h2]; exact ih
      · show HopInv x J (clearingUpdate (d := d) (m := m) n₀ j u s₁ a₁).2.active
          (clearingUpdate (d := d) (m := m) n₀ j u s₁ a₁).2.Mnum
        rw [h1, h2]
        have hpx : p ∈ x.endpoint.active := by
          rcases hp with hp | ⟨hcp, hp⟩
          · rw [hx1] at hp; exact coupledActive_subset_active x hp
          · have := (hI.post hcp).1
            rw [← this] at hp
            exact hI.sub (Finset.mem_inter.mp hp).2
        rw [hx1]
        exact hopInv_elim x J hJ s₁.2 p hpx _ _ _ ih
  have hI := clrInv_reach n₀ j u y x hDx s hs
  have hx1 := (clr_reach n₀ j u y x s hs).1
  have ha' : a ∈ s.2.active := (Finset.mem_sdiff.mp ha).1
  have hb'' : b ∈ s.2.active := (Finset.mem_sdiff.mp hb).1
  have hMab : s.2.Mnum a b ≠ J a b := by
    intro h0
    apply hab'
    show (s.2.Mnum.map Complex.ofReal) a b = ((J a b : ℝ) : ℂ)
    rw [Matrix.map_apply, h0]
  have h0 := key s hs a (hI.sub ha') b (hI.sub hb'') hMab
  have hsub : x.terminal ∪ (x.endpoint.active \ s.2.active) ⊆ (clearingDoneExit x s.2).terminal := by
    show _ ⊆ x.terminal ∪ s.2.core ∪ s.2.inspected
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hz)
    · rcases Finset.mem_union.mp (hI.removed hz) with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
      · exact Finset.mem_union_right _ h
  exact le_antisymm ((terminalDistance_antitone hconn hsub a b).trans h0.le)
    (terminalDistance_nonneg _ _ _ _)

end AndersonAC.AgentS78
