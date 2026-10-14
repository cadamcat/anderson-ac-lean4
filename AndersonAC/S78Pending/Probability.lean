import AndersonAC.S78.Definitions
import AndersonAC.S78Hist.Closure

open scoped BigOperators ENNReal
open MeasureTheory
open AndersonAC.S78
set_option autoImplicit false
noncomputable section

namespace AndersonAC.SolS78

private theorem birthLabel_mem_possibleLabels {d m j : ℕ}
    (a : BirthLabel (Torus d m)) (ha : a.scale ≤ j) : a ∈ possibleLabels d m j := by
  classical
  change a ∈ ((Finset.range (j + 1) ×ˢ (Finset.univ : Finset BirthType)) ×ˢ
    (Finset.univ : Finset (Torus d m))).image
      (fun p => ⟨p.1.1, p.1.2, p.2⟩)
  apply Finset.mem_image.mpr
  refine ⟨((a.scale, a.kind), a.anchor), ?_, ?_⟩
  · simp [ha]
  · rfl

private theorem witness_mem_family_of_scale {d m n₀ j : ℕ} {x : Torus d m}
    {L : Finset (BirthLabel (Torus d m))} (hW : IsWitness d m n₀ j x L)
    (hscale : ∀ a ∈ L, a.scale ≤ j) : L ∈ witnessFamily d m n₀ j x := by
  classical
  change L ∈ (possibleLabels d m j).powerset.filter (IsWitness d m n₀ j x)
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun a ha => birthLabel_mem_possibleLabels a (hscale a ha), hW⟩

private theorem no_witness_at_initial_scale {d m n₀ : ℕ} {x : Torus d m}
    {L : Finset (BirthLabel (Torus d m))}
    (h : IsWitness d m n₀ n₀ x L) : False := by
  cases h <;> omega

/-- At the initial scale there are no witnesses, so the partition sum starts
at zero. -/
theorem witnessMass_initial (d m n₀ : ℕ) (c : ℝ) :
    witnessMass d m n₀ n₀ c = 0 := by
  classical
  have hempty (x : Torus d m) : witnessFamily d m n₀ n₀ x = ∅ := by
    dsimp [witnessFamily]
    apply Finset.filter_eq_empty_iff.mpr
    intro L _ hW
    exact no_witness_at_initial_scale hW
  have hsum (x : Torus d m) :
      (∑ L ∈ witnessFamily d m n₀ n₀ x, witnessWeight c L) = 0 := by
    simp [hempty x]
  let x₀ : Torus d m := fun _ => 0
  unfold witnessMass
  apply le_antisymm
  · apply csSup_le
    · exact ⟨0, ⟨x₀, by simp [hsum]⟩⟩
    · intro y hy
      rcases hy with ⟨x, rfl⟩
      simp [hsum]
  · have hbounded : BddAbove (Set.range fun x : Torus d m =>
        ∑ L ∈ witnessFamily d m n₀ n₀ x, witnessWeight c L) :=
      (Set.finite_range _).bddAbove
    exact le_csSup hbounded ⟨x₀, by simp [hsum]⟩

/-- The finite partition sum at every root is nonnegative; hence so is its
supremum over roots. -/
theorem witnessMass_nonneg (d m n₀ j : ℕ) (c : ℝ) :
    0 ≤ witnessMass d m n₀ j c := by
  classical
  let x₀ : Torus d m := fun _ => 0
  have hroot : 0 ≤ ∑ L ∈ witnessFamily d m n₀ j x₀, witnessWeight c L := by
    apply Finset.sum_nonneg
    intro L hL
    unfold witnessWeight birthBound
    exact Finset.prod_nonneg (fun a ha => Real.exp_nonneg _)
  unfold witnessMass
  exact hroot.trans (le_csSup ((Set.finite_range (fun x : Torus d m =>
    ∑ L ∈ witnessFamily d m n₀ j x, witnessWeight c L)).bddAbove) ⟨x₀, rfl⟩)

/-- The probability cost of all deterministic witnesses at one root is bounded
by the partition sum used in the history recursion. -/
theorem pending_by_witness_mass {d m n₀ j : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (H : PendingHistory d m n₀ Ω) (x : Torus d m) (c : ℝ)
    (hcover : ∀ ω ∈ H.pending j x,
      ∃ L ∈ witnessFamily d m n₀ j x, ∀ a ∈ L, ω ∈ H.birth a)
    (hjoint : ∀ S : Finset (BirthLabel (Torus d m)),
      μ (⋂ a ∈ S, H.birth a) ≤ ENNReal.ofReal (witnessWeight c S)) :
    μ (H.pending j x) ≤ ENNReal.ofReal (witnessMass d m n₀ j c) := by
  classical
  let fam := witnessFamily d m n₀ j x
  have hsubset : H.pending j x ⊆ ⋃ L ∈ fam, (⋂ a ∈ L, H.birth a) := by
    intro ω hω
    obtain ⟨L, hL, hborn⟩ := hcover ω hω
    simp only [Set.mem_iUnion]
    exact ⟨L, hL, by simpa only [Set.mem_iInter] using hborn⟩
  have hsum : μ (⋃ L ∈ fam, (⋂ a ∈ L, H.birth a)) ≤
      ∑ L ∈ fam, ENNReal.ofReal (witnessWeight c L) := by
    calc
      μ (⋃ L ∈ fam, (⋂ a ∈ L, H.birth a)) ≤
          ∑ L ∈ fam, μ (⋂ a ∈ L, H.birth a) := measure_biUnion_finset_le fam _
      _ ≤ ∑ L ∈ fam, ENNReal.ofReal (witnessWeight c L) := by
        apply Finset.sum_le_sum
        intro L hL
        exact hjoint L
  have hweights : ∀ L ∈ fam, 0 ≤ witnessWeight c L := by
    intro L hL
    unfold witnessWeight birthBound
    exact Finset.prod_nonneg (fun a ha => Real.exp_nonneg _)
  have hsum_real :
      (∑ L ∈ fam, ENNReal.ofReal (witnessWeight c L)) =
        ENNReal.ofReal (∑ L ∈ fam, witnessWeight c L) := by
    rw [ENNReal.ofReal_sum_of_nonneg hweights]
  have hroot : (∑ L ∈ fam, witnessWeight c L) ≤ witnessMass d m n₀ j c := by
    unfold witnessMass
    apply le_csSup
    · exact (Set.finite_range (fun y : Torus d m =>
        ∑ L ∈ witnessFamily d m n₀ j y, witnessWeight c L)).bddAbove
    · exact ⟨x, rfl⟩
  calc
    μ (H.pending j x) ≤ μ (⋃ L ∈ fam, (⋂ a ∈ L, H.birth a)) := measure_mono hsubset
    _ ≤ ∑ L ∈ fam, ENNReal.ofReal (witnessWeight c L) := hsum
    _ = ENNReal.ofReal (∑ L ∈ fam, witnessWeight c L) := hsum_real
    _ ≤ ENNReal.ofReal (witnessMass d m n₀ j c) := ENNReal.ofReal_le_ofReal hroot

/-- The section bound follows from deterministic extraction, support control,
finite witness counting, and the scalar history-recursion closure. -/
theorem pending_site_bound_from_helpers (d : ℕ) (hd : 3 ≤ d) (c C : ℝ)
    (hc : 0 < c) (_hC : 1 ≤ C)
    (hExtract : ∃ N : ℕ, ∀ (m n₀ : ℕ) (Ω : Type)
      (H : PendingHistory d m n₀ Ω), N ≤ n₀ → H.C = C →
      ∀ j x ω, n₀ ≤ j → clearingScheduled j m → ω ∈ H.pending j x →
        ∃ L, IsWitness d m n₀ j x L ∧ ∀ a ∈ L, ω ∈ H.birth a)
    (hSupport : ∃ N : ℕ, ∀ m n₀ j x L, N ≤ n₀ → IsWitness d m n₀ j x L →
      (∀ a ∈ L, physicalDistance d m x a.anchor ≤ witnessRadius j) ∧
      (∀ a ∈ L, n₀ < a.scale ∧ a.scale ≤ j))
    (hRecursion : ∃ N : ℕ, ∃ C₀ : ℝ, 1 ≤ C₀ ∧
      ∀ m n₀ j c, N ≤ n₀ → n₀ < j → clearingScheduled j m → 0 < c →
        witnessMass d m n₀ j c ≤ recursionBound d n₀ j c C₀
          (fun r => witnessMass d m n₀ r c)) :
    ∃ N : ℕ, ∀ (m n₀ : ℕ) (Ω : Type) [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (H : PendingHistory d m n₀ Ω), N ≤ n₀ → H.C = C →
      (∀ j x, MeasurableSet (H.pending j x)) → (∀ a, MeasurableSet (H.birth a)) →
      (∀ S : Finset (BirthLabel (Torus d m)),
        μ (⋂ a ∈ S, H.birth a) ≤ ENNReal.ofReal (witnessWeight c S)) →
      ∀ j x, n₀ ≤ j → clearingScheduled j m →
        μ (H.pending j x) ≤ ENNReal.ofReal (birthBound (historyExponent d c) j) := by
  obtain ⟨Nextract, hextract⟩ := hExtract
  obtain ⟨Nsupport, hsupport⟩ := hSupport
  obtain ⟨Nrec, C₀, hC₀, hrec⟩ := hRecursion
  obtain ⟨Nclose, hclose⟩ :=
    close_history_recursion_proof d hd c C₀ hc hC₀
  let N := max Nextract (max Nsupport (max Nrec Nclose))
  refine ⟨N, ?_⟩
  intro m n₀ Ω _ μ _ H hN hHC _ _ hJoint j x hj hscheduled
  have hNextract : Nextract ≤ n₀ := (le_max_left _ _).trans hN
  have hNsupport : Nsupport ≤ n₀ :=
    (le_max_of_le_right (le_max_left _ _)).trans hN
  have hNrec : Nrec ≤ n₀ :=
    (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))).trans hN
  have hNclose : Nclose ≤ n₀ :=
    (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right le_rfl))).trans hN
  let Z : ℕ → ℝ := fun r => witnessMass d m n₀ r c
  have hZ : ∀ r, 0 ≤ Z r := by
    intro r
    exact witnessMass_nonneg d m n₀ r c
  have hinit : Z n₀ = 0 := witnessMass_initial d m n₀ c
  have hZrec : ∀ r, n₀ < r → r ≤ j →
      Z r ≤ recursionBound d n₀ r c C₀ Z := by
    intro r hnr hrj
    have hrscheduled : clearingScheduled r m := by
      exact le_trans hrj (by simpa [clearingScheduled] using hscheduled)
    simpa [Z] using hrec m n₀ r c hNrec hnr hrscheduled hc
  have hmass := hclose n₀ j hNclose Z hZ hinit hZrec j hj le_rfl
  have hcover : ∀ ω ∈ H.pending j x,
      ∃ L ∈ witnessFamily d m n₀ j x, ∀ a ∈ L, ω ∈ H.birth a := by
    intro ω hω
    obtain ⟨L, hW, hborn⟩ :=
      hextract m n₀ Ω H hNextract hHC j x ω hj hscheduled hω
    have hscale := (hsupport m n₀ j x L hNsupport hW).2
    refine ⟨L, witness_mem_family_of_scale hW (fun a ha => (hscale a ha).2), hborn⟩
  have hpending := pending_by_witness_mass μ H x c hcover hJoint
  exact hpending.trans (ENNReal.ofReal_le_ofReal hmass)

end AndersonAC.SolS78
