import AndersonAC.AgentS6Construct.Core

noncomputable section

namespace AndersonAC.AgentS6Construct

open AndersonAC.S6

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem scatteringOfDamping_entry_of_ne (t : ℝ) (p : ι → ℝ)
    (g : Matrix ι ι ℂ) (i j : ι) (hij : i ≠ j) :
    scatteringOfDamping t p g i j =
      (2 * Complex.I * (t : ℂ)) * (Real.sqrt (p i) : ℂ) * g i j *
        (Real.sqrt (p j) : ℂ) := by
  simp [scatteringOfDamping, sqrtDamping, hij, Matrix.mul_apply,
    Matrix.diagonal_apply]
  ring

def trialCrossFromHatG {core : Finset ι} (t : ℝ) (r : ι → ℂ)
    (active : Finset ι) (H : Matrix ι ι ℂ) : Matrix ι {b // b ∈ core} ℂ :=
  fun i b => if hi : i ∈ active then
    if i ∈ core then 0 else
      (2 * Complex.I * (t : ℂ)) * (Real.sqrt ((r i).im) : ℂ) * H i b *
        (Real.sqrt ((r b).im) : ℂ)
    else 0

theorem trialCross_eq_trialCrossFromHatG {core : Finset ι} (t : ℝ)
    (r : ι → ℂ) (s : TrialState core)
    (hmatch : ∀ (i j : {i // i ∈ s.active}),
      trialInverse t r s i j = s.hatG i j) :
    trialCross t r s = trialCrossFromHatG t r s.active s.hatG := by
  classical
  ext i b
  by_cases hi : i ∈ s.active
  · by_cases hc : i ∈ core
    · simp [trialCross, trialCrossFromHatG, hi, hc]
    · let iA : {i // i ∈ s.active} := ⟨i, hi⟩
      let bA : {i // i ∈ s.active} := ⟨b, s.core_active b.property⟩
      have hne : iA ≠ bA := by
        intro h
        apply hc
        have hv : i = b := by simpa [iA, bA] using congrArg Subtype.val h
        exact hv ▸ b.property
      have hentry := scatteringOfDamping_entry_of_ne t
        (imagDamping (fun i : {i // i ∈ s.active} => r i))
        (trialInverse t r s) iA bA hne
      have hmatch' : trialInverse t r s iA bA = s.hatG i b := by
        simpa [iA, bA] using hmatch iA bA
      simpa [trialCross, trialCrossFromHatG, hi, hc, iA, bA, scattering, imagDamping,
        hmatch'] using hentry
  · simp [trialCross, trialCrossFromHatG, hi]

end AndersonAC.AgentS6Construct
