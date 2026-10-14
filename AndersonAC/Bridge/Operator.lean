import AndersonAC.Blueprint.Target
import AndersonAC.Challenge

noncomputable section

open MeasureTheory OAI.Anderson
open scoped ENNReal lp Topology
open AndersonAC.Blueprint AndersonChallenge

namespace AndersonAC.MuseBridge

variable {d : ℕ}

/-- Pointwise formula for the bounded potential operator. -/
@[simp] theorem boundedPotentialOperator_apply (V : Site d → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hV : ∀ x, |V x| ≤ M) (f : StateSpace d) (x : Site d) :
    boundedPotentialOperator V M hM hV f x = (V x : ℂ) * f x := rfl

/-- Pointwise formula for the direct Simon Hamiltonian. -/
theorem simonHamiltonian_apply (V : Site d → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hV : ∀ x, |V x| ≤ M) (f : StateSpace d) (x : Site d) :
    simonHamiltonian V M hM hV f x =
      (∑ j : Fin d, (f (x + Pi.single j 1) + f (x - Pi.single j 1)))
        + (V x : ℂ) * f x := by
  simp only [simonHamiltonian, hopping, basisVector, add_apply,
    sum_apply, lp.coeFn_add, lp.coeFn_sum,
    Finset.sum_apply, Pi.add_apply, shift_apply,
    boundedPotentialOperator_apply, sub_eq_add_neg, neg_neg]

/-- The challenge's Anderson operator property determines the operator. -/
theorem isAndersonOperator_unique {V : (Fin d → ℤ) → ℝ}
    {T₁ T₂ : lp (fun _ : Fin d → ℤ => ℂ) 2 →L[ℂ] lp (fun _ : Fin d → ℤ => ℂ) 2}
    (h₁ : IsAndersonOperator V T₁) (h₂ : IsAndersonOperator V T₂) :
    T₁ = T₂ := by
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  ext n
  rw [h₁ u n, h₂ u n]

/-- The direct Simon Hamiltonian satisfies the challenge's Anderson operator property. -/
theorem simonHamiltonian_isAndersonOperator (V : Site d → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hV : ∀ x, |V x| ≤ M) :
    IsAndersonOperator V (simonHamiltonian V M hM hV) := by
  intro u n
  exact simonHamiltonian_apply V M hM hV u n

/-- The bounded potential operator is self-adjoint. -/
theorem boundedPotentialOperator_isSelfAdjoint (V : Site d → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hV : ∀ x, |V x| ≤ M) :
    IsSelfAdjoint (boundedPotentialOperator V M hM hV) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro x
  change inner ℂ ((V x : ℂ) • f x) (g x) = inner ℂ (f x) ((V x : ℂ) • g x)
  simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal]

/-- The direct Simon Hamiltonian is self-adjoint. -/
theorem simonHamiltonian_isSelfAdjoint (V : Site d → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hV : ∀ x, |V x| ≤ M) :
    IsSelfAdjoint (simonHamiltonian V M hM hV) := by
  unfold simonHamiltonian
  exact (IsSelfAdjoint.neg (R := StateSpace d →L[ℂ] StateSpace d)
    (hopping_isSelfAdjoint d)).add
    (boundedPotentialOperator_isSelfAdjoint V M hM hV)

/-- Any Anderson operator for a bounded potential equals the direct Hamiltonian. -/
theorem isAndersonOperator_eq_simonHamiltonian (V : Site d → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hV : ∀ x, |V x| ≤ M)
    {T : lp (fun _ : Fin d → ℤ => ℂ) 2 →L[ℂ] lp (fun _ : Fin d → ℤ => ℂ) 2}
    (hT : IsAndersonOperator V T) :
    T = simonHamiltonian V M hM hV :=
  isAndersonOperator_unique hT (simonHamiltonian_isAndersonOperator V M hM hV)

end AndersonAC.MuseBridge
