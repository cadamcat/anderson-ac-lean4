import AndersonAC.S78.Definitions

open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78
open AndersonAC.S78

/-- The finite connected spatial form used at the initial assembly state. -/
def SpatialFormInput : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι), G.Connected →
    ∀ (A : Finset ι) (b : ℝ), 0 < b →
      (∀ f : ι → ℝ, 0 ≤ spatialEnergy G A b f) ∧
      (∀ (s : ℝ) (f : ι → ℝ),
        spatialEnergy G A b (fun i => s * f i) = s ^ 2 * spatialEnergy G A b f) ∧
      constantKernel A (spatialEnergy G A b) ∧
      (∀ y : ι → ℝ, neutral A y →
        BddAbove (Set.range fun f : ι → ℝ =>
          2 * (∑ i ∈ A, y i * f i) - spatialEnergy G A b f))

/-- A real form padded from its active coordinates. -/
def realForm {ι : Type} (A : Finset ι) (Q : Matrix A A ℝ) (f : ι → ℝ) : ℝ :=
  ∑ i : A, ∑ j : A, f i.val * Q i j * f j.val

def FiniteRealForm {ι : Type} (A : Finset ι) (D : (ι → ℝ) → ℝ) : Prop :=
  ∃ Q : Matrix A A ℝ, Q.transpose = Q ∧ ∀ f, D f = realForm A Q f

/-- Finite quadratic minimization supplies the kernel and finiteness facts
needed by the assembly prefix and inverse comparison, including empty initial
active sets and every nonempty retained set. -/
def FiniteFormInput : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Finset ι)
    (D : (ι → ℝ) → ℝ), FiniteRealForm A D → (∀ f, 0 ≤ D f) → constantKernel A D →
      (∀ y : ι → ℝ, neutral A y →
        BddAbove (Set.range fun f : ι → ℝ => 2 * (∑ i ∈ A, y i * f i) - D f)) ∧
      (∀ B : Finset ι, B ⊆ A → B.Nonempty →
        constantKernel B (schurEnergy B D) ∧ FiniteRealForm B (schurEnergy B D) ∧
          ∀ f : ι → ℝ, ∃ F : ι → ℝ, (∀ i ∈ B, F i = f i) ∧
            D F = schurEnergy B D f)

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.SpatialFormInput
#print axioms AndersonAC.SolS78.FiniteFormInput
