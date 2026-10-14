import AndersonAC.S78.Definitions

open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78
open AndersonAC.S78

/-- The three matrix outputs of the committed assembly, independent of the
relative form comparison. This is a contract to prove, not an axiom. -/
def AssemblyMatrixBounds : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ (C c P : ℝ), 1 ≤ C → 0 < c → 0 ≤ P →
    ∃ C' t₀ : ℝ, 0 < C' ∧ 0 < t₀ ∧
      ∀ (m k : ℕ) (t b : ℝ) (r : Torus d m → ℂ) (I : AssemblyInput d m k t b r),
      I.C = C → I.c = c → I.P = P → t < t₀ → ∀ a : Fin (k + 1),
      matrixNorm (squareKernel (normalizedInverse (I.state a) t)) ≤
        matrixNorm (squareKernel (normalizedInverse (I.state 0) t)) + t ^ (0.10 * delta) ∧
      (∀ i ∈ (I.state a).active,
        ‖(I.state a).g i i - r i‖ ≤ C' * t ^ (0.42 * delta - (d : ℝ) * nu d)) ∧
      (∀ i, (rowFour (normalizedInverse (I.state a) t) i) ^ (1 / 4 : ℝ) ≤
        (0.7 ^ (1 / 4 : ℝ) + C' * t ^ (0.0225 * delta - (d : ℝ) * nu d)) *
          t ^ ((1 + delta) / 4) ∧
        rowFour (normalizedInverse (I.state a) t) i < 0.8 * t ^ (1 + delta))

/-- The local extension used to bound the old near-edge energy by the one
fixed spatial split of the initial potential. -/
def LocalCutoffInput : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ (m : ℕ) (z : Torus d m) (R b : ℝ) (A : Finset (Torus d m))
      (α v : Torus d m → ℝ), 1 ≤ R →
      4 * R < (OAI.Anderson.sideLength m : ℝ) → 0 < b →
      ∃ F : Torus d m → ℝ,
        (∀ i ∈ cube d m z R ∩ A, ∀ j ∈ cube d m z R ∩ A,
          F i - F j = (α i + v i) - (α j + v j)) ∧
        spatialEnergy (nnGraph d m) A b F ≤
          C * ((∑ i ∈ cube d m z (2 * R) ∩ A, (α i) ^ 2) +
            b⁻¹ * cubeGradient d m (cube d m z (2 * R)) v)

/-- The uniform anchor envelope for the far part of an actual survivor
difference. All constants precede volume and the number of operations. -/
def AssemblyAnchorTailInput : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ (C c P : ℝ), 1 ≤ C → 0 < c → 0 ≤ P →
    ∃ P' t₀ : ℝ, 0 ≤ P' ∧ 0 < t₀ ∧
      ∀ (m k : ℕ) (t b : ℝ) (r : Torus d m → ℂ) (I : AssemblyInput d m k t b r),
      I.C = C → I.c = c → I.P = P → t < t₀ →
      ∀ (a : Fin k) (i j : Torus d m),
      i ∉ cube d m (I.anchor a) (100 * I.Ds) ∨
        j ∉ cube d m (I.anchor a) (100 * I.Ds) →
      ‖survivorDifference (I.state a.castSucc) (I.state a.succ) t i j‖ ≤
        t ^ (-P') * Real.exp (-(c / 4) * t * I.Ds) *
          Real.exp (-(c / 4) * t * (physicalDistance d m i (I.anchor a) +
            physicalDistance d m j (I.anchor a)))

/-- Analytic error summation for the assembly. Matrix estimates and finite Schur
algebra are separate inputs. -/
def AssemblyEnergyBounds : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ (C c P : ℝ), 1 ≤ C → 0 < c → 0 ≤ P →
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ (m k : ℕ) (t b : ℝ) (r : Torus d m → ℂ) (I : AssemblyInput d m k t b r),
      I.C = C → I.c = c → I.P = P → t < t₀ →
      ∀ (a : Fin (k + 1)) (f : Torus d m → ℝ),
      |∑ q : Fin k with q.val < a.val, operationEnergyError I q f| ≤
        t ^ (0.10 * delta) * endpointEnergy (I.state 0) r t f

def localCubeMean (d m : ℕ) (z : Torus d m) (R : ℝ) (v : Torus d m → ℝ) : ℝ :=
  (∑ i ∈ cube d m z (2 * R), v i) / ((cube d m z (2 * R)).card : ℝ)

/-- The two weighted-cube consequences needed for the old Schur bridge:
weighted mean deviations near the removed set and a point-to-mean bound for
the far trial. The coordinate transport is shared with weighted_local_energy. -/
def LocalDeviationInput : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ (m : ℕ) (z : Torus d m) (R Lmax Ltotal : ℝ) (l v : Torus d m → ℝ),
    1 ≤ R → 4 * R < (OAI.Anderson.sideLength m : ℝ) → 0 ≤ Lmax → 0 ≤ Ltotal →
    (∀ i, 0 ≤ l i ∧ l i ≤ Lmax) → (∀ i, i ∉ cube d m z R → l i = 0) →
    (∑ i, l i) ≤ Ltotal →
      (∑ i, l i * (v i - localCubeMean d m z R v) ^ 2) ≤
        C * Lmax ^ (1 / 3 : ℝ) * Ltotal ^ (2 / 3 : ℝ) *
          cubeGradient d m (cube d m z (2 * R)) v ∧
      (v z - localCubeMean d m z R v) ^ 2 ≤
        C * R ^ 2 * cubeGradient d m (cube d m z (2 * R)) v

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.AssemblyMatrixBounds
#print axioms AndersonAC.SolS78.LocalCutoffInput
#print axioms AndersonAC.SolS78.AssemblyAnchorTailInput
#print axioms AndersonAC.SolS78.AssemblyEnergyBounds
#print axioms AndersonAC.SolS78.LocalDeviationInput
