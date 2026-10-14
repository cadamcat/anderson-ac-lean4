import Mathlib
import OAI.MathematicalPhysics.Anderson.Certificates
import AndersonAC.Blueprint.FiniteInputs

/-! Concrete definitions for §3 initialization. This module has no proof placeholders. -/

noncomputable section

open scoped BigOperators NNReal ENNReal
open MeasureTheory
open AndersonAC.Blueprint
attribute [local instance] Classical.propDecidable

namespace AndersonAC.S3

abbrev Torus (d L : ℕ) := Fin d → ZMod L
abbrev Frequency (d : ℕ) := Fin d → ℝ
abbrev Cube (d l : ℕ) := Fin d → Fin l

variable {d L : ℕ} [NeZero L]

def normSq {A : Type*} [Fintype A] (v : A → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2
def normOne {A : Type*} [Fintype A] (v : A → ℂ) : ℝ := ∑ i, ‖v i‖
def neutral {A : Type*} [Fintype A] (v : A → ℂ) : Prop := ∑ i, v i = 0
def pairing {A : Type*} [Fintype A] (y f : A → ℂ) : ℝ :=
  (∑ i, star (y i) * f i).re
def form {A : Type*} [Fintype A] (M : Matrix A A ℂ) (v : A → ℂ) : ℝ :=
  pairing v (M.mulVec v)
def meanProjection (A : Type*) [Fintype A] : Matrix A A ℂ :=
  fun _ _ => (Fintype.card A : ℂ)⁻¹
def inverseOnConstants {A : Type*} [Fintype A] [DecidableEq A]
    (D : Matrix A A ℂ) : Matrix A A ℂ :=
  (D + meanProjection A)⁻¹ - meanProjection A
def connectedLaplacian {A : Type*} [Fintype A] (D : Matrix A A ℂ) : Prop :=
  D.conjTranspose = D ∧ ∀ f : A → ℂ,
    0 ≤ form D f ∧ (form D f = 0 ↔ ∃ c : ℂ, f = fun _ => c)
def basisStep (j : Fin d) : Torus d L := Pi.single j 1
def gradientEnergy (v : Torus d L → ℂ) : ℝ :=
  ∑ x, ∑ j : Fin d, ‖v (x + basisStep j) - v x‖ ^ 2
def freeHopping : Matrix (Torus d L) (Torus d L) ℂ := fun x y =>
  -(∑ j : Fin d, ((if y = x + basisStep j then 1 else 0) +
    (if y = x - basisStep j then 1 else 0)))
def laplacian : Matrix (Torus d L) (Torus d L) ℂ :=
  (2 * (d : ℂ)) • 1 + freeHopping
def laplacianPlus : Matrix (Torus d L) (Torus d L) ℂ :=
  inverseOnConstants laplacian
def siteSum {A : Type*} [Fintype A] (π : A → Torus d L) (y : A → ℂ) :
    Torus d L → ℂ := fun i => ∑ x with π x = i, y x
def atMostTwo {A : Type*} [Fintype A] (π : A → Torus d L) : Prop :=
  ∀ i, (Finset.univ.filter (fun x => π x = i)).card ≤ 2
def comparisonCost {A : Type*} [Fintype A] (π : A → Torus d L)
    (b : ℝ) (f : A → ℂ) (v : Torus d L → ℂ) : ℝ :=
  normSq (fun x => f x - v (π x)) + b⁻¹ * gradientEnergy v
def comparisonW {A : Type*} [Fintype A] (π : A → Torus d L)
    (b : ℝ) (f : A → ℂ) : ℝ := sInf (Set.range (comparisonCost π b f))
def comparisonWStar {A : Type*} [Fintype A] (π : A → Torus d L)
    (b : ℝ) (y : A → ℂ) : ℝ := normSq y + b * form laplacianPlus (siteSum π y)
def convexDual {A : Type*} [Fintype A] (W : (A → ℂ) → ℝ) (y : A → ℂ) : ℝ :=
  sSup {r : ℝ | ∃ f : A → ℂ, r = 2 * pairing y f - W f}



def gridAngle (k : Torus d L) : Frequency d := fun j =>
  2 * Real.pi * (if 2 * (k j).val < L then ((k j).val : ℝ)
    else ((k j).val : ℝ) - (L : ℝ)) / (L : ℝ)
def radius (k : Frequency d) : ℝ := Real.sqrt (∑ j, k j ^ 2)
def laplacianSymbol (k : Frequency d) : ℝ := 4 * ∑ j, Real.sin (k j / 2) ^ 2
def dispersion (k : Frequency d) : ℝ := -2 * ∑ j, Real.cos (k j)
def character (k x : Torus d L) : ℂ :=
  Complex.exp (Complex.I * (∑ j, gridAngle k j * ((x j).val : ℝ)))
def fourier (v : Torus d L → ℂ) (k : Torus d L) : ℂ :=
  ∑ x, v x * star (character k x)
def gridAvg (v : Torus d L → ℂ) : ℂ := (Fintype.card (Torus d L) : ℂ)⁻¹ * ∑ k, v k
def gridAvgReal (v : Torus d L → ℝ) : ℝ := (Fintype.card (Torus d L) : ℝ)⁻¹ * ∑ k, v k







def cubeMean {l : ℕ} (v : Cube d l → ℂ) : ℂ :=
  (Fintype.card (Cube d l) : ℂ)⁻¹ * ∑ i, v i
def cubeAdjacent {l : ℕ} (x y : Cube d l) : Prop :=
  ∃ j : Fin d, (∀ i, i ≠ j → x i = y i) ∧ |((x j).val : ℤ) - (y j).val| = 1
def cubeEnergy {l : ℕ} (v : Cube d l → ℂ) : ℝ :=
  (1 / 2) * ∑ x, ∑ y, if cubeAdjacent x y then ‖v x - v y‖ ^ 2 else 0
def foldCoordinate (l : ℕ) (j : ZMod (2 * l)) : ℕ :=
  if j.val < l then j.val else 2 * l - 1 - j.val
def reflected {l : ℕ} [NeZero (2 * l)] (hl : 0 < l) (v : Cube d l → ℂ) (x : Torus d (2 * l)) : ℂ :=
  v (fun j => ⟨foldCoordinate l (x j), by
    have hx := (x j).val_lt
    unfold foldCoordinate
    split_ifs <;> omega⟩) - cubeMean v




def torusDistance (x y : Torus d L) : ℕ :=
  ∑ j, min ((x j - y j).val) (L - (x j - y j).val)
def ballCard (x : Torus d L) (R : ℝ) : ℕ :=
  (Finset.univ.filter (fun y => (torusDistance x y : ℝ) ≤ R)).card
def exponentialMoment (x : Torus d L) (u : ℝ) (a : ℕ) : ℝ :=
  ∑ y, (torusDistance x y : ℝ) ^ a * Real.exp (-u * (torusDistance x y : ℝ))



def offset (d : ℕ) (e₂ : ℝ) : ℝ := if d = 3 then e₂ else 1 / 100
def energyWindow (d : ℕ) (e₂ : ℝ) : Set ℝ :=
  OAI.Anderson.energyWindow d e₂
def expandedWindow (d : ℕ) (e₂ : ℝ) : Set ℝ :=
  Set.Icc (-2 * (d : ℝ) + 2 * offset d e₂ / 5) (-2 * (d : ℝ) + 5 * offset d e₂ / 4)
def frequencyMeasure (d : ℕ) : Measure (Frequency d) :=
  ENNReal.ofReal ((2 * Real.pi) ^ d)⁻¹ •
    volume.restrict (Set.pi Set.univ (fun _ : Fin d => Set.Ico (-Real.pi) Real.pi))
def continuumResolvent (z : ℂ) (k : Frequency d) : ℂ := ((dispersion k : ℂ) - z)⁻¹
def freeStieltjes (d : ℕ) (z : ℂ) : ℂ := ∫ k : Frequency d, continuumResolvent z k ∂frequencyMeasure d
def perturbedDispersion (c φ k : Frequency d) : ℝ := -2 * ∑ j, c j * Real.cos (k j + φ j)
def sphereIntegral (d : ℕ) (f : Frequency d → ℝ) : ℝ :=
  (d : ℝ) * ∫ x : Frequency d in {x | radius x < 1}, f (fun j => x j / radius x)
def bottomDensity (d : ℕ) (s : ℝ) : ℝ :=
  Real.rpow s ((d : ℝ) / 2 - 1) / (2 * (2 * Real.pi) ^ d) *
    sphereIntegral d (fun ω => ∏ j, (Real.sqrt (1 - s * ω j ^ 2 / 4))⁻¹)





def initialIndex (coupling : ℝ) : ℕ := ⌊Real.log (3 / coupling ^ 2) / Real.log 4⌋₊
def scaleS (coupling : ℝ) (n : ℕ) : ℝ := coupling ^ 2 / 3 * (4 : ℝ) ^ (initialIndex coupling : ℤ) / (4 : ℝ) ^ n
def scaleT (coupling : ℝ) (m n : ℕ) : ℝ := scaleS coupling n + scaleS coupling m
def sideLength (m : ℕ) : ℕ := OAI.Anderson.sideLength m
instance sideLength_neZero (m : ℕ) : NeZero (sideLength m) := OAI.Anderson.sideLength_neZero m
def startupT (n₀ m : ℕ) (u : ℝ) : ℝ :=
  OAI.Anderson.scaleHeight n₀ u + OAI.Anderson.scaleHeight m u
def delta : ℝ := 1 / 100
def kappa : ℝ := (1 / 200) * delta
def rectangle (a₀ B : ℝ) : Set ℂ := {r | |r.re| ≤ B ∧ a₀ ≤ r.im ∧ r.im ≤ B}
def gridResolvent (E t : ℝ) (r : ℂ) (k : Torus d L) : ℂ :=
  ((dispersion (gridAngle k) : ℂ) - E - t * r)⁻¹
def scalarMap (E t : ℝ) (r : ℂ) : ℂ := gridAvg (gridResolvent E t r : Torus d L → ℂ)
def initialMatrix (E t : ℝ) (r : ℂ) : Matrix (Torus d L) (Torus d L) ℂ :=
  freeHopping - ((E : ℂ) + t * r) • 1
def initialG (E t : ℝ) (r : ℂ) : Matrix (Torus d L) (Torus d L) ℂ :=
  (initialMatrix E t r)⁻¹
def initialH (E t : ℝ) (r : ℂ) : Matrix (Torus d L) (Torus d L) ℂ :=
  (Real.sqrt t : ℂ) • initialG E t r
def initialK (E t : ℝ) (r : ℂ) : Matrix (Torus d L) (Torus d L) ℂ :=
  entrywiseSquare (initialH E t r)
def initialF (E t : ℝ) (r : ℂ) : Matrix (Torus d L) (Torus d L) ℂ :=
  fun i j => (‖initialH E t r i j‖ ^ 2 : ℝ)
def initialD (E t : ℝ) (r : ℂ) : Matrix (Torus d L) (Torus d L) ℂ :=
  (r.im ^ 2 : ℂ) • (1 - initialF E t r)
def initialX (E t : ℝ) (r : ℂ) : Matrix (Torus d L) (Torus d L) ℂ :=
  inverseOnConstants (initialD E t r)
def fSymbol (E t : ℝ) (r : ℂ) (ζ : Torus d L) : ℂ :=
  t * gridAvg (fun k => gridResolvent E t r k * star (gridResolvent E t r (k + ζ)))
def kSymbol (E t : ℝ) (r : ℂ) (ζ : Torus d L) : ℂ :=
  t * gridAvg (fun k => gridResolvent E t r k * gridResolvent E t r (k + ζ))
def fourthRow (E t : ℝ) (r : ℂ) (i : Torus d L) : ℝ :=
  ∑ j, ‖initialH E t r i j‖ ^ 4








def directionalPatch (α t c₀ θ : ℝ) (e : Frequency d) : Set (Frequency d) :=
  {k | |∑ j, (2 * Real.sin (k j / 2)) ^ 2 - α| ≤ c₀ * t ∧
    (∑ j, (2 * Real.sin (k j / 2)) * e j) ≥
      Real.cos θ * radius (fun j => 2 * Real.sin (k j / 2)) ∧
    ∀ j, |k j| < 1 / 4}



def slicedDispersion (sign : ℝ) (ζ x : Frequency d) : ℝ :=
  -2 * (∑ j, Real.cos (ζ j / 2) * Real.sqrt (1 - x j ^ 2)) +
    sign * 2 * ∑ j, Real.sin (ζ j / 2) * x j













/- Exact local mirror of Blueprint.InitializationInput (FiniteInputs.lean).
The mirror stays inside S3 because that other branch is not yet an importable
dependency of this worktree. Integration can replace this alias by its source.
-/
end AndersonAC.S3
