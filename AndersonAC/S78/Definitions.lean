import Mathlib
import AndersonAC.Blueprint.Certificate

/-! Concrete §7–8 data and forms. This file contains no proof placeholders. -/
open scoped BigOperators ENNReal Topology
open MeasureTheory Filter
set_option autoImplicit false
noncomputable section
namespace AndersonAC.S78

abbrev Torus := OAI.Anderson.Torus

def delta : ℝ := 1 / 100
def nu (d : ℕ) : ℝ := delta / (100000 * (d : ℝ))
def heatExponent : ℝ := 0.46 * delta
def clearingScheduled (j m : ℕ) : Prop := j ≤ m / 2
def stageScale (u : ℝ) (j m : ℕ) : ℝ := u / (4 : ℝ) ^ j + u / (4 : ℝ) ^ m
def separationRadius (j : ℕ) : ℝ := (4 : ℝ) ^ (8 * j)
def inspectionRadius (j : ℕ) : ℝ := (4 : ℝ) ^ (4 * j)
def heatLimit (t : ℝ) : ℕ := ⌊t ^ (-1 - heatExponent)⌋₊

def nnGraph (d m : ℕ) : SimpleGraph (Torus d m) :=
  SimpleGraph.fromRel fun x y => ∃ i : Fin d,
    y = x + OAI.Anderson.torusBasisVector i ∨ y = x - OAI.Anderson.torusBasisVector i

def physicalDistance (d m : ℕ) (x y : Torus d m) : ℝ := ((nnGraph d m).dist x y : ℝ)

def pathCost {ι : Type} (T : Finset ι) (xs : List ι) : ℕ := by
  classical
  exact ((xs.zip xs.tail).map fun e => if e.1 ∈ T ∨ e.2 ∈ T then 0 else 1).sum

def terminalDistance {ι : Type} (G : SimpleGraph ι) (T : Finset ι) (u v : ι) : ℝ :=
  ((sInf {n : ℕ | ∃ xs : List ι, xs.IsChain G.Adj ∧ xs.head? = some u ∧
    xs.getLast? = some v ∧ pathCost T xs = n} : ℕ) : ℝ)

def cube (d m : ℕ) (z : Torus d m) (radius : ℝ) : Finset (Torus d m) := by
  classical
  exact Finset.univ.filter fun x => ∀ i : Fin d,
    ((min ((x i - z i).val) (OAI.Anderson.sideLength m - (x i - z i).val) : ℕ) : ℝ) ≤ radius

def distanceTo {ι : Type} (dist : ι → ι → ℝ) (O : Finset ι) (x : ι) : ℝ :=
  sInf {dist x y | y ∈ O}

def overlap {ι κ : Type} [Fintype κ] (Q : κ → Finset ι) (x : ι) : ℕ := by
  classical
  exact (Finset.univ.filter fun a => x ∈ Q a).card

def matrixNorm {ι : Type} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ) : ℝ :=
  ‖B.toEuclideanLin.toContinuousLinearMap‖
def rowTwo {ι : Type} [Fintype ι] (h : Matrix ι ι ℂ) (i : ι) : ℝ := ∑ j, ‖h i j‖ ^ 2
def rowFour {ι : Type} [Fintype ι] (h : Matrix ι ι ℂ) (i : ι) : ℝ := ∑ j, ‖h i j‖ ^ 4
def frobeniusSq {ι : Type} [Fintype ι] (h : Matrix ι ι ℂ) : ℝ := ∑ i, rowTwo h i
def squareKernel {ι : Type} (h : Matrix ι ι ℂ) : Matrix ι ι ℂ := fun i j => (h i j) ^ 2

def wardEnergy {ι : Type} (A : Finset ι) (p : ι → ℝ) (h : Matrix ι ι ℂ)
    (f : ι → ℝ) : ℝ :=
  (1 / 2) * ∑ i ∈ A, ∑ j ∈ A, p i * p j * ‖h i j‖ ^ 2 * (f i - f j) ^ 2

def gradientEnergy {ι : Type} [Fintype ι] (G : SimpleGraph ι) (f : ι → ℝ) : ℝ := by
  classical
  exact (1 / 2) * ∑ i, ∑ j, if G.Adj i j then (f i - f j) ^ 2 else 0

def spatialEnergy {ι : Type} [Fintype ι] (G : SimpleGraph ι) (A : Finset ι)
    (b : ℝ) (f : ι → ℝ) : ℝ :=
  sInf {e : ℝ | ∃ α v : ι → ℝ, (∀ i ∈ A, f i = α i + v i) ∧
    e = (∑ i ∈ A, (α i) ^ 2) + b⁻¹ * gradientEnergy G v}

def schurEnergy {ι : Type} (A : Finset ι) (D : (ι → ℝ) → ℝ) (f : ι → ℝ) : ℝ :=
  sInf (D '' {F : ι → ℝ | ∀ i ∈ A, F i = f i})

def inverseEnergy {ι : Type} (A : Finset ι) (D : (ι → ℝ) → ℝ) (y : ι → ℝ) : ℝ :=
  sSup (Set.range fun f : ι → ℝ => 2 * (∑ i ∈ A, y i * f i) - D f)

def neutral {ι : Type} [Fintype ι] (A : Finset ι) (y : ι → ℝ) : Prop :=
  (∀ i ∉ A, y i = 0) ∧ ∑ i ∈ A, y i = 0

def constantKernel {ι : Type} (A : Finset ι) (D : (ι → ℝ) → ℝ) : Prop :=
  ∀ f, D f = 0 ↔ ∃ c : ℝ, ∀ i ∈ A, f i = c

structure Endpoint (ι : Type) where
  active : Finset ι
  M : Matrix ι ι ℂ
  g : Matrix ι ι ℂ

def normalizedInverse {ι : Type} (s : Endpoint ι) (t : ℝ) : Matrix ι ι ℂ :=
  (Real.sqrt t : ℂ) • s.g

def endpointEnergy {ι : Type} (s : Endpoint ι) (r : ι → ℂ) (t : ℝ) : (ι → ℝ) → ℝ :=
  wardEnergy s.active (fun i => (r i).im) (normalizedInverse s t)
/-- §2 real terminal-Schur data. Invertibility here is an explicit input. -/

def IsDampedEndpoint {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Endpoint ι) (r : ι → ℂ) (t : ℝ) : Prop :=
  (∀ i j, s.M i j = s.M j i ∧ (s.M i j).im = 0) ∧
  (∀ i j, i ∉ s.active ∨ j ∉ s.active → s.g i j = 0) ∧
  let B := s.M.submatrix (fun i : s.active => i.val) (fun i : s.active => i.val) -
    (t : ℂ) • Matrix.diagonal (fun i : s.active => r i.val)
  let G := s.g.submatrix (fun i : s.active => i.val) (fun i : s.active => i.val)
  B * G = 1 ∧ G * B = 1

def survivorDifference {ι : Type} [DecidableEq ι] (s₀ s₁ : Endpoint ι)
    (t : ℝ) : Matrix ι ι ℂ := fun i j => if i ∈ s₁.active ∧ j ∈ s₁.active then
  normalizedInverse s₁ t i j - normalizedInverse s₀ t i j else 0

structure AssemblyInput (d m k : ℕ) (t b : ℝ) (r : Torus d m → ℂ) where
  state : Fin (k + 1) → Endpoint (Torus d m)
  anchor : Fin k → Torus d m
  C : ℝ
  c : ℝ
  P : ℝ
  Ds : ℝ
  positive : 0 < t ∧ t ≤ 1 ∧ 0 < b ∧ b ≤ t ∧ 0 < c ∧ 1 ≤ C ∧ 0 ≤ P
  scaleRadius : t ^ (-8 - nu d) ≤ Ds ∧ Ds ≤ C * t ^ (-8 - nu d)
  embedded : 400 * Ds < (OAI.Anderson.sideLength m : ℝ)
  damping : ∀ i, c ≤ (r i).im ∧ (r i).im ≤ C ∧ ‖r i‖ ≤ C
  physical : ∀ a, IsDampedEndpoint (state a) r t
  nested : ∀ a : Fin k, (state a.succ).active ⊆ (state a.castSucc).active
  activeCount : ∀ a, Fintype.card (Torus d m) ≤ 2 * (state a).active.card
  distinct : Function.Injective anchor
  removedNonempty : ∀ a : Fin k, ((state a.castSucc).active \ (state a.succ).active).Nonempty
  removedSize : ∀ a : Fin k,
    (((state a.castSucc).active \ (state a.succ).active).card : ℝ) ≤ C * (heatLimit t : ℝ)
  removedLocal : ∀ a : Fin k, ∀ i ∈ (state a.castSucc).active \ (state a.succ).active,
    physicalDistance d m i (anchor a) ≤ Ds
  haloOverlap : ∀ x, (overlap (fun a => cube d m (anchor a) (200 * Ds)) x : ℝ) ≤
    C * t ^ (-(d : ℝ) * nu d)
  metric : ∀ a u v, physicalDistance d m u v / 2 - t ^ (-1.03 : ℝ) ≤
    terminalDistance (nnGraph d m) (Finset.univ \ (state a).active) u v
  /-- §5 Combes–Thomas bound on indexed real terminal-Schur states. -/
  resolventDecay : ∀ a i j, ‖normalizedInverse (state a) t i j‖ ≤
    C / Real.sqrt t * Real.exp (-c * t * max (physicalDistance d m i j / 2 - t ^ (-1.03 : ℝ)) 0)
  initialComparison : ∀ f,
    c * spatialEnergy (nnGraph d m) (state 0).active b f ≤ endpointEnergy (state 0) r t f ∧
    endpointEnergy (state 0) r t f ≤ C * spatialEnergy (nnGraph d m) (state 0).active b f
  initialRows : ∀ i, rowFour (normalizedInverse (state 0) t) i ≤ 0.7 * t ^ (1 + delta)
  initialLag : ∀ i ∈ (state 0).active, ‖(state 0).g i i - r i‖ ≤ C * t ^ (0.42 * delta)
  entryChange : ∀ a : Fin k, ∀ i j,
    ‖survivorDifference (state a.castSucc) (state a.succ) t i j‖ ≤ C * Real.sqrt t * t ^ (0.42 * delta)
  rowChange : ∀ a : Fin k, ∀ i,
    rowTwo (survivorDifference (state a.castSucc) (state a.succ) t) i ≤ C * t ^ (0.25 * delta)
  totalChange : ∀ a : Fin k,
    frobeniusSq (survivorDifference (state a.castSucc) (state a.succ) t) ≤ C * t ^ (-1 - 0.47 * delta)
  decay : ∀ a : Fin k, ∀ i j,
    let O := (state a.castSucc).active \ (state a.succ).active
    ‖survivorDifference (state a.castSucc) (state a.succ) t i j‖ ≤ t ^ (-P) * Real.exp (-c * t *
      (max (distanceTo (physicalDistance d m) O i - C * t ^ (-1.03 : ℝ)) 0 +
       max (distanceTo (physicalDistance d m) O j - C * t ^ (-1.03 : ℝ)) 0))

def operationEnergyError {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin k) (f : Torus d m → ℝ) : ℝ :=
  endpointEnergy (I.state a.succ) r t f -
    schurEnergy (I.state a.succ).active (endpointEnergy (I.state a.castSucc) r t) f

def resetInverse {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (r : ι → ℂ) (t : ℝ) : Matrix ι ι ℂ := (M - (t : ℂ) • Matrix.diagonal r)⁻¹

def resetLag {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (r : ι → ℂ) (t : ℝ) : ι → ℂ := fun i => resetInverse M r t i i - r i

def ResetOutput {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (r ζ : ι → ℂ) (t C : ℝ) : Prop :=
  let g := resetInverse M r t
  let g' := resetInverse M (r + ζ) t
  let h := (Real.sqrt t : ℂ) • g
  let h' := (Real.sqrt t : ℂ) • g'
  (∀ i, g' i i = (r + ζ) i) ∧
  (∀ i, Real.sqrt (rowTwo (h' - h) i) ≤ C * ‖ζ‖) ∧
  (∀ i j, ‖(h' - h) i j‖ ≤ C * Real.sqrt t * ‖ζ‖) ∧
  (∀ i, (rowFour (h' - h) i) ^ (1 / 4 : ℝ) ≤ C * t ^ (1 / 4 : ℝ) * ‖ζ‖) ∧
  matrixNorm (squareKernel h' - squareKernel h) ≤ C * ‖ζ‖ ∧
  (∀ f, (1 - C * ‖ζ‖) * wardEnergy Finset.univ (fun i => (r i).im) h f ≤
    wardEnergy Finset.univ (fun i => ((r + ζ) i).im) h' f ∧
    wardEnergy Finset.univ (fun i => ((r + ζ) i).im) h' f ≤
      (1 + C * ‖ζ‖) * wardEnergy Finset.univ (fun i => (r i).im) h f)

inductive BirthType | tile | clearing deriving DecidableEq
instance : Fintype BirthType where
  elems := {.tile, .clearing}
  complete x := by cases x <;> simp
structure BirthLabel (ι : Type) where
  scale : ℕ
  kind : BirthType
  anchor : ι
  deriving DecidableEq

def birthBound (c : ℝ) (j : ℕ) : ℝ := Real.exp (-(4 : ℝ) ^ (c * (j : ℝ)))
def historyAlpha (d : ℕ) : ℝ := nu d / (100 * (d : ℝ))
def historyBeta (d : ℕ) : ℝ := 0.2 * nu d
def historyEarlier (d j : ℕ) : ℕ := ⌊historyAlpha d * (j : ℝ)⌋₊
def historyChildren (d j : ℕ) : ℕ := ⌊(4 : ℝ) ^ (historyBeta d * (j : ℝ))⌋₊
def witnessRadius (j : ℕ) : ℝ := (4 : ℝ) ^ (10 * j)
def historyExponent (d : ℕ) (c : ℝ) : ℝ := min (c * historyAlpha d / 4) (nu d / 20)

structure BirthProcess (Ω : Type) [MeasurableSpace Ω] where
  history : Filtration ℕ ‹MeasurableSpace Ω›
  event : ℕ → Set Ω
  scale : ℕ → ℕ
  adapted : ∀ n, MeasurableSet[history (n + 1)] (event n)

/-- Witnesses represented by their finite leaf sets; distinct tree encodings
with the same leaf events are identified. Tree counting upper-bounds this family. -/

inductive IsWitness (d m n₀ : ℕ) : ℕ → Torus d m → Finset (BirthLabel (Torus d m)) → Prop
  | leaf (j : ℕ) (x : Torus d m) (a : BirthLabel (Torus d m))
      (hj : n₀ < j) (hs : n₀ < a.scale ∧ a.scale ≤ j ∧ historyEarlier d j < a.scale)
      (hnear : physicalDistance d m x a.anchor ≤ witnessRadius j / 2) : IsWitness d m n₀ j x {a}
  | branch (j : ℕ) (x : Torus d m) (hj : n₀ < j)
      (hr : n₀ ≤ historyEarlier d j) (hdec : historyEarlier d j < j)
      (centers : Fin (historyChildren d j) → Torus d m)
      (leaves : Fin (historyChildren d j) → Finset (BirthLabel (Torus d m)))
      (hnear : ∀ i, physicalDistance d m x (centers i) ≤ witnessRadius j / 2)
      (hsep : ∀ i l, i ≠ l → 3 * witnessRadius (historyEarlier d j) <
        physicalDistance d m (centers i) (centers l))
      (children : ∀ i, IsWitness d m n₀ (historyEarlier d j) (centers i) (leaves i)) :
      IsWitness d m n₀ j x (Finset.univ.biUnion leaves)

def witnessWeight {ι : Type} (c : ℝ) (L : Finset (BirthLabel ι)) : ℝ := ∏ a ∈ L, birthBound c a.scale

structure PendingHistory (d m n₀ : ℕ) (Ω : Type) where
  pending : ℕ → Torus d m → Set Ω
  birth : BirthLabel (Torus d m) → Set Ω
  latest : ℕ → Torus d m → Ω → BirthLabel (Torus d m)
  C : ℝ
  initial : ∀ x, pending n₀ x = ∅
  latestOccurred : ∀ j x ω, ω ∈ pending j x →
    n₀ < (latest j x ω).scale ∧ (latest j x ω).scale ≤ j ∧ ω ∈ birth (latest j x ω)
  latestNearby : ∀ j x ω, ω ∈ pending j x →
    physicalDistance d m x (latest j x ω).anchor ≤ C * (4 : ℝ) ^ ((8 + nu d) * ((latest j x ω).scale : ℝ))
  persistence : ∀ j r x ω, n₀ ≤ r → r < j → ω ∈ pending j x →
    (latest j x ω).scale ≤ r → ω ∈ pending r x
  dichotomy : ∀ j x ω, n₀ < j → clearingScheduled j m → ω ∈ pending j x →
    ((latest j x ω).scale = j) ∨ ∃ S : Finset (Torus d m), x ∈ S ∧
      stageScale 1 j m ^ (-nu d) < (S.card : ℝ) ∧ (∀ y ∈ S, ω ∈ pending j y) ∧
      (∀ y ∈ S, physicalDistance d m x y ≤ C * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)))

def recursionBound (d n₀ j : ℕ) (c C : ℝ) (Z : ℕ → ℝ) : ℝ :=
  C * (j : ℝ) * witnessRadius j ^ d * birthBound c (max n₀ (historyEarlier d j)) +
  if n₀ ≤ historyEarlier d j then
    (C * witnessRadius j ^ d * Z (historyEarlier d j)) ^ historyChildren d j else 0

def abortBound (d m : ℕ) (q C : ℝ) : ℝ := (1 + C * ((m : ℝ) + 1)) *
  Real.exp (20 * (d : ℝ) * (m : ℝ) * Real.log 4 - (4 : ℝ) ^ (q * ((m : ℝ) / 2 - 1)))

abbrev certificateEvent := OAI.Anderson.certificateEvent
abbrev thresholdCriterion := OAI.Anderson.thresholdCriterion
abbrev finiteBoxThreshold := OAI.Anderson.finiteBoxThreshold

abbrev windowThreshold := AndersonAC.Blueprint.windowThreshold
abbrev CertificateFamily := AndersonAC.Blueprint.CertificateFamily
abbrev WeakCertificates := AndersonAC.Blueprint.WeakCertificates
/-- The true-variable event with arbitrary uniform certificate constants. -/

def boundedCertificateEvent (d n₀ m : ℕ) (u E Cr cp cg : ℝ) :
    Set (OAI.Anderson.TorusConfiguration d m) :=
  {ω | ∃ (A : Finset (Torus d m)) (r : Torus d m → ℂ) (G : Matrix (Torus d m) (Torus d m) ℂ),
    Fintype.card (Torus d m) ≤ 2 * A.card ∧ (∀ i ∈ A, ‖r i‖ ≤ Cr ∧ cp ≤ (r i).im) ∧
    OAI.Anderson.certificateMatrix n₀ m u E ω A r * G = 1 ∧
    G * OAI.Anderson.certificateMatrix n₀ m u E ω A r = 1 ∧ (∀ i ∈ A, cg ≤ (G i i).im)}
/-- Completion of Proposition 2.1, exposed as a true-variable probability
hypothesis until the earlier construction lanes supply their endpoints. -/

def UniformCertificateInput (d : ℕ) (e₂ : ℝ) : Prop :=
  ∃ cutoff : ℕ, ∃ Cr cp cg : ℝ, 0 < cp ∧ 0 < cg ∧
    ∀ n₀ m : ℕ, cutoff ≤ n₀ → 4 * n₀ ≤ m → ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
    ∀ E : ℝ, E ∈ OAI.Anderson.energyWindow d e₂ →
      (1 / 2 : ℝ≥0∞) ≤ OAI.Anderson.torusLaw d m (boundedCertificateEvent d n₀ m u E Cr cp cg)

structure ClearingGeometry (d m n₀ j l : ℕ) (u C : ℝ) where
  index : Fin l → ℕ
  core : Fin l → Finset (Torus d m)
  edits : Fin l → Finset (Torus d m)
  anchor : Fin l → Torus d m
  stages : ∀ a, n₀ ≤ index a ∧ index a ≤ j
  anchorMem : ∀ a, anchor a ∈ core a
  eligible : ∀ a, ((core a).card : ℝ) ≤ stageScale u (index a) m ^ (-nu d)
  coreRadius : ∀ a x, x ∈ core a → physicalDistance d m (anchor a) x ≤
    stageScale u (index a) m ^ (-nu d) * separationRadius (index a)
  separated : ∀ a b, a ≠ b → index a = index b → ∀ x ∈ core a, ∀ y ∈ core b,
    separationRadius (index a) < physicalDistance d m x y
  groupSize : ∀ a, ((edits a).card : ℝ) ≤ C * (heatLimit (stageScale u (index a) m) : ℝ)
  locations : ∀ a x, x ∈ edits a → ∃ y ∈ core a,
    physicalDistance d m x y ≤ inspectionRadius (index a) / 2

def geometryTerminals {d m n₀ j l : ℕ} {u C : ℝ}
    (T : ClearingGeometry d m n₀ j l u C) : Finset (Torus d m) := Finset.univ.biUnion T.edits
/-- §7.5 completed stage invariant. Λ⁺ is represented by its variational form. -/

def StageBounds (d m n₀ n : ℕ) (u cP CP cL CL C₀ : ℝ)
    (s : Endpoint (Torus d m)) (r : Torus d m → ℂ) : Prop :=
  let t := stageScale u n m
  let b := stageScale u n₀ m * t
  let X := inverseEnergy s.active (endpointEnergy s r t)
  let Λ := inverseEnergy Finset.univ (gradientEnergy (nnGraph d m))
  (∀ i ∈ s.active, s.g i i = r i ∧ cP ≤ (r i).im ∧ (r i).im ≤ CP ∧ ‖r i‖ ≤ CP) ∧
  (∀ i, rowFour (normalizedInverse s t) i ≤ t ^ (1 + delta)) ∧
  matrixNorm (squareKernel (normalizedInverse s t)) ≤ 1 / 3 ∧
  constantKernel s.active (endpointEnergy s r t) ∧
  Fintype.card (Torus d m) ≤ 2 * s.active.card ∧
  (∀ x y, physicalDistance d m x y / 2 - t ^ (-1.03 : ℝ) ≤
    terminalDistance (nnGraph d m) (Finset.univ \ s.active) x y) ∧
  (∀ y, neutral s.active y → cL * b * Λ y ≤ X y ∧
    X y ≤ C₀ * (∑ i ∈ s.active, (y i) ^ 2) + CL * b * Λ y ∧
    X y ≤ (1 + t ^ (0.005 * delta)) * (∑ i ∈ s.active, (y i) ^ 2 / (r i).im ^ 2) + CL * t * Λ y)
/-- Inputs already derived by ordinary sweep, assembly and reset. They are
listed rather than asserted as a hidden preservation implication. -/

structure PathwiseStageInputs (d m n₀ : ℕ) (u C : ℝ) where
  state : ℕ → Endpoint (Torus d m)
  r : ℕ → Torus d m → ℂ
  physical : ∀ n, n₀ ≤ n → n ≤ m → IsDampedEndpoint (state n) (r n) (stageScale u n m)
  nested : ∀ n, n₀ ≤ n → n < m → (state (n + 1)).active ⊆ (state n).active
  reset : ∀ n, n₀ ≤ n → n ≤ m → ∀ i ∈ (state n).active, (state n).g i i = r n i
  rows : ∀ n, n₀ ≤ n → n ≤ m → ∀ i,
    rowFour (normalizedInverse (state n) (stageScale u n m)) i ≤ stageScale u n m ^ (1 + delta)
  normStep : ∀ n, n₀ ≤ n → n < m →
    matrixNorm (squareKernel (normalizedInverse (state (n + 1)) (stageScale u (n + 1) m))) ≤
      matrixNorm (squareKernel (normalizedInverse (state n) (stageScale u n m))) + C * stageScale u n m ^ (0.10 * delta)
  rStep : ∀ n, n₀ ≤ n → n < m → ‖r (n + 1) - r n‖ ≤ C * stageScale u n m ^ (0.35 * delta)
  kernels : ∀ n, n₀ ≤ n → n ≤ m → constantKernel (state n).active (endpointEnergy (state n) (r n) (stageScale u n m))
  counts : ∀ n, n₀ ≤ n → n ≤ m → Fintype.card (Torus d m) ≤ 2 * (state n).active.card
  metrics : ∀ n, n₀ ≤ n → n ≤ m → ∀ x y,
    physicalDistance d m x y / 2 - stageScale u n m ^ (-1.03 : ℝ) ≤
      terminalDistance (nnGraph d m) (Finset.univ \ (state n).active) x y
  affineStep : ∀ n, n₀ ≤ n → n < m → ∀ y, neutral (state (n + 1)).active y →
    let θ := stageScale u (n + 1) m / stageScale u n m
    let old := inverseEnergy (state n).active (endpointEnergy (state n) (r n) (stageScale u n m)) y
    let new := inverseEnergy (state (n + 1)).active (endpointEnergy (state (n + 1)) (r (n + 1)) (stageScale u (n + 1) m)) y
    let target := θ * old + (1 - θ) * (∑ i ∈ (state (n + 1)).active, (y i) ^ 2 / (r n i).im ^ 2)
    (1 - C * stageScale u n m ^ (0.10 * delta)) * target ≤ new ∧
    new ≤ (1 + C * stageScale u n m ^ (0.10 * delta)) * target
/-- Finite deterministic witness family and its partition sum. -/

def possibleLabels (d m j : ℕ) : Finset (BirthLabel (Torus d m)) := by
  classical
  exact ((Finset.range (j + 1) ×ˢ (Finset.univ : Finset BirthType)) ×ˢ Finset.univ).image
    (fun p => ⟨p.1.1, p.1.2, p.2⟩)

def witnessFamily (d m n₀ j : ℕ) (x : Torus d m) : Finset (Finset (BirthLabel (Torus d m))) := by
  classical
  exact (possibleLabels d m j).powerset.filter (IsWitness d m n₀ j x)

def witnessMass (d m n₀ j : ℕ) (c : ℝ) : ℝ :=
  sSup (Set.range fun x : Torus d m => ∑ L ∈ witnessFamily d m n₀ j x, witnessWeight c L)
/-- The snapshot graph is frozen before any component trial. -/

def snapshotGraph (d m : ℕ) (pending : Finset (Torus d m)) (R : ℝ) : SimpleGraph pending :=
  SimpleGraph.fromRel fun x y => physicalDistance d m x.val y.val ≤ R

def eligibleCore (d : ℕ) {ι : Type} (B : Finset ι) (t : ℝ) : Prop := (B.card : ℝ) ≤ t ^ (-nu d)

inductive TrialOutcome | done | fail deriving DecidableEq
/-- Query records survive both outcomes; numerical failure restores the prestate. -/

structure TrialRecord (ι Q : Type) where
  before : Endpoint ι
  output : Endpoint ι
  outcome : TrialOutcome
  queriedBefore : Finset Q
  queriedAfter : Finset Q
  pendingAfter : Finset ι
  inspected : Finset ι
  retained : queriedBefore ⊆ queriedAfter
  rollback : outcome = .fail → output = before
  failedMarks : outcome = .fail → inspected ⊆ pendingAfter
  successfulTerminals : outcome = .done → ∀ i ∈ inspected, i ∉ output.active

def thresholdIndex (d : ℕ) (hne : ∃ k, thresholdCriterion d k) : ℕ := by
  classical
  exact Nat.find hne

def intrinsicThreshold (d : ℕ) (hne : ∃ k, thresholdCriterion d k) : ℝ :=
  Real.sqrt 3 / (2 : ℝ) ^ thresholdIndex d hne

def cubeGradient (d m : ℕ) (Q : Finset (Torus d m)) (v : Torus d m → ℝ) : ℝ := by
  classical
  exact (1 / 2) * ∑ i ∈ Q, ∑ j ∈ Q, if (nnGraph d m).Adj i j then (v i - v j) ^ 2 else 0
end AndersonAC.S78
