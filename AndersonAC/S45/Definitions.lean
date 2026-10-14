import AndersonAC.Blueprint.FiniteInputs

/-!
Exact interfaces for Anderson paper §§4–5.
Definition-only base. No theorem placeholders or new axioms occur here.
Quantitative statement constants are quantified before finite index sizes.
Real forms suffice; `complexForm` extends them to complex charges/potentials.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators
namespace AndersonAC.S45

abbrev CMat (ι : Type*) := Matrix ι ι ℂ
abbrev RMat (ι : Type*) := Matrix ι ι ℝ
abbrev Form (ι : Type*) := (ι → ℝ) → ℝ

def delta : ℝ := 1 / 100
def kappa : ℝ := delta / 200
def beta : ℝ := 21 * delta / 50
def power (t e : ℝ) : ℝ := Real.rpow t e
def rowCap (t : ℝ) : ℝ := power t (1 + delta)
def logFactor (t : ℝ) : ℝ := 1 + Real.log (1 / t)
def tileSide (n : ℕ) : ℕ := 4 ^ (6 * n)
def tileSlots (d n : ℕ) : ℕ := tileSide n ^ d

def l2sq {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜] (f : ι → 𝕜) : ℝ :=
  ∑ i, ‖f i‖ ^ 2

def l1 {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜] (f : ι → 𝕜) : ℝ :=
  ∑ i, ‖f i‖

def rowNorm {ι : Type*} [Fintype ι] (A : CMat ι) : ℝ := ‖fun i => l1 (A i)‖
def neutral {ι : Type*} [Fintype ι] (y : ι → ℝ) : Prop := ∑ i, y i = 0
def qform {ι : Type*} [Fintype ι] (A : RMat ι) : Form ι :=
  fun f => ∑ i, f i * (A *ᵥ f) i

def complexForm {ι : Type*} (Q : Form ι) (z : ι → ℂ) : ℝ :=
  Q (fun i => (z i).re) + Q (fun i => (z i).im)

def dualForm {ι : Type*} [Fintype ι] (Q : Form ι) : Form ι :=
  fun y => sSup {a : ℝ | ∃ f : ι → ℝ, a = 2 * (∑ i, y i * f i) - Q f}

def formAbsLe {ι : Type*} (Q R : Form ι) (a : ℝ) : Prop :=
  ∀ f, |Q f| ≤ a * R f

def formComparable {ι : Type*} (Q R : Form ι) (C : ℝ) : Prop :=
  ∀ f, R f / C ≤ Q f ∧ Q f ≤ C * R f

def constantKernel {ι : Type*} [Fintype ι] (D : RMat ι) : Prop :=
  D.IsSymm ∧ (∀ f, 0 ≤ qform D f) ∧
    (∀ f, qform D f = 0 ↔ ∃ a : ℝ, ∀ i, f i = a)

def laplacian {ι : Type*} [Fintype ι] [DecidableEq ι] (c : RMat ι) : RMat ι :=
  fun i j => if i = j then ∑ k, if k = i then 0 else c i k else -c i j

def matrixIm {ι : Type*} (A : CMat ι) : CMat ι := fun i j => ((A i j).im : ℂ)
abbrev entrywiseSquare {ι : Type*} (h : CMat ι) : CMat ι := AndersonAC.Blueprint.entrywiseSquare h
def entryAbsSquare {ι : Type*} (h : CMat ι) : RMat ι := fun i j => ‖h i j‖ ^ 2

structure State (ι : Type*) where
  g : CMat ι
  r : ι → ℂ

namespace State
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def p (s : State ι) : ι → ℝ := fun i => (s.r i).im
def q (s : State ι) : ι → ℝ := fun i => (s.g i i).im
def h (t : ℝ) (s : State ι) : CMat ι := (Real.sqrt t : ℂ) • s.g
def K (t : ℝ) (s : State ι) : CMat ι := entrywiseSquare (s.h t)
def F (t : ℝ) (s : State ι) : RMat ι := entryAbsSquare (s.h t)
def D (t : ℝ) (s : State ι) : RMat ι :=
  diagonal (fun i => s.p i * s.q i) - diagonal s.p * s.F t * diagonal s.p

def X (t : ℝ) (s : State ι) : Form ι := dualForm (qform (s.D t))
def P (t : ℝ) (s : State ι) : CMat ι := (1 - s.K t)⁻¹
def rawLag (s : State ι) : ι → ℂ := fun i => s.g i i - s.r i
def lag (t : ℝ) (s : State ι) : ι → ℂ := s.P t *ᵥ s.rawLag
def z (t : ℝ) (s : State ι) : ι → ℂ := (Real.sqrt t : ℂ) • s.rawLag
def U (t : ℝ) (s : State ι) : ι → ℂ := s.P t *ᵥ s.z t
def fourthRow (t : ℝ) (s : State ι) (C : Finset ι) (i : ι) : ℝ :=
  ∑ j ∈ C, ‖s.h t i j‖ ^ 4

def ward (t : ℝ) (s : State ι) : Prop :=
  s.h t * diagonal (fun i => (s.p i : ℂ)) * (s.h t)ᴴ = matrixIm s.g
end State

section FiniteAlgebra
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def restrict {α : Type*} (A : Matrix ι ι α) (S : Finset ι) : Matrix S S α :=
  A.submatrix Subtype.val Subtype.val

def pad {α : Type*} [Zero α] (S : Finset ι) (A : Matrix S S α) : Matrix ι ι α :=
  fun i j => if hi : i ∈ S then if hj : j ∈ S then A ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0

def mask {α : Type*} [Zero α] (S : Finset ι) (A : Matrix ι ι α) : Matrix ι ι α :=
  pad S (restrict A S)

def survivors (x : ι) : Finset ι := Finset.univ.erase x

def schur {𝕜 : Type*} [RCLike 𝕜] (A : Matrix ι ι 𝕜) (E : Finset ι) : Matrix (↑(Eᶜ) : Type _) (↑(Eᶜ) : Type _) 𝕜 :=
  restrict A Eᶜ -
    A.submatrix (fun i : (↑(Eᶜ) : Type _) => i.val) (fun i : E => i.val) * (restrict A E)⁻¹ *
    A.submatrix (fun i : E => i.val) (fun i : (↑(Eᶜ) : Type _) => i.val)

def scalarSchur {𝕜 : Type*} [RCLike 𝕜] (A : Matrix ι ι 𝕜) (x : ι) :
    Matrix (survivors x) (survivors x) 𝕜 :=
  fun i j => A i j - A i x * (A x x)⁻¹ * A x j

def gamma (t : ℝ) (s : State ι) (x : ι) (ξ : ℝ) : ℂ :=
  ((ξ : ℂ) + t * s.r x) /
    ((Real.sqrt t : ℂ) * (1 + ((ξ : ℂ) + t * s.r x) * s.g x x))

def deleteState (t : ℝ) (s : State ι) (x : ι) (ξ : ℝ) : State (survivors x) where
  g i j := s.g i j - ((ξ : ℂ) + t * s.r x) * s.g i x * s.g x j /
    (1 + ((ξ : ℂ) + t * s.r x) * s.g x x)
  r i := s.r i

def Jinc (t : ℝ) (s : State ι) (x : ι) (ξ : ℝ) : CMat ι :=
  pad (survivors x) (fun i j =>
    -2 * gamma t s x ξ * s.h t i x * s.h t i j * s.h t x j +
    ((gamma t s x ξ)^2 - (1 - s.K t x x)⁻¹) * s.K t i x * s.K t x j)

def Ledge (t : ℝ) (s : State ι) (x : ι) (ξ : ℝ) : RMat (survivors x) :=
  fun i j => s.p i * s.p j *
    (-2 * (gamma t s x ξ * star (s.h t i j) * s.h t i x * s.h t x j).re +
    (‖gamma t s x ξ‖^2 - s.p x / (s.q x - s.p x * s.F t x x)) *
      s.F t i x * s.F t x j)

def Linc (t : ℝ) (s : State ι) (x : ι) (ξ : ℝ) : RMat ι :=
  pad (survivors x) (laplacian (Ledge t s x ξ))

def lagInc (t : ℝ) (s : State ι) (x : ι) (ξ : ℝ) : ι → ℂ :=
  fun i => if hi : i ∈ survivors x then
    (deleteState t s x ξ).lag t ⟨i, hi⟩ - s.lag t i else 0

def fourthProxy (t : ℝ) (s : State ι) (C : Finset ι) (i x : ι) (ξ : ℝ) : ℝ :=
  if i = x then 0 else ∑ j ∈ C.erase x,
    (‖s.h t i j - gamma t s x ξ * s.h t i x * s.h t x j‖^4 - ‖s.h t i j‖^4)

def forcing (t : ℝ) (s : State ι) (x : ι) (ξ : ℝ) : ι → ℂ :=
  fun i => if i = x then 0 else
    -(gamma t s x ξ + s.z t x / (1 - s.K t x x)) * s.K t i x +
      (Jinc t s x ξ *ᵥ s.U t) i
end FiniteAlgebra

structure PortMap (P I : Type*) where
  site : P → I
  weight : P → ℝ

namespace PortMap
variable {P I : Type*} [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]
def mass (v : PortMap P I) (i : I) : ℝ :=
  ∑ x, if v.site x = i then v.weight x ^ 4 else 0

def liftState (v : PortMap P I) (s : State I) : State P where
  g x y := v.weight x * v.weight y * s.g (v.site x) (v.site y)
  r x := v.weight x ^ 2 * s.r (v.site x)

def sumCharge (v : PortMap P I) (y : P → ℝ) : I → ℝ :=
  fun i => ∑ x, if v.site x = i then y x else 0

def average (v : PortMap P I) (f : P → ℝ) : I → ℝ :=
  fun i => ∑ x, if v.site x = i then v.weight x ^ 4 * f x else 0

def Q (v : PortMap P I) : Matrix P I ℂ :=
  fun x i => if v.site x = i then (v.weight x ^ 2 : ℝ) else 0
end PortMap

def initialPorts (I : Type*) := I × Bool
instance {I : Type*} [Fintype I] : Fintype (initialPorts I) := inferInstanceAs (Fintype (I × Bool))
instance {I : Type*} [DecidableEq I] : DecidableEq (initialPorts I) := inferInstanceAs (DecidableEq (I × Bool))
def splitPorts (I : Type*) (θ : ℝ) : PortMap (initialPorts I) I where
  site := Prod.fst
  weight x := power (if x.2 then θ else 1 - θ) (1 / 4)

def reserves {I : Type*} [Fintype I] [DecidableEq I] : Finset (initialPorts I) :=
  Finset.univ.filter (fun x => x.2 = true)

def reserveCharge {I : Type*} (y : I → ℝ) : initialPorts I → ℝ :=
  fun x => if x.2 then y x.1 else 0

def physicalPrefix {I P : Type*} [Fintype I] [DecidableEq I] [Fintype P]
    [DecidableEq P] (t : ℝ) (M : RMat I) (r : I → ℂ) (v : PortMap P I) : State I where
  g := (M.map (fun z => (z : ℂ)) -
    diagonal (fun i => (t * v.mass i : ℝ) * r i))⁻¹
  r := r


def spatialDual {P I : Type*} [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]
    (v : PortMap P I) (b : ℝ) (Λplus : Form I) : Form P :=
  fun y => l2sq y + b * Λplus (v.sumCharge y)

def spatialEnergy {P I : Type*} [Fintype P] [Fintype I]
    (site : P → I) (b : ℝ) (Λ : Form I) : Form P :=
  fun f => sInf {a : ℝ | ∃ α : P → ℝ, ∃ v : I → ℝ,
    (∀ x, f x = α x + v (site x)) ∧ a = l2sq α + Λ v / b}


structure StageBoundary {I : Type*} [Fintype I] [DecidableEq I]
    (t b C cLow cHigh : ℝ) (Λplus W : Form I) (s : State I) : Prop where
  constants : 1 ≤ C ∧ 0 < cLow ∧ 0 < cHigh
  scale_pos : 0 < t
  b_pos : 0 < b
  b_le : b ≤ t
  broad : ∀ i, ‖s.r i‖ ≤ C ∧ 1 / C ≤ s.p i ∧ s.p i ≤ C
  symmetric : s.g.IsSymm
  ward : s.ward t
  fixed_point : ∀ i, s.g i i = s.r i
  K_cap : ‖s.K t‖ ≤ 1 / 3
  row_cap : ∀ i, s.fourthRow t Finset.univ i ≤ rowCap t
  kernel : constantKernel (s.D t)
  lower : ∀ y, neutral y → cLow * b * Λplus y ≤ s.X t y
  rough : ∀ y, neutral y → s.X t y ≤ C * l2sq y + cHigh * b * Λplus y
  sharp : ∀ y, neutral y → s.X t y ≤
    (1 + power t kappa) * (∑ i, y i ^ 2 / s.p i ^ 2) + cHigh * t * Λplus y
  comparison : formComparable (qform (s.D t)) W C


structure Prestate {P : Type*} [Fintype P] [DecidableEq P]
    (t C : ℝ) (Λplus Wstar : Form P) (s : State P) : Prop where
  scale : 0 < t ∧ t < 1
  broad : ∀ i, ‖s.r i‖ ≤ C ∧ 1 / C ≤ s.p i ∧ s.p i ≤ C
  symmetric : s.g.IsSymm
  ward : s.ward t
  K_cap : ‖s.K t‖ ≤ 1 / 2
  invertible : IsUnit (1 - s.K t)
  kernel : constantKernel (s.D t)
  row_cap : ∀ i, s.fourthRow t Finset.univ i ≤ rowCap t
  lag_cap : ∀ i, ‖s.lag t i‖ ≤ power t beta
  sharp : ∀ y, neutral y → s.X t y ≤
    (1 + C * power t kappa) * (∑ i, y i ^ 2 / s.p i ^ 2) + C * t * Λplus y
  fourier : ∀ y, neutral y → Λplus y ≤ C * power (l1 y) (4 / 3) * power (l2sq y) (1 / 3)
  dual_fourier : ∀ y, neutral y → Wstar y ≤
    l2sq y + C * t * power (l1 y) (4 / 3) * power (l2sq y) (1 / 3)
  volume : 1 / (Fintype.card P : ℝ) ≤ C * power t (1 + delta + kappa)

structure MomentLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (t C : ℝ) (ξ : Ω → ℝ) : Prop where
  measurable : Measurable ξ
  mean : (∫ ω, ξ ω ∂μ) = 0
  variance : (∫ ω, (ξ ω)^2 ∂μ) = t
  bounded : ∀ᵐ ω ∂μ, |ξ ω| ≤ C * Real.sqrt t























def arrayA1 {P : Type*} [Fintype P] (S : Finset P) (Y : P → P → ℂ) : ℝ :=
  ‖fun i => ∑ x ∈ S, ‖Y i x‖‖
def arrayA2sq {P : Type*} [Fintype P] (S : Finset P) (Y : P → P → ℂ) : ℝ :=
  ‖fun i => ∑ x ∈ S, ‖Y i x‖^2‖






def pullback {P H : Type*} [Fintype P] [Fintype H]
    (B : Matrix P H ℝ) (L : RMat P) : RMat H := Bᵀ * L * B


/-! Fixed ambient records, including the values retained at later deleted coordinates. -/
structure LiveState (P : Type*) [Fintype P] [DecidableEq P] where
  live : Finset P
  g : CMat P

namespace LiveState
variable {P : Type*} [Fintype P] [DecidableEq P]
def state (a : LiveState P) (r : P → ℂ) : State a.live where
  g := restrict a.g a.live
  r i := r i

def ambient (a : LiveState P) (r : P → ℂ) : State P := ⟨mask a.live a.g, r⟩
def ambientLag (a : LiveState P) (t : ℝ) (r : P → ℂ) : P → ℂ :=
  fun i => if hi : i ∈ a.live then (a.state r).lag t ⟨i, hi⟩ else 0
end LiveState

structure StepRel {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (r : P → ℂ) (a b : LiveState P) (x : P) (ξ : ℝ) : Prop where
  pivot_live : x ∈ a.live
  survivors : b.live = a.live.erase x
  update : b.g = mask b.live (fun i j => a.g i j -
    ((ξ : ℂ) + t * r x) * a.g i x * a.g x j /
      (1 + ((ξ : ℂ) + t * r x) * a.g x x))
  denominator : 1 + ((ξ : ℂ) + t * r x) * a.g x x ≠ 0

structure Sequence (P : Type*) [Fintype P] [DecidableEq P] where
  length : ℕ
  state : ℕ → LiveState P
  pivot : ℕ → Option P
  scalar : ℕ → ℝ

namespace Sequence
variable {P : Type*} [Fintype P] [DecidableEq P]
def wellFormed (q : Sequence P) (t : ℝ) (r : P → ℂ) : Prop :=
  (∀ k ≤ q.length, (q.state k).g = mask (q.state k).live (q.state k).g) ∧
  ∀ k < q.length, match q.pivot k with
    | none => q.state (k + 1) = q.state k
    | some x => StepRel t r (q.state k) (q.state (k + 1)) x (q.scalar k)

def stepJ (q : Sequence P) (t : ℝ) (r : P → ℂ) (k : ℕ) : CMat P :=
  match q.pivot k with
    | none => 0
    | some x => mask (q.state (k + 1)).live (Jinc t ((q.state k).ambient r) x (q.scalar k))
def stepL (q : Sequence P) (t : ℝ) (r : P → ℂ) (k : ℕ) : RMat P :=
  match q.pivot k with
    | none => 0
    | some x => mask (q.state (k + 1)).live (Linc t ((q.state k).ambient r) x (q.scalar k))
def stepLag (q : Sequence P) (t : ℝ) (r : P → ℂ) (k : ℕ) : P → ℂ :=
  fun i => if i ∈ (q.state (k + 1)).live then
    (q.state (k + 1)).ambientLag t r i - (q.state k).ambientLag t r i else 0

def stepRow (q : Sequence P) (t : ℝ) (r : P → ℂ) (cols : Finset P) (k : ℕ) : P → ℝ :=
  fun i => if i ∈ (q.state (k + 1)).live then
    (∑ j ∈ cols ∩ (q.state (k + 1)).live,
      (‖((q.state (k + 1)).ambient r).h t i j‖^4 -
      ‖((q.state k).ambient r).h t i j‖^4)) / rowCap t else 0

def Jrecord (q : Sequence P) (t : ℝ) (r : P → ℂ) (K : Finset ℕ) : CMat P :=
  ∑ k ∈ K, q.stepJ t r k
def Lrecord (q : Sequence P) (t : ℝ) (r : P → ℂ) (K : Finset ℕ) : RMat P :=
  ∑ k ∈ K, q.stepL t r k
def lagRecord (q : Sequence P) (t : ℝ) (r : P → ℂ) (K : Finset ℕ) : P → ℂ :=
  ∑ k ∈ K, q.stepLag t r k
def rowRecord (q : Sequence P) (t : ℝ) (r : P → ℂ) (cols : Finset P) (K : Finset ℕ) : P → ℝ :=
  ∑ k ∈ K, q.stepRow t r cols k

def valid (q : Sequence P) (t : ℝ) (r : P → ℂ) (D0 : RMat P) (k : ℕ) : Prop :=
  ‖q.Jrecord t r (Finset.range k)‖ ≤ power t (delta / 10) ∧
  formAbsLe (qform (q.Lrecord t r (Finset.range k))) (qform D0) (power t (delta / 10)) ∧
  (∀ i : (q.state k).live, ((q.state k).state r).fourthRow t Finset.univ i ≤ rowCap t) ∧
  (∀ i : (q.state k).live, ‖((q.state k).state r).lag t i‖ ≤ power t beta)
end Sequence




/-! §5 geometry. `G` is the actual finite hopping graph; the torus shell
and cube inequalities are inputs to be supplied by the lattice module. -/

def walkCost {I : Type*} [DecidableEq I] (G : SimpleGraph I) (T : Finset I)
    {i j : I} : G.Walk i j → ℕ
  | .nil => 0
  | @SimpleGraph.Walk.cons _ _ a b _ _ w =>
      (if a ∈ T ∨ b ∈ T then 0 else 1) + walkCost G T w

def collapsedDistance {I : Type*} [DecidableEq I] (G : SimpleGraph I) (T : Finset I)
    (i j : I) : ℝ := sInf {a : ℝ | ∃ w : G.Walk i j, a = (walkCost G T w : ℝ)}

def graphEnergy {I : Type*} [Fintype I] (G : SimpleGraph I) [DecidableRel G.Adj] : Form I :=
  fun v => (1 / 2 : ℝ) * ∑ i, ∑ j, if G.Adj i j then (v i - v j)^2 else 0

structure FiniteGeometry (I : Type*) [Fintype I] [DecidableEq I] (d : ℕ) where
  graph : SimpleGraph I
  decidable : DecidableRel graph.Adj
  connected : graph.Connected
  degree : ∀ i, (Finset.univ.filter (graph.Adj i)).card ≤ 2 * d

attribute [instance] FiniteGeometry.decidable

def FiniteGeometry.distance {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ}
    (g : FiniteGeometry I d) (i j : I) : ℝ := g.graph.dist i j

def terminalSchur {I : Type*} [Fintype I] [DecidableEq I]
    (H : RMat I) (A : Finset I) : RMat A :=
  restrict H A -
    H.submatrix (fun i : A => i.val) (fun i : (↑(Aᶜ) : Type _) => i.val) * (restrict H Aᶜ)⁻¹ *
    H.submatrix (fun i : (↑(Aᶜ) : Type _) => i.val) (fun i : A => i.val)

def dampedActive {I : Type*} [Fintype I] [DecidableEq I]
    (H : RMat I) (A : Finset I) (τ : A → ℝ) : CMat A :=
  (terminalSchur H A).map (fun z => (z : ℂ)) -
    diagonal (fun i => Complex.I * (τ i : ℂ))





structure ShellBounds {P : Type*} [Fintype P] (d : ℕ) (C : ℝ) (dist : P → P → ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ dist i j
  symmetric : ∀ i j, dist i j = dist j i
  triangle : ∀ i j k, dist i k ≤ dist i j + dist j k
  self : ∀ i, dist i i = 0
  count : ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ i,
    (∑ j, Real.exp (-u * dist i j)) ≤ C * power u (-(d : ℝ))
  second : ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ i,
    (∑ j, dist i j^2 * Real.exp (-u * dist i j)) ≤ C * power u (-(d : ℝ) - 2)





/-! §5.2 concrete local pair space. Constants in v are removed by subtracting
its average; orthonormal coordinates are chosen once, before the trial. -/
structure LocalCube (P I : Type*) [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I] where
  site : P → I
  outer : Finset I
  cutoff : I → ℝ
  edge : RMat outer

def LocalCube.ports {P I : Type*} [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]
    (Q : LocalCube P I) : Finset P := Finset.univ.filter (fun x => Q.site x ∈ Q.outer)

def LocalCube.energy {P I : Type*} [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]
    (Q : LocalCube P I) (b : ℝ) (α : Q.ports → ℝ) (v : Q.outer → ℝ) : ℝ :=
  l2sq α + qform (laplacian Q.edge) v / b

def LocalCube.extend {P I : Type*} [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]
    (Q : LocalCube P I) (α : Q.ports → ℝ) (v : Q.outer → ℝ) : P → ℝ :=
  fun x => if hx : x ∈ Q.ports then Q.cutoff (Q.site x) *
    (α ⟨x, hx⟩ + v ⟨Q.site x, (Finset.mem_filter.mp hx).2⟩ -
      (∑ i, v i) / Q.outer.card) else 0

structure LocalCoordinates {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] (Q : LocalCube P I) (b : ℝ) (h : ℕ) where
  alpha : Matrix Q.ports (Fin h) ℝ
  potential : Matrix Q.outer (Fin h) ℝ
  neutral_potential : ∀ v, neutral (potential *ᵥ v)
  normalized : ∀ v, Q.energy b (alpha *ᵥ v) (potential *ᵥ v) = l2sq v
  complete : ∀ α v, neutral v → ∃ w, alpha *ᵥ w = α ∧ potential *ᵥ w = v

def LocalCoordinates.B {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] {Q : LocalCube P I} {b : ℝ} {h : ℕ}
    (a : LocalCoordinates Q b h) : Matrix P (Fin h) ℝ :=
  fun x j => Q.extend (fun i => a.alpha i j) (fun i => a.potential i j) x




structure TileCover {P I : Type*} [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]
    (d : ℕ) (t b C : ℝ) (dist : P → P → ℝ) where
  site : P → I
  energy : Form I
  count : ℕ
  tile : Fin count → Finset P
  inner : Fin count → Finset P
  cube : Fin count → LocalCube P I
  dim : Fin count → ℕ
  coords : ∀ T, LocalCoordinates (cube T) b (dim T)
  /-- The local potential energy is the cube gradient energy `‖∇v‖²_{Q'}`
  (05-local-sweeps.tex:249-256), so its conductances are symmetric; this makes
  `qform (laplacian edge)` is invariant under constant shifts. -/
  edge_symm : ∀ T, ((cube T).edge).IsSymm
  cutoff_one : ∀ T, ∀ i ∈ inner T, (cube T).cutoff ((cube T).site i) = 1
  same_site : ∀ T, (cube T).site = site
  cover : ∀ x, ∃! T, x ∈ tile T
  inside : ∀ T, tile T ⊆ inner T ∧ inner T ⊆ (cube T).ports
  buffer : ∀ T, ∀ x ∈ tile T, ∀ i, i ∉ inner T → power t (-6) ≤ dist i x
  overlap : ∀ i, (Finset.univ.filter (fun T => i ∈ inner T)).card ≤ C
  dimension : ∀ T, (dim T : ℝ) ≤ C * power t (-6 * (d : ℝ))
  local_split : ∀ T, ∀ w : Fin (dim T) → ℝ, ∃ α : P → ℝ, ∃ v : I → ℝ,
    (∀ x, ((coords T).B *ᵥ w) x = α x + v (site x)) ∧
      l2sq α + energy v / b ≤ C * l2sq w
  kernel_energy : ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ α : P → ℝ, ∀ v : I → ℝ,
    ((1 / 2 : ℝ) * ∑ i, ∑ j, Real.exp (-u * dist i j) *
      (α i + v (site i) - α j - v (site j))^2) ≤
        C * (power u (-(d : ℝ)) * l2sq α + power u (-(d : ℝ) - 2) * energy v)
  local_sum : ∀ α : P → ℝ, ∀ v : I → ℝ,
    (∑ T, (cube T).energy b (fun x => α x) (fun i => v i)) ≤
      C * (l2sq α + energy v / b)


def localBudget {P I : Type*} [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]
    {d : ℕ} {t b C : ℝ} {dist : P → P → ℝ}
    (cover : TileCover (P := P) (I := I) d t b C dist) (T : Fin cover.count)
    (J : CMat P) (L : RMat P) (u : P → ℂ) (Ra Rr : P → ℝ) : Prop :=
    (∀ i ∈ cover.inner T, ‖u i‖ ≤ power t (11 * delta / 25)) ∧
    (∀ i ∈ cover.inner T, |Ra i| ≤ power t (delta / 2000) ∧ |Rr i| ≤ power t (delta / 2000)) ∧
    ‖mask (cover.inner T) J‖ ≤ power t (delta / 8) ∧
    ‖pullback (cover.coords T).B L‖ ≤ power t (delta / 8)

structure TraceTails {P : Type*} [Fintype P] [DecidableEq P]
    (q : Sequence P) (t C c : ℝ) (r : P → ℂ) (res : Finset P)
    (dist : P → P → ℝ) : Prop where
  J : ∀ k < q.length, ∀ x, q.pivot k = some x → ∀ i j,
    ‖q.stepJ t r k i j‖ ≤ power t (-C) * Real.exp (-c * t^3 * (dist i x + dist j x))
  L : ∀ k < q.length, ∀ x, q.pivot k = some x → ∀ i j, i ≠ j →
    |q.stepL t r k i j| ≤ power t (-C) * Real.exp (-c * t^3 * (dist i x + dist j x))
  lag : ∀ k < q.length, ∀ x, q.pivot k = some x → ∀ i,
    ‖q.stepLag t r k i‖ ≤ power t (-C) * Real.exp (-c * t^3 * dist i x)
  rows : ∀ k < q.length, ∀ x, q.pivot k = some x → ∀ i,
    |q.stepRow t r Finset.univ k i| + |q.stepRow t r res k i| ≤
      power t (-C) * Real.exp (-c * t^3 * dist i x)



/-! Lemma 5.6. Golden–Thompson is the sole external matrix analytic theorem.
The predictable variance is a scalar, not a matrix-norm-of-total-variance surrogate. -/
open scoped ComplexOrder

def dilation {P H : Type*} (B : Matrix P H ℂ) : CMat (P ⊕ H) :=
  fromBlocks 0 B Bᴴ 0

def traceExp {P : Type*} [Fintype P] [DecidableEq P] (A : CMat P) : ℝ := (NormedSpace.exp A).trace.re

def GoldenThompson : Prop := ∀ (n : ℕ) (A B : CMat (Fin n)),
  A.IsHermitian → B.IsHermitian → traceExp (A + B) ≤
    ((NormedSpace.exp A * NormedSpace.exp B).trace).re

def partialSum {Ω E : Type*} [AddCommMonoid E] (Y : ℕ → Ω → E) (n : ℕ) (ω : Ω) : E :=
  ∑ k ∈ Finset.range n, Y (k + 1) ω

def centered {Ω P : Type*} [MeasurableSpace Ω] [Fintype P] [DecidableEq P]
    (μ : Measure Ω) (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (Z : ℕ → Ω → CMat P) :
    ℕ → Ω → CMat P :=
  fun k ω => if k = 0 then 0 else Z k ω - μ[Z k | ℱ (k - 1)] ω

structure MatrixDiffHyp {Ω P : Type*} [MeasurableSpace Ω] [Fintype P] [DecidableEq P]
    (μ : Measure Ω) (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (Y : ℕ → Ω → CMat P) (v : ℕ → Ω → ℝ) (J V : ℝ) : Prop where
  adapted : StronglyAdapted ℱ Y
  integrable : ∀ k, Integrable (Y k) μ
  square_integrable : ∀ k, Integrable (fun ω => (Y k ω)^2) μ
  hermitian : ∀ k, ∀ᵐ ω ∂μ, (Y (k + 1) ω).IsHermitian
  centered : ∀ k, μ[Y (k + 1) | ℱ k] =ᵐ[μ] 0
  jump : ∀ k, ∀ᵐ ω ∂μ, ‖Y (k + 1) ω‖ ≤ J
  predictable : ∀ k, StronglyMeasurable[ℱ k] (v k)
  variance_nonneg : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ v k ω
  variance : ∀ k, ∀ᵐ ω ∂μ,
    μ[(fun ω => (Y (k + 1) ω)^2) | ℱ k] ω ≤ (v k ω) • (1 : CMat P)
  total_variance : ∀ n, ∀ᵐ ω ∂μ, (∑ k ∈ Finset.range n, v k ω) ≤ V

def traceProcess {Ω P : Type*} [Fintype P] [DecidableEq P] (u C : ℝ)
    (Y : ℕ → Ω → CMat P) (v : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n ω => traceExp (u • partialSum Y n ω -
    (C * u^2 * (∑ k ∈ Finset.range n, v k ω)) • (1 : CMat P))















/-! §5.5: local trial concentration and retained-history/retry interfaces. -/
inductive MonitorKind | lag | matrix | row deriving DecidableEq

def monitorBudget (t : ℝ) : MonitorKind → ℝ
  | .lag => power t (11 * delta / 25)
  | .matrix => power t (delta / 8)
  | .row => power t (delta / 2000)
def monitorJump (t : ℝ) : MonitorKind → ℝ
  | .lag => logFactor t * power t (delta / 2)
  | .matrix => power t (delta / 4)
  | .row => power t (kappa / 2)
def monitorVariance (t : ℝ) : MonitorKind → ℝ
  | .lag => logFactor t ^ 3 * power t delta
  | .matrix => logFactor t * power t (delta / 2)
  | .row => logFactor t * power t kappa

def monitorBias (t : ℝ) : MonitorKind → ℝ
  | .lag => logFactor t ^ 2 * (power t (2 * beta) + Real.sqrt t) +
      logFactor t ^ 3 * power t (delta / 2)
  | .matrix => logFactor t * power t beta
  | .row => logFactor t * power t kappa

structure TrialInputs {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (s : ℕ) (d : ℕ) (t C : ℝ) where
  kind : Fin s → MonitorKind
  dimension : Fin s → ℕ
  raw : ∀ i, ℕ → Ω → CMat (Fin (dimension i))
  envelope : Fin s → ℕ → Ω → ℝ
  differences : ∀ i, MatrixDiffHyp μ ℱ (centered μ ℱ (raw i)) (envelope i)
    (C * monitorJump t (kind i)) (C * monitorVariance t (kind i))
  drift : ∀ i N, ∀ᵐ ω ∂μ,
    ‖∑ k ∈ Finset.range N, μ[raw i (k + 1) | ℱ k] ω‖ ≤ C * monitorBias t (kind i)
  dimensions : (∑ i, (dimension i : ℝ)) ≤ C * power t (-6 * (d : ℝ))

def TrialInputs.crossing {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} {s d : ℕ} {t C : ℝ}
    (a : TrialInputs μ ℱ s d t C) : Set Ω :=
  {ω | ∃ i N, monitorBudget t (a.kind i) < ‖partialSum (a.raw i) N ω‖}




structure QueryHistory (I : Type*) where
  coupled : Set I
  trueQueries : Set (I × ℕ)
  depth : ℕ

def QueryHistory.fresh {I : Type*} (q : QueryHistory I) : Prop :=
  ∀ i ∈ q.coupled, ∀ k, q.depth < k → (i, k) ∉ q.trueQueries

def QueryHistory.failedTile {I : Type*} (q : QueryHistory I) (T : Set I)
    (newQueries : Set (I × ℕ)) : QueryHistory I :=
  ⟨q.coupled \ T, q.trueQueries ∪ newQueries, q.depth⟩





/-! §5.6 deterministic endpoint and the final true-suffix normalization. -/








/-! Interfaces from the blueprint are exposed under the §4–5 names used by these
theorems. -/

abbrev opNorm {P : Type*} [Fintype P] [DecidableEq P] (A : CMat P) : ℝ :=
  AndersonAC.Blueprint.opNorm A
abbrev matrixImag {P : Type*} [Fintype P] [DecidableEq P] (A : CMat P) : CMat P :=
  AndersonAC.Blueprint.matrixImag A
abbrev twoSidedInverse {P : Type*} [Fintype P] [DecidableEq P] (A G : CMat P) : Prop :=
  AndersonAC.Blueprint.twoSidedInverse A G
abbrev matrixCondExp {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    (m : MeasurableSpace Ω) {N : ℕ} (Y : Ω → CMat (Fin N)) : Ω → CMat (Fin N) :=
  @AndersonAC.Blueprint.matrixCondExp Ω mΩ μ m N Y
abbrev ConcentrationInput := AndersonAC.Blueprint.ConcentrationInput
abbrev DeletionInput := AndersonAC.Blueprint.DeletionInput

/-! Proposition 4.8's table, in a type that exposes means, both matrix square
orders, scalar squares, and individual jumps. -/
structure FamilyTable {P H Ω : Type*} [Fintype P] [Fintype H]
    [DecidableEq P] [DecidableEq H] [MeasurableSpace Ω]
    (μ : Measure Ω) (t scalarC C : ℝ) (s : State P) (S cols : Finset P)
    (B : Matrix P H ℝ) (ξ : P → Ω → ℝ) : Prop where
  J_mean : ‖∑ x ∈ S, ∫ ω, Jinc t s x (ξ x ω) ∂μ‖ ≤ C * power t beta
  J_squares : ∀ z : P → ℝ, (∀ x ∈ S, |z x| ≤ scalarC * Real.sqrt t) →
    (∑ x ∈ S, Jinc t s x (z x) * (Jinc t s x (z x))ᴴ) ≤
      (C * power t (delta / 2)) • (1 : CMat P) ∧
    (∑ x ∈ S, (Jinc t s x (z x))ᴴ * Jinc t s x (z x)) ≤
      (C * power t (delta / 2)) • (1 : CMat P)
  J_jump : ∀ x ∈ S, ∀ z, |z| ≤ scalarC * Real.sqrt t → ‖Jinc t s x z‖ ≤ C * power t (delta / 4)
  L_mean : ‖∑ x ∈ S, ∫ ω, pullback B (Linc t s x (ξ x ω)) ∂μ‖ ≤ C * power t beta
  L_square : ∀ z : P → ℝ, (∀ x ∈ S, |z x| ≤ scalarC * Real.sqrt t) →
    (∑ x ∈ S, (pullback B (Linc t s x (z x)))^2) ≤
      (C * power t (delta / 2)) • (1 : RMat H)
  L_jump : ∀ x ∈ S, ∀ z, |z| ≤ scalarC * Real.sqrt t →
    ‖pullback B (Linc t s x z)‖ ≤ C * power t (delta / 4)
  lag_mean : ∀ i, ‖∑ x ∈ S, ∫ ω, lagInc t s x (ξ x ω) i ∂μ‖ ≤
    C * (logFactor t * (power t (2 * beta) + Real.sqrt t) +
      logFactor t^2 * power t (delta / 2))
  lag_square : ∀ z : P → ℝ, (∀ x ∈ S, |z x| ≤ scalarC * Real.sqrt t) → ∀ i,
    (∑ x ∈ S, ‖lagInc t s x (z x) i‖^2) ≤ C * logFactor t^2 * power t delta
  lag_jump : ∀ x ∈ S, ∀ z, |z| ≤ scalarC * Real.sqrt t → ∀ i,
    ‖lagInc t s x z i‖ ≤ C * logFactor t * power t (delta / 2)
  row_mean : ∀ i, |∑ x ∈ S, ∫ ω, fourthProxy t s cols i x (ξ x ω) / rowCap t ∂μ| ≤ C * power t kappa
  row_square : ∀ z : P → ℝ, (∀ x ∈ S, |z x| ≤ scalarC * Real.sqrt t) → ∀ i,
    (∑ x ∈ S, |fourthProxy t s cols i x (z x) / rowCap t|^2) ≤ C * power t kappa
  row_jump : ∀ x ∈ S, ∀ z, |z| ≤ scalarC * Real.sqrt t → ∀ i,
    |fourthProxy t s cols i x z / rowCap t| ≤ C * power t (kappa / 2)




def embedCharge {P P0 : Type*} [Fintype P] [DecidableEq P0]
    (e : P ↪ P0) (y : P → ℝ) : P0 → ℝ :=
  fun i => ∑ j, if e j = i then y j else 0










def continueIndicator {Ω : Type*} (ok : ℕ → Ω → Prop) (k : ℕ) (ω : Ω) : ℝ :=
  by classical exact if ∀ j ≤ k, ok j ω then 1 else 0

def firstFailure (M : ℕ) (ok : ℕ → Prop) : ℕ :=
  by classical exact if h : ∃ k : ℕ, k ≤ M ∧ ¬ ok k then Nat.find h else M + 1





structure UniformSlotLaw {Ω I : Type*} [mΩ : MeasurableSpace Ω]
    [Fintype I] [DecidableEq I] (μ : Measure Ω) (ℱ : Filtration ℕ mΩ)
    (M : ℕ) (t C : ℝ) (run : ℕ → Ω → Bool)
    (remaining : ℕ → Ω → Finset I) (slot : ℕ → Ω → I) (ξ : ℕ → Ω → ℝ) : Prop where
  run_predictable : ∀ k < M, @Measurable Ω Bool (ℱ k) ⊤ (run k)
  remaining_measurable : ∀ k < M, @Measurable Ω (Finset I) (ℱ k) ⊤ (remaining k)
  slot_adapted : ∀ k < M, @Measurable Ω I (ℱ (k + 1)) ⊤ (slot k)
  scalar_adapted : ∀ k < M, @Measurable Ω ℝ (ℱ (k + 1)) _ (ξ k)
  nonempty : ∀ k < M, ∀ ω, run k ω = true → (remaining k ω).Nonempty
  bounded : ∀ k < M, ∀ᵐ ω ∂μ, run k ω = true → |ξ k ω| ≤ C * Real.sqrt t
  uniform : ∀ k < M, ∀ i,
    μ[(fun ω => if run k ω = true ∧ slot k ω = i then (1 : ℝ) else 0) | ℱ k] =ᵐ[μ]
      fun ω => if run k ω = true ∧ i ∈ remaining k ω then 1 / (remaining k ω).card else 0
  mean : ∀ k < M, ∀ i,
    μ[(fun ω => if run k ω = true ∧ slot k ω = i then ξ k ω else 0) | ℱ k] =ᵐ[μ] 0
  variance : ∀ k < M, ∀ i,
    μ[(fun ω => if run k ω = true ∧ slot k ω = i then ξ k ω^2 else 0) | ℱ k] =ᵐ[μ]
      fun ω => if run k ω = true ∧ i ∈ remaining k ω then t / (remaining k ω).card else 0


structure OrderedRawBounds {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (s M : ℕ) (t C : ℝ) where
  kind : Fin s → MonitorKind
  dimension : Fin s → ℕ
  raw : ∀ i, ℕ → Ω → CMat (Fin (dimension i))
  adapted : ∀ i, StronglyAdapted ℱ (raw i)
  measurable : ∀ i k, AEStronglyMeasurable (raw i k) μ
  hermitian : ∀ i k, ∀ᵐ ω ∂μ, (raw i (k + 1) ω).IsHermitian
  finite_horizon : ∀ i k, M ≤ k → ∀ ω, raw i (k + 1) ω = 0
  jump : ∀ i k, ∀ᵐ ω ∂μ, ‖raw i (k + 1) ω‖ ≤ C * monitorJump t (kind i)
  mean : ∀ i k, k < M → ∀ᵐ ω ∂μ,
    ‖μ[raw i (k + 1) | ℱ k] ω‖ ≤
      C * monitorBias t (kind i) / logFactor t / (M - k : ℕ)
  square : ∀ i k, k < M → ∀ᵐ ω ∂μ,
    μ[(fun ω => (raw i (k + 1) ω)^2) | ℱ k] ω ≤
      (C * monitorVariance t (kind i) / logFactor t / (M - k : ℕ)) •
        (1 : CMat (Fin (dimension i)))





end AndersonAC.S45
