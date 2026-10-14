import OAI.MathematicalPhysics.Anderson.Certificates
import AndersonAC.Blueprint.Certificate
import Mathlib

/-! Section 2 definitions. This module has no theorem placeholders and can be
imported by proofs without bringing a placeholder proof into their dependencies. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal ComplexConjugate Matrix.Norms.L2Operator ComplexOrder

namespace AndersonAC.S2

abbrev Torus := OAI.Anderson.Torus
abbrev Configuration := OAI.Anderson.TorusConfiguration
abbrev torusLaw := OAI.Anderson.torusLaw
abbrev hamiltonian := @OAI.Anderson.periodicHamiltonian
abbrev diagonalOn := @OAI.Anderson.diagonalOn
abbrev energyWindow := OAI.Anderson.energyWindow

def coordinateRestriction {ι : Type*} (A : Set ι) (f : ι → ℂ) : A → ℂ := fun i => f i.val
def coordinateProjection {ι : Type*} (A : Set ι) (f : ι → ℂ) : ι → ℂ := by
  classical
  exact fun i => if i ∈ A then f i else 0

/- Scales, including the exact floor used in (2.1). All division is in ℝ. -/
def initialScale (coupling : ℝ) : ℕ := Nat.floor (Real.log (3 / coupling ^ 2) / Real.log 4)
def scaleU (coupling : ℝ) : ℝ := coupling ^ 2 / 3 * (4 : ℝ) ^ initialScale coupling
def varianceScale (coupling : ℝ) (n : ℕ) : ℝ := scaleU coupling / (4 : ℝ) ^ n
def finalHeight (coupling : ℝ) (m : ℕ) : ℝ := varianceScale coupling m
def dampingScale (coupling : ℝ) (m n : ℕ) : ℝ := varianceScale coupling n + finalHeight coupling m






/- Proposition 2.1. The natural k combines C=k and c=1/k; the OAI
event bounds Im r above as a consequence of the norm bound. -/
abbrev certificateEvent := OAI.Anderson.certificateEvent

def UniformCertificateLimit (d k n₀ : ℕ) (u e₂ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 4 * n₀ ≤ m →
    ∀ E : ℝ, E ∈ energyWindow d e₂ →
      1 - ε ≤ (torusLaw d m (certificateEvent d k n₀ m u E)).toReal

def UniformSmallFailure (d k : ℕ) (e₂ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ nMin : ℕ, ∀ n₀ : ℕ, nMin ≤ n₀ →
    ∀ m : ℕ, 4 * n₀ ≤ m → ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      ∀ E : ℝ, E ∈ energyWindow d e₂ →
        1 - ε ≤ (torusLaw d m (certificateEvent d k n₀ m u E)).toReal

def FiniteCertificateTarget (d : ℕ) (e₂ : ℝ) : Prop :=
  ∃ k : ℕ, 10 ≤ k ∧
    (∀ n₀ : ℕ, k ≤ n₀ → ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      UniformCertificateLimit d k n₀ u e₂) ∧ UniformSmallFailure d k e₂

/- The architect's frozen interfaces are imported from main. -/
abbrev windowThreshold := AndersonAC.Blueprint.windowThreshold
abbrev CertificateFamily := AndersonAC.Blueprint.CertificateFamily

def AuxiliaryLaw : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)

instance AuxiliaryLaw_isProbabilityMeasure : IsProbabilityMeasure AuxiliaryLaw := by
  unfold AuxiliaryLaw
  infer_instance

def enlargedLaw (d m : ℕ) : Measure (Configuration d m × (ℕ → Bool)) :=
  (torusLaw d m).prod AuxiliaryLaw

instance enlargedLaw_isProbabilityMeasure (d m : ℕ) : IsProbabilityMeasure (enlargedLaw d m) := by
  unfold enlargedLaw
  infer_instance




/- Binary representation. Index k in Lean is digit k+1 in the paper. -/
def signValue (a : Bool) : ℝ := if a then 1 else -1
def binaryValue (coupling : ℝ) (a : ℕ → Bool) : ℝ :=
  ∑' k : ℕ, coupling / (2 : ℝ) ^ (k + 1) * signValue (a k)
def binaryPrefix (coupling : ℝ) (h : ℕ) (a : ℕ → Bool) : ℝ :=
  ∑ k ∈ Finset.range h, coupling / (2 : ℝ) ^ (k + 1) * signValue (a k)
def binarySuffix (coupling : ℝ) (h : ℕ) (a : ℕ → Bool) : ℝ :=
  ∑' k : ℕ, coupling / (2 : ℝ) ^ (h + k + 1) * signValue (a (h + k))
def uniformInterval (a : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (2 * a))⁻¹ • volume.restrict (Set.Icc (-a) a)











/- Exact query model: product signs and independent uniformly random orders. -/
section Queries
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

abbrev SignIndex := (ι × ℕ) ⊕ ℕ
abbrev Order (M : ℕ) := Equiv.Perm (Fin M)
instance orderMeasurableSpace (M : ℕ) : MeasurableSpace (Order M) := ⊤
abbrev RandomSources (M : ℕ → ℕ) :=
  (SignIndex ι → Bool) × ((o : ℕ) → Order (M o))

def signsLaw : Measure (SignIndex ι → Bool) :=
  Measure.infinitePi (fun _ : SignIndex ι => (PMF.uniformOfFintype Bool).toMeasure)
instance signsLaw_isProbabilityMeasure : IsProbabilityMeasure (signsLaw ι) := by
  unfold signsLaw
  infer_instance
def ordersLaw (M : ℕ → ℕ) : Measure ((o : ℕ) → Order (M o)) :=
  Measure.infinitePi (fun o : ℕ => (PMF.uniformOfFintype (Order (M o))).toMeasure)
instance ordersLaw_isProbabilityMeasure (M : ℕ → ℕ) : IsProbabilityMeasure (ordersLaw M) := by
  unfold ordersLaw
  infer_instance
def sourcesLaw (M : ℕ → ℕ) : Measure (RandomSources ι M) :=
  (signsLaw ι).prod (ordersLaw M)
instance sourcesLaw_isProbabilityMeasure (M : ℕ → ℕ) : IsProbabilityMeasure (sourcesLaw ι M) := by
  unfold sourcesLaw
  infer_instance


inductive Query where
  | trueDigit : ι → ℕ → Query
  | auxiliary : ℕ → Query
  | trueSuffix : ι → ℕ → Query
  | nextOrder : ℕ → Query
  | decision : Query
  deriving DecidableEq
instance queryMeasurableSpace : MeasurableSpace (Query ι) := ⊤

def querySigns (c : Query ι) : Set (SignIndex ι) :=
  match c with
  | .trueDigit i k => {Sum.inl (i, k)}
  | .auxiliary k => {Sum.inr k}
  | .trueSuffix i h => {x | ∃ k, h ≤ k ∧ x = Sum.inl (i, k)}
  | _ => ∅

def queriedSigns {M : ℕ → ℕ} (Q : ℕ → RandomSources ι M → Query ι)
    (q : ℕ) (ω : RandomSources ι M) : Set (SignIndex ι) :=
  ⋃ j ∈ Finset.range q, querySigns ι (Q j ω)

def orderCount {M : ℕ → ℕ} (Q : ℕ → RandomSources ι M → Query ι)
    (q : ℕ) (ω : RandomSources ι M) (o : ℕ) : ℕ :=
  (Finset.range q).filter (fun j => Q j ω = Query.nextOrder o) |>.card

abbrev Answer := (SignIndex ι → Option Bool) × Option ℕ

instance optionBoolMeasurableSpace : MeasurableSpace (Option Bool) := ⊤
instance optionNatMeasurableSpace : MeasurableSpace (Option ℕ) := ⊤

def answer {M : ℕ → ℕ} (Q : ℕ → RandomSources ι M → Query ι)
    (q : ℕ) (ω : RandomSources ι M) : Answer ι := by
  classical
  exact (fun x => if x ∈ querySigns ι (Q q ω) then some (ω.1 x) else none,
    match Q q ω with
    | .nextOrder o => if h : orderCount ι Q q ω o < M o then
        some ((ω.2 o ⟨orderCount ι Q q ω o, h⟩).val) else none
    | _ => none)

def retained {M : ℕ → ℕ} (Q : ℕ → RandomSources ι M → Query ι) :
    ℕ → MeasurableSpace (RandomSources ι M)
  | 0 => ⊥
  | q + 1 => retained Q q ⊔ MeasurableSpace.comap
      (fun ω => (Q q ω, answer ι Q q ω)) inferInstance

def ObeysQueryRules {M : ℕ → ℕ} (Q : ℕ → RandomSources ι M → Query ι) : Prop :=
  (∀ q, @Measurable _ _ (retained ι Q q) inferInstance (Q q)) ∧
  (∀ q ω k, Q q ω = .auxiliary k → Sum.inr k ∉ queriedSigns ι Q q ω) ∧
  (∀ q ω o, Q q ω = .nextOrder o → orderCount ι Q q ω o < M o)

def signsUnqueried {M : ℕ → ℕ} (Q : ℕ → RandomSources ι M → Query ι)
    (q : ℕ) (s : Finset (SignIndex ι)) : Set (RandomSources ι M) :=
  {ω | ∀ x ∈ s, x ∉ queriedSigns ι Q q ω}

def signCylinder {M : ℕ → ℕ} (s : Finset (SignIndex ι))
    (a : SignIndex ι → Bool) : Set (RandomSources ι M) := {ω | ∀ x ∈ s, ω.1 x = a x}
def orderCylinder {M : ℕ → ℕ} (O : Finset ℕ) (b : (o : ℕ) → Order (M o)) :
    Set (RandomSources ι M) := {ω | ∀ o ∈ O, ω.2 o = b o}

def completionWeight {M : ℕ → ℕ} (Q : ℕ → RandomSources ι M → Query ι)
    (q : ℕ) (O : Finset ℕ) (b : (o : ℕ) → Order (M o))
    (ω : RandomSources ι M) : ℝ := by
  classical
  exact ∏ o ∈ O, if (∀ j : Fin (M o), j.val < orderCount ι Q q ω o →
    b o j = ω.2 o j) then ((M o - orderCount ι Q q ω o).factorial : ℝ)⁻¹ else 0

/- This finite-cylinder identity states the full joint conditional product law;
the order weight is random and measurable in the retained history. -/
def FreshAt {M : ℕ → ℕ} (Q : ℕ → RandomSources ι M → Query ι)
    (q : ℕ) : Prop :=
  ∀ (D : Set (RandomSources ι M)), MeasurableSet[retained ι Q q] D →
    ∀ (s : Finset (SignIndex ι)) (a : SignIndex ι → Bool)
      (O : Finset ℕ) (b : (o : ℕ) → Order (M o)),
    (sourcesLaw ι M (D ∩ signsUnqueried ι Q q s ∩ signCylinder ι s a ∩
      orderCylinder ι O b)).toReal =
      (2 : ℝ) ^ (-(s.card : ℤ)) *
        ∫ ω in D ∩ signsUnqueried ι Q q s, completionWeight ι Q q O b ω ∂sourcesLaw ι M




/- Finite-valued stopping time version; no uniform deterministic bound on τ. -/
def IsRetainedStoppingTime {M : ℕ → ℕ} (Q : ℕ → RandomSources ι M → Query ι)
    (τ : RandomSources ι M → ℕ) : Prop :=
  ∀ q, MeasurableSet[retained ι Q q] {ω | τ ω ≤ q}

def stoppedRetained {M : ℕ → ℕ} (Q : ℕ → RandomSources ι M → Query ι)
    (τ : RandomSources ι M → ℕ) : MeasurableSpace (RandomSources ι M) :=
  ⨅ q : ℕ, ((retained ι Q q).comap (fun ω : {ω // τ ω = q} => ω.val)).map
    (fun ω : {ω // τ ω = q} => ω.val)



def suffixesUnqueried {M : ℕ → ℕ} (Q : ℕ → RandomSources ι M → Query ι)
    (q : ℕ) (sites : Finset ι) (h : ι → ℕ) : Set (RandomSources ι M) :=
  {ω | ∀ i ∈ sites, ∀ k, h i ≤ k → Sum.inl (i, k) ∉ queriedSigns ι Q q ω}




end Queries

/- Numerical records are distinct from retained histories. -/
section SiteStates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure SiteState (ι : Type*) [Fintype ι] [DecidableEq ι] where
  active : Finset ι
  terminal : Finset ι
  pending : Finset ι
  installed : ι → ℝ
  prefixLength : ι → ℕ
  damping : ι → ℂ
  partition : Disjoint active terminal ∧ active ∪ terminal = Finset.univ
  pending_active : pending ⊆ active

def initialState (damping : ι → ℂ) : SiteState ι where
  active := Finset.univ
  terminal := ∅
  pending := ∅
  installed := fun _ => 0
  prefixLength := fun _ => 0
  damping := damping
  partition := by simp
  pending_active := by simp

def coupled (s : SiteState ι) : Finset ι := s.active \ s.pending

def TrueStateInvariant (s : SiteState ι) (coupling : ℝ) (digits : ι → ℕ → Bool)
    (seen : Set (SignIndex ι)) : Prop :=
  (∀ i ∈ s.terminal, s.installed i = binaryValue coupling (digits i)) ∧
  (∀ i ∈ coupled s, s.installed i = binaryPrefix coupling (s.prefixLength i) (digits i) ∧
    ∀ k, s.prefixLength i ≤ k → Sum.inl (i, k) ∉ seen)

def RecordedStateInvariant (s : SiteState ι) (coupling : ℝ) (digits : ι → ℕ → Bool)
    (seen : Set (SignIndex ι)) : Prop :=
  TrueStateInvariant s coupling digits seen ∧
    (∀ i ∈ s.terminal, ∀ k, Sum.inl (i, k) ∈ seen) ∧
    ∀ i ∈ coupled s, ∀ k, k < s.prefixLength i → Sum.inl (i, k) ∈ seen

def CommittedTransition (before after : SiteState ι) : Prop :=
  before.terminal ⊆ after.terminal ∧
  (∀ i ∈ before.terminal, after.installed i = before.installed i) ∧
  before.pending ⊆ after.pending ∪ after.terminal

def FinalStateInvariant (s : SiteState ι) (coupling : ℝ) (digits : ι → ℕ → Bool) : Prop :=
  s.pending = ∅ ∧ (∀ i, s.installed i = binaryValue coupling (digits i)) ∧
    ∀ i ∈ s.active, 0 < (s.damping i).im

def rollback (before : SiteState ι) (mark : Finset ι) : SiteState ι where
  active := before.active
  terminal := before.terminal
  pending := before.pending ∪ (mark ∩ before.active)
  installed := before.installed
  prefixLength := before.prefixLength
  damping := before.damping
  partition := before.partition
  pending_active := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact before.pending_active hi
    · exact (Finset.mem_inter.mp hi).2


end SiteStates

/- Schur algebra and the Ward Laplacian. -/
section Matrices
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def realMatrix (M : Matrix ι ι ℝ) : Matrix ι ι ℂ := fun i j => M i j
def dampedMatrix (M : Matrix ι ι ℝ) (t : ℝ) (r : ι → ℂ) : Matrix ι ι ℂ :=
  realMatrix M - (t : ℂ) • Matrix.diagonal r
def resolvent (M : Matrix ι ι ℝ) (t : ℝ) (r : ι → ℂ) : Matrix ι ι ℂ :=
  (dampedMatrix M t r)⁻¹
def normalizedResolvent (M : Matrix ι ι ℝ) (t : ℝ) (r : ι → ℂ) : Matrix ι ι ℂ :=
  (Real.sqrt t : ℂ) • resolvent M t r
def squaredEntries (h : Matrix ι ι ℂ) : Matrix ι ι ℂ := fun i j => (h i j) ^ 2
def wardWeights (h : Matrix ι ι ℂ) : Matrix ι ι ℝ := fun i j => ‖h i j‖ ^ 2
def diagonalImaginary (g : Matrix ι ι ℂ) : ι → ℝ := fun i => (g i i).im
def hermitianImaginary (B : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (1 / (2 * Complex.I)) • (B - B.conjTranspose)
def wardLaplacian (p q : ι → ℝ) (F : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => p i * q i) - Matrix.diagonal p * F * Matrix.diagonal p
def squareNorm (f : ι → ℂ) : ℝ := ∑ i, ‖f i‖ ^ 2
def pairing (y f : ι → ℂ) : ℂ := ∑ i, conj (y i) * f i
def quadraticForm (B : Matrix ι ι ℂ) (f : ι → ℂ) : ℝ :=
  (pairing f (B.mulVec f)).re
def Neutral (y : ι → ℂ) : Prop := ∑ i, y i = 0
def constantProjection : Matrix ι ι ℂ := fun _ _ => (Fintype.card ι : ℂ)⁻¹
def laplacianPseudoInverse (D : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (D + constantProjection)⁻¹ - constantProjection
def ConstantKernel (D : Matrix ι ι ℂ) : Prop :=
  ∀ f : ι → ℂ, D.mulVec f = 0 ↔ ∃ c : ℂ, f = fun _ => c
def ConnectedLaplacian (D : Matrix ι ι ℂ) : Prop := D.PosSemidef ∧ ConstantKernel D

def schurOn (B : Matrix ι ι ℂ) (U : Finset ι) :
    Matrix {i // i ∉ U} {i // i ∉ U} ℂ := by
  classical
  exact B.submatrix Subtype.val Subtype.val -
    B.submatrix (fun i : {i // i ∉ U} => i.val) (fun i : {i // i ∈ U} => i.val) *
    (B.submatrix (fun i : {i // i ∈ U} => i.val) (fun i : {i // i ∈ U} => i.val))⁻¹ *
    B.submatrix (fun i : {i // i ∈ U} => i.val) (fun i : {i // i ∉ U} => i.val)

def extendSurvivors (U : Finset ι) (y : {i // i ∉ U} → ℂ) : ι → ℂ :=
  fun i => if hi : i ∉ U then y ⟨i, hi⟩ else 0























end Matrices

/- Stage invariants and port forms, whose propagation belongs to §§3–8. -/
def delta : ℝ := 1 / 100
def kappa : ℝ := (1 / 200) * delta
def nu (d : ℕ) : ℝ := (1 / 100000) * delta / (d : ℝ)
def fourthPowerCap (t : ℝ) : ℝ := Real.rpow t (1 + delta)
def spatialScale (coupling : ℝ) (m : ℕ) (t : ℝ) : ℝ := dampingScale coupling m (initialScale coupling) * t
def clearingLastStage (m : ℕ) : ℕ := m / 2

def torusLaplacian (d m : ℕ) : Matrix (Torus d m) (Torus d m) ℂ :=
  fun i j => (if i = j then (2 * (d : ℂ)) else 0) -
    ∑ k : Fin d, ((if j = i + OAI.Anderson.torusBasisVector k then (1 : ℂ) else 0) +
      (if j = i - OAI.Anderson.torusBasisVector k then (1 : ℂ) else 0))




section Bounds
variable {ι τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ]

def StageBounds (r : ι → ℂ) (h : Matrix ι ι ℂ) (D : Matrix ι ι ℂ)
    (Λ : Matrix τ τ ℂ) (site : ι → τ) (t b c C cₙ Cₙ C₀ : ℝ) : Prop :=
  (∀ i, ‖r i‖ ≤ C ∧ c ≤ (r i).im ∧ (r i).im ≤ C) ∧
  ‖squaredEntries h‖ ≤ (1 / 3 : ℝ) ∧
  (∀ i, (∑ j, ‖h i j‖ ^ 4) ≤ fourthPowerCap t) ∧ ConnectedLaplacian D ∧
  ∀ y : ι → ℂ, Neutral y →
    let ySum : τ → ℂ := fun j => ∑ i, if site i = j then y i else 0
    cₙ * b * quadraticForm (laplacianPseudoInverse Λ) ySum ≤
        quadraticForm (laplacianPseudoInverse D) y ∧
    quadraticForm (laplacianPseudoInverse D) y ≤
        C₀ * squareNorm y + Cₙ * b * quadraticForm (laplacianPseudoInverse Λ) ySum ∧
    quadraticForm (laplacianPseudoInverse D) y ≤
        (1 + Real.rpow t kappa) * (∑ i, ((r i).im)⁻¹ ^ 2 * ‖y i‖ ^ 2) +
          Cₙ * t * quadraticForm (laplacianPseudoInverse Λ) ySum

def portCharge (site : ι → τ) (y : ι → ℂ) : τ → ℂ :=
  fun j => ∑ i, if site i = j then y i else 0
def repeatAtPorts (site : ι → τ) (v : τ → ℂ) : ι → ℂ := fun i => v (site i)
def AtMostTwoPorts (site : ι → τ) : Prop :=
  ∀ j, (Finset.univ.filter (fun i => site i = j)).card ≤ 2
def dualPortForm (site : ι → τ) (Λ : Matrix τ τ ℂ) (b : ℝ) (y : ι → ℂ) : ℝ :=
  squareNorm y + b * quadraticForm (laplacianPseudoInverse Λ) (portCharge site y)
def primalPortForm (site : ι → τ) (Λ : Matrix τ τ ℂ) (b : ℝ) (f : ι → ℂ) : ℝ :=
  sInf (Set.range (fun v : τ → ℂ =>
    squareNorm (f - repeatAtPorts site v) + b⁻¹ * quadraticForm Λ v))


/- Lemma 3.1, referenced but not proved in §2. Hypothesis is an explicit
interface rather than an assumption that the port form is already dual. -/


end Bounds

/- Terminal path metric and the support statement used for decay. -/
def neighbors {d m : ℕ} (i j : Torus d m) : Prop :=
  ∃ k : Fin d, j = i + OAI.Anderson.torusBasisVector k ∨
    j = i - OAI.Anderson.torusBasisVector k

def pathCost {d m : ℕ} (T : Finset (Torus d m)) : List (Torus d m) → ℕ
  | i :: j :: rest => (if i ∈ T ∨ j ∈ T then 0 else 1) + pathCost T (j :: rest)
  | _ => 0

def terminalDistance {d m : ℕ} (T : Finset (Torus d m)) (i j : Torus d m) : ℕ :=
  sInf {n | ∃ path : List (Torus d m), path.head? = some i ∧ path.getLast? = some j ∧
    path.IsChain neighbors ∧ pathCost T path = n}

def torusDistance {d m : ℕ} (i j : Torus d m) : ℕ := terminalDistance ∅ i j
def GeometryBound {d m : ℕ} (T : Finset (Torus d m)) (t : ℝ) : Prop :=
  ∀ i j, (1 / 2 : ℝ) * (torusDistance i j : ℝ) - Real.rpow t (-(103 / 100 : ℝ)) ≤
    (terminalDistance T i j : ℝ)



end AndersonAC.S2
