import AndersonAC.S78.AssemblyEstimates

/-! Exact analytic subcontracts for the committed assembly. They are
propositions to prove; none is asserted as an axiom. -/
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78
open AndersonAC.S78

def assemblyNearSites {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin k) : Finset (Torus d m) :=
  cube d m (I.anchor a) (100 * I.Ds) ∩ (I.state a.succ).active

def assemblyLocalSplit {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin k) (α v : Torus d m → ℝ) : ℝ :=
  (∑ i ∈ cube d m (I.anchor a) (200 * I.Ds) ∩ (I.state 0).active, (α i) ^ 2) +
    b⁻¹ * cubeGradient d m (cube d m (I.anchor a) (200 * I.Ds)) v

def assemblyGlobalSplit {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (α v : Torus d m → ℝ) : ℝ :=
  (∑ i ∈ (I.state 0).active, (α i) ^ 2) + b⁻¹ * gradientEnergy (nnGraph d m) v

def assemblyNearChange {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin k) (f : Torus d m → ℝ) : ℝ :=
  wardEnergy (assemblyNearSites I a) (fun i => (r i).im)
    (normalizedInverse (I.state a.succ) t) f -
  wardEnergy (assemblyNearSites I a) (fun i => (r i).im)
    (normalizedInverse (I.state a.castSucc) t) f

def assemblySurvivorTail {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin k) (f : Torus d m → ℝ) : ℝ :=
  endpointEnergy (I.state a.succ) r t f -
    wardEnergy (I.state a.succ).active (fun i => (r i).im)
      (normalizedInverse (I.state a.castSucc) t) f - assemblyNearChange I a f

def assemblyBridge {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin k) (f : Torus d m → ℝ) : ℝ :=
  schurEnergy (I.state a.succ).active (endpointEnergy (I.state a.castSucc) r t) f -
    wardEnergy (I.state a.succ).active (fun i => (r i).im)
      (normalizedInverse (I.state a.castSucc) t) f

/-- §7, (assembly-tail-form): sum the survivor tails using distinct anchors,
the global exponential energy estimate and uniform exponential absorption. -/
def AssemblySurvivorTailBounds : Prop :=
  AssemblyAnchorTailInput →
  ∀ (d : ℕ), 3 ≤ d → ∀ (C c P : ℝ), 1 ≤ C → 0 < c → 0 ≤ P →
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ (m k : ℕ) (t b : ℝ) (r : Torus d m → ℂ) (I : AssemblyInput d m k t b r),
      I.C = C → I.c = c → I.P = P → t < t₀ →
      ∀ (S : Finset (Fin k)) (f α v : Torus d m → ℝ),
      (∀ i ∈ (I.state 0).active, f i = α i + v i) →
      |∑ a ∈ S, assemblySurvivorTail I a f| ≤
        t ^ (0.2 * delta) * assemblyGlobalSplit I α v

/-- §7, (assembly-bridge-trial), (assembly-bridge-tail): the old Schur trial
is bounded using the fourth rows from AssemblyMatrixBounds, the Ward row-two
identity, LocalDeviationInput and the old resolvent's separate far decay. -/
def AssemblyBridgeBounds : Prop :=
  AssemblyMatrixBounds → LocalDeviationInput →
  ∀ (d : ℕ), 3 ≤ d → ∀ (C c P : ℝ), 1 ≤ C → 0 < c → 0 ≤ P →
    ∃ C' t₀ : ℝ, 0 < C' ∧ 0 < t₀ ∧
      ∀ (m k : ℕ) (t b : ℝ) (r : Torus d m → ℂ) (I : AssemblyInput d m k t b r),
      I.C = C → I.c = c → I.P = P → t < t₀ →
      ∀ (S : Finset (Fin k)) (f α v : Torus d m → ℝ),
      (∀ i ∈ (I.state 0).active, f i = α i + v i) →
      (∑ a ∈ S, assemblyBridge I a f) ≤
        C' * t ^ (0.27 * delta) * (∑ a ∈ S, assemblyLocalSplit I a α v) +
        t ^ (0.2 * delta) * assemblyGlobalSplit I α v

end AndersonAC.SolS78
