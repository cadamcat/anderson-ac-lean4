import AndersonAC.AgentS78.Construction.TileCoverStatement

/-!
# WP10 construction: the §5 tile covers — frozen sub-statements

agent-s78cover (2026-10-14). The analytic inputs of `TileCoverStatement`
(TileCoverStatement.lean) that do not depend on the tiling. Each is a closed `Prop`; helper
lanes prove `theorem <name>_proof : <Statement>` in their own files.

* `GridPoincareStatement`: the Poincaré inequality on the grid box `Fin d → Fin K`
  (05:285–291 "cube Poincaré inequality"), with nearest-neighbour edges and no wrap-around.
* `TorusMetricStatement`: the torus graph distance is the circular `ℓ¹` distance.
* `TorusShellStatement`: the exponential shell sums of the torus distance
  (`S45.ShellBounds.count/second` on the sites), uniformly in `m`.
* `TorusKernelStatement`: the kernel energy of a potential (`S45.TileCover.kernel_energy`,
  potential part): `Σ_{x,y} e^{-u dist(x,y)} (v_x - v_y)² ≤ C u^{-d-2} Λ(v)`.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- Nearest-neighbour energy of the grid box `Fin d → Fin K` (no wrap-around): each edge
`{w, w + e_i}` with `w_i + 1 < K` counted once. -/
def gridEnergy {d K : ℕ} (f : (Fin d → Fin K) → ℝ) : ℝ :=
  ∑ w, ∑ i : Fin d,
    if h : (w i).val + 1 < K then (f (Function.update w i ⟨(w i).val + 1, h⟩) - f w) ^ 2 else 0

/-- **Grid Poincaré inequality.** -/
def GridPoincareStatement : Prop :=
  ∀ (d K : ℕ) (f : (Fin d → Fin K) → ℝ),
    ∑ w, (f w - (∑ w', f w') / (K : ℝ) ^ d) ^ 2 ≤ (d : ℝ) * (K : ℝ) ^ 2 * gridEnergy f

/-- Circular distance of a residue to `0` in `ZMod (sideLength m)`. -/
def circDist (m : ℕ) (a : ZMod (OAI.Anderson.sideLength m)) : ℕ :=
  min a.val (OAI.Anderson.sideLength m - a.val)

/-- Circular `ℓ¹` distance on the torus. -/
def l1Dist {d m : ℕ} (x y : Torus d m) : ℕ := ∑ k, circDist m (y k - x k)

/-- **The torus graph is connected** (every `m`; for `m = 0` the torus is one site). -/
def TorusConnectedStatement : Prop := ∀ d m : ℕ, (nnGraph d m).Connected

/-- **The torus graph distance is the circular `ℓ¹` distance.** -/
def TorusMetricStatement : Prop :=
  ∀ (d m : ℕ) (x y : Torus d m), physicalDistance d m x y = (l1Dist x y : ℝ)

/-- **Shell sums of the torus distance**, uniform in the torus size. -/
def TorusShellStatement (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (u : ℝ), 0 < u → u ≤ 1 → ∀ x : Torus d m,
    (∑ y, Real.exp (-u * physicalDistance d m x y)) ≤ C * S45.power u (-(d : ℝ)) ∧
    (∑ y, physicalDistance d m x y ^ 2 * Real.exp (-u * physicalDistance d m x y)) ≤
      C * S45.power u (-(d : ℝ) - 2)

/-- **Kernel energy of a potential**, uniform in the torus size. -/
def TorusKernelStatement (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (u : ℝ), 0 < u → u ≤ 1 → ∀ v : Torus d m → ℝ,
    (∑ x, ∑ y, Real.exp (-u * physicalDistance d m x y) * (v x - v y) ^ 2) ≤
      C * S45.power u (-(d : ℝ) - 2) * torusEnergy d m v

end AndersonAC.AgentS78
