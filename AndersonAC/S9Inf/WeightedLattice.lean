import AndersonAC.S9Inf.DiagonalL2
import AndersonAC.S9Inf.WeightedGreen

/-! The weighted hopping error; real diagonal potentials cancel exactly. -/

noncomputable section

open OAI.Anderson

namespace AndersonAC.SolS9Inf

def WeightRatioBound {d : ℕ} (w : Site d → ℝ) (b : ℝ) : Prop :=
  ∀ (x : Site d) (j : Fin d),
    |w x / w (x + basisVector j) - 1| ≤ b ∧
    |w x / w (x - basisVector j) - 1| ≤ b

def latticeDefect {d : ℕ} (w : Site d → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hr : WeightRatioBound w b) : StateSpace d →L[ℂ] StateSpace d :=
  ∑ j : Fin d, (
    (diagonalRealL2 (fun x => w x / w (x + basisVector j) - 1) b hb
      (fun x => (hr x j).1)) * shift (basisVector j) +
    (diagonalRealL2 (fun x => w x / w (x - basisVector j) - 1) b hb
      (fun x => (hr x j).2)) * shift (-basisVector j))

theorem norm_latticeDefect_le {d : ℕ} (w : Site d → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hr : WeightRatioBound w b) : ‖latticeDefect w b hb hr‖ ≤ 2 * (d : ℝ) * b := by
  calc
    _ ≤ ∑ j : Fin d, ‖(diagonalRealL2
      (fun x => w x / w (x + basisVector j) - 1) b hb (fun x => (hr x j).1)) *
        shift (basisVector j) +
      (diagonalRealL2 (fun x => w x / w (x - basisVector j) - 1) b hb
        (fun x => (hr x j).2)) * shift (-basisVector j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin d, (b + b) := by
      apply Finset.sum_le_sum
      intro j _
      apply (norm_add_le _ _).trans
      apply add_le_add
      · exact (norm_mul_le _ _).trans (by
          calc
            _ ≤ b * 1 := mul_le_mul (norm_diagonalRealL2_le _ b hb _)
              (norm_shift_le_one _) (norm_nonneg _) hb
            _ = b := mul_one b)
      · exact (norm_mul_le _ _).trans (by
          calc
            _ ≤ b * 1 := mul_le_mul (norm_diagonalRealL2_le _ b hb _)
              (norm_shift_le_one _) (norm_nonneg _) hb
            _ = b := mul_one b)
    _ = 2 * (d : ℝ) * b := by simp <;> ring

theorem latticeDefect_apply {d : ℕ} (w : Site d → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hr : WeightRatioBound w b) (v : StateSpace d) (x : Site d) :
    latticeDefect w b hb hr v x =
      ∑ j : Fin d, (
        ((w x / w (x + basisVector j) - 1 : ℝ) : ℂ) * v (x + basisVector j) +
        ((w x / w (x - basisVector j) - 1 : ℝ) : ℂ) * v (x - basisVector j)) := by
  simp only [latticeDefect, ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.mul_apply, lp.coeFn_sum, lp.coeFn_add,
    Finset.sum_apply, Pi.add_apply, diagonalRealL2_apply, shift_apply, sub_eq_add_neg]

theorem lattice_weighted_equation {d : ℕ} (coupling : ℝ) (ω : Configuration d)
    (z : ℂ) (w : Site d → ℝ) (M b : ℝ) (hM : 0 ≤ M)
    (hw : ∀ x, |w x| ≤ M) (hp : ∀ x, 0 < w x) (hb : 0 ≤ b)
    (hr : WeightRatioBound w b) (v : StateSpace d) :
    (hamiltonian coupling ω - z • (1 : StateSpace d →L[ℂ] StateSpace d))
        (diagonalRealL2 w M hM hw v) =
      diagonalRealL2 w M hM hw
        ((hamiltonian coupling ω - z • (1 : StateSpace d →L[ℂ] StateSpace d)) v) +
      latticeDefect w b hb hr (diagonalRealL2 w M hM hw v) := by
  apply lp.ext
  funext x
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, lp.coeFn_sub, lp.coeFn_smul, lp.coeFn_add,
    Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    diagonalRealL2_apply, hamiltonian_apply, latticeDefect_apply]
  have hterm (u : Site d) :
      ((w x / w u - 1 : ℝ) : ℂ) * ((w u : ℂ) * v u) =
        ((w x : ℂ) - (w u : ℂ)) * v u := by
    have hu : (w u : ℂ) ≠ 0 := by exact_mod_cast (hp u).ne'
    push_cast
    field_simp [hu] <;> ring
  simp_rw [hterm]
  simp only [mul_sub, sub_mul, mul_neg, mul_add, Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  ring

end AndersonAC.SolS9Inf
