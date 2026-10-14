import AndersonAC.GT.Power
import AndersonAC.GT.ExpLimit

/-!
Finite-dimensional Golden–Thompson, as used in Lemma 5.6 of
`refs/tex/05-local-sweeps.tex:708–712`. The proof takes limits in Dyson's
power inequality, using the elementary matrix exponential limits.
-/

open Matrix Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace AndersonAC.MuseGT

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The first-order product approximation converges to the exponential of the sum. -/
theorem product_pow_tendsto_exp (A B : Matrix n n ℂ) [Nonempty n] :
    Tendsto (fun m : ℕ => ((1 + (m : ℂ)⁻¹ • A) * (1 + (m : ℂ)⁻¹ • B)) ^ m)
      atTop (nhds (exp (A + B))) := by
  have hR : Tendsto
      (fun m : ℕ => (m : ℝ) • ‖((m : ℂ)⁻¹ ^ 2) • (A * B)‖)
      atTop (nhds 0) := by
    refine (tendsto_const_div_atTop_nhds_zero_nat ‖A * B‖).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [smul_eq_mul, norm_smul, norm_pow, norm_nat_inv]
    field_simp
  have h := perturbed_pow_tendsto_exp (A + B)
    (fun m => ((m : ℂ)⁻¹ ^ 2) • (A * B)) hR
  convert h using 1
  funext m
  congr 1
  simp only [mul_add, add_mul, mul_one, one_mul, smul_add,
    smul_mul_assoc, mul_smul_comm, smul_smul, pow_two]
  abel

/-- Golden–Thompson for arbitrary finite Hermitian complex matrices. -/
theorem goldenThompson (A B : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace (exp (A + B))).re ≤ (Matrix.trace (exp A * exp B)).re := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn =>
    let := hn
    simp [Matrix.trace]
  | inr hn =>
    let := hn
    have ht : Tendsto (fun k : ℕ => 2 ^ (k + 1)) atTop atTop := by
      refine tendsto_atTop.mpr fun b => ?_
      filter_upwards [eventually_ge_atTop b] with k hk
      have hpow : ∀ j : ℕ, j + 1 ≤ 2 ^ (j + 1) := by
        intro j
        induction j with
        | zero => decide
        | succ k ih =>
          rw [pow_succ]
          omega
      exact hk.trans (Nat.le_succ k |>.trans (hpow k))
    have hleft := (product_pow_tendsto_exp A B).comp ht
    have hright := ((one_add_div_pow_tendsto_exp A).mul
      (one_add_div_pow_tendsto_exp B)).comp ht
    have htrace : Continuous (Matrix.trace : Matrix n n ℂ → ℂ) :=
      continuous_id.matrix_trace
    have hln := (htrace.tendsto _ |>.comp hleft).norm
    have hrr := Complex.continuous_re.tendsto _ |>.comp (htrace.tendsto _ |>.comp hright)
    have hbound : ‖Matrix.trace (exp (A + B))‖ ≤
        (Matrix.trace (exp A * exp B)).re := by
      refine le_of_tendsto_of_tendsto hln hrr (Eventually.of_forall fun k => ?_)
      apply dyson_pow_bound _ _ _ _ k
      · exact isHermitian_one.add (hA.smul (by simp [isSelfAdjoint_iff]))
      · exact isHermitian_one.add (hB.smul (by simp [isSelfAdjoint_iff]))
    exact (Complex.re_le_norm _).trans hbound

#print axioms goldenThompson

end AndersonAC.MuseGT
