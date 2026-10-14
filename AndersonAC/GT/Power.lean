import AndersonAC.GT.Dyson

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! Dyson's Lemma 3 (power inequality) for Golden–Thompson:
`‖Tr(AB)^{2^{k+1}}‖ ≤ Tr(A^{2^{k+1}} B^{2^{k+1}})` for Hermitian `A B`.
Proved by induction from Lemma 2 (`dyson_word_bound`). -/

/-- Product of a constant-`false` word is a power. -/
lemma wProd_replicate_false (X : Matrix n n ℂ) (m : ℕ) :
    wProd X (List.replicate m false) = X ^ m := by
  induction m with
  | zero => simp [wProd_nil]
  | succ m ih =>
    have hrep : List.replicate (m + 1) false = false :: List.replicate m false :=
      List.replicate_succ
    rw [hrep, wProd_cons, ih]
    show X * X ^ m = X ^ (m + 1)
    exact (pow_succ' X m).symm

/-- Cyclic move inside trace-powers: `ABBA` to `AABB` form. -/
lemma trace_ABBA_eq (A B : Matrix n n ℂ) (m : ℕ) :
    Matrix.trace ((A * B * B * A) ^ m)
      = Matrix.trace ((A * ((A * B) * B)) ^ m) :=
  trace_pow_mul_comm _ _ _

/-- `ABBA`-power traces equal `A²B²`-power traces. -/
lemma trace_ABBA_eq_sq (A B : Matrix n n ℂ) (m : ℕ) :
    Matrix.trace ((A * B * B * A) ^ m)
      = Matrix.trace (((A ^ 2) * (B ^ 2)) ^ m) := by
  have s1 : Matrix.trace ((A * B * B * A) ^ m)
      = Matrix.trace ((A * ((A * B) * B)) ^ m) :=
    trace_ABBA_eq A B m
  have rbase : (A * ((A * B) * B) : Matrix n n ℂ) = (A ^ 2) * (B ^ 2) := by
    noncomm_ring
  rw [s1, rbase]

/-- Dyson's Lemma 3 (norm form). -/
theorem dyson_pow_bound (A B : Matrix n n ℂ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (k : ℕ) :
    ‖Matrix.trace ((A * B) ^ (2 ^ (k + 1)))‖
      ≤ (Matrix.trace ((A ^ (2 ^ (k + 1))) * (B ^ (2 ^ (k + 1))))).re := by
  revert A B hA hB
  induction k with
  | zero =>
    intro A B hA hB
    have e2 : (2 : ℕ) ^ (0 + 1) = 2 := by decide
    rw [e2]
    -- Lemma 2 with X = AB, all-false word of length 2
    have hL2 := dyson_word_bound (A * B) 1 ⟨[false, false], rfl⟩
    have eLHS : wProd (A * B) [false, false] = (A * B) ^ 2 := by
      have fF : wFactor (A * B) false = A * B := rfl
      rw [wProd_pair, fF, pow_two]
    have hAB : ((A * B))ᴴ = B * A := by
      have hAe : Aᴴ = A := hA
      have hBe : Bᴴ = B := hB
      rw [Matrix.conjTranspose_mul, hAe, hBe]
    have eRHS : Matrix.trace (((A * B) * ((A * B))ᴴ) ^ 1)
        = Matrix.trace ((A ^ 2) * (B ^ 2)) := by
      rw [hAB]
      have r : ((A * B) * (B * A) : Matrix n n ℂ) = A * B * B * A := by
        simp only [mul_assoc]
      rw [r]
      have e1 := trace_ABBA_eq_sq A B 1
      rw [e1, pow_one]
    rw [eLHS] at hL2
    rw [eRHS] at hL2
    -- hL2 : ‖Tr((AB)^2)‖ ≤ (Tr((A^2)*(B^2))).re. Goal matches up to .re placement.
    exact hL2
  | succ k ih =>
    intro A B hA hB
    have hAe : Aᴴ = A := hA
    have hBe : Bᴴ = B := hB
    have hA2 : (A ^ 2).IsHermitian := hA.pow 2
    have hB2 : (B ^ 2).IsHermitian := hB.pow 2
    have eexp : (2 : ℕ) ^ ((k + 1) + 1) = 2 * 2 ^ (k + 1) := pow_succ' _ _
    rw [eexp]
    have hL2 := dyson_word_bound (A * B) (2 ^ (k + 1))
      ⟨List.replicate (2 * 2 ^ (k + 1)) false, List.length_replicate⟩
    have eLHS : wProd (A * B) (List.replicate (2 * 2 ^ (k + 1)) false)
        = (A * B) ^ (2 * 2 ^ (k + 1)) :=
      wProd_replicate_false _ _
    rw [eLHS] at hL2
    have hAB : ((A * B))ᴴ = B * A := by
      rw [Matrix.conjTranspose_mul, hAe, hBe]
    have eRHS : Matrix.trace (((A * B) * ((A * B))ᴴ) ^ (2 ^ (k + 1)))
        = Matrix.trace (((A ^ 2) * (B ^ 2)) ^ (2 ^ (k + 1))) := by
      rw [hAB]
      have r : ((A * B) * (B * A) : Matrix n n ℂ) = A * B * B * A := by
        simp only [mul_assoc]
      rw [r]
      exact trace_ABBA_eq_sq A B _
    rw [eRHS] at hL2
    have hIH := ih (A ^ 2) (B ^ 2) hA2 hB2
    have eA : ((A ^ 2) ^ (2 ^ (k + 1)) : Matrix n n ℂ) = A ^ (2 * 2 ^ (k + 1)) :=
      (pow_mul _ _ _).symm
    have eB : ((B ^ 2) ^ (2 ^ (k + 1)) : Matrix n n ℂ) = B ^ (2 * 2 ^ (k + 1)) :=
      (pow_mul _ _ _).symm
    have eAB : (Matrix.trace (((A ^ 2) ^ (2 ^ (k + 1))) * ((B ^ 2) ^ (2 ^ (k + 1))))).re
        = (Matrix.trace ((A ^ (2 * 2 ^ (k + 1))) * (B ^ (2 * 2 ^ (k + 1))))).re := by
      rw [eA, eB]
    have s1 : ‖Matrix.trace ((A * B) ^ (2 * 2 ^ (k + 1)))‖
        ≤ (Matrix.trace (((A ^ 2) * (B ^ 2)) ^ (2 ^ (k + 1)))).re := hL2
    have s2 : (Matrix.trace (((A ^ 2) * (B ^ 2)) ^ (2 ^ (k + 1)))).re
        ≤ ‖Matrix.trace (((A ^ 2) * (B ^ 2)) ^ (2 ^ (k + 1)))‖ :=
      Complex.re_le_norm _
    have s3 : ‖Matrix.trace (((A ^ 2) * (B ^ 2)) ^ (2 ^ (k + 1)))‖
        ≤ (Matrix.trace (((A ^ 2) ^ (2 ^ (k + 1))) * ((B ^ 2) ^ (2 ^ (k + 1))))).re :=
      hIH
    have s4 : (Matrix.trace (((A ^ 2) ^ (2 ^ (k + 1))) * ((B ^ 2) ^ (2 ^ (k + 1))))).re
        = (Matrix.trace ((A ^ (2 * 2 ^ (k + 1))) * (B ^ (2 * 2 ^ (k + 1))))).re :=
      eAB
    exact le_trans (le_trans (le_trans s1 s2) s3) s4.le
