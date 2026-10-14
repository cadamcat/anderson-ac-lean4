import AndersonAC.S9Inf.HelperStatements

/-! Exact leading coefficient of a power of the Anderson Hamiltonian. -/

noncomputable section

open OAI.Anderson

namespace AndersonAC.SolS9Inf

private def coefficient {d : ℕ} (coupling : ℝ) (ω : Configuration d)
    (x y : Site d) (n : ℕ) : ℂ :=
  ((hamiltonian coupling ω ^ n) (AndersonAC.Blueprint.delta y)) x

private lemma latticeDistance_triangle {d : ℕ} (x y z : Site d) :
    latticeDistance x z ≤ latticeDistance x y + latticeDistance y z := by
  unfold latticeDistance
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  calc
    Int.natAbs (x j - z j) = Int.natAbs ((x j - y j) + (y j - z j)) := by
      congr 2 <;> omega
    _ ≤ Int.natAbs (x j - y j) + Int.natAbs (y j - z j) := Int.natAbs_add_le _ _

private lemma latticeDistance_step {d : ℕ} (x : Site d) (j : Fin d) :
    latticeDistance x (x + basisVector j) = 1 := by
  classical
  have hdiff : (fun k : Fin d => x k - (x + basisVector j) k) =
      Pi.single j (-1 : ℤ) := by
    ext k
    by_cases hk : k = j
    · subst k
      simp [basisVector]
    · simp [basisVector, hk]
  unfold latticeDistance
  have hsum : (∑ k : Fin d, Int.natAbs ((Pi.single j (-1 : ℤ) : Site d) k)) =
      Int.natAbs (-1 : ℤ) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k hk hkj
      simp [Pi.single_apply, hkj]
    · simp
  calc
    (∑ k : Fin d, Int.natAbs (x k - (x + basisVector j) k)) =
        ∑ k : Fin d, Int.natAbs ((Pi.single j (-1 : ℤ) : Site d) k) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact congrArg Int.natAbs (congrFun hdiff k)
    _ = Int.natAbs (-1 : ℤ) := hsum
    _ = 1 := by norm_num

private lemma latticeDistance_sub_step {d : ℕ} (x : Site d) (j : Fin d) :
    latticeDistance x (x - basisVector j) = 1 := by
  classical
  have hdiff : (fun k : Fin d => x k - (x - basisVector j) k) =
      Pi.single j (1 : ℤ) := by
    ext k
    by_cases hk : k = j
    · subst k
      simp [basisVector]
    · simp [basisVector, hk]
  unfold latticeDistance
  have hsum : (∑ k : Fin d, Int.natAbs ((Pi.single j (1 : ℤ) : Site d) k)) =
      Int.natAbs (1 : ℤ) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k hk hkj
      simp [Pi.single_apply, hkj]
    · simp
  calc
    (∑ k : Fin d, Int.natAbs (x k - (x - basisVector j) k)) =
        ∑ k : Fin d, Int.natAbs ((Pi.single j (1 : ℤ) : Site d) k) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact congrArg Int.natAbs (congrFun hdiff k)
    _ = Int.natAbs (1 : ℤ) := hsum
    _ = 1 := by norm_num

private lemma natAbs_add_one_of_nonneg (a : ℤ) (ha : 0 ≤ a) :
    Int.natAbs (a + 1) = Int.natAbs a + 1 := by
  have hcast : (Int.natAbs (a + 1) : ℤ) = Int.natAbs a + 1 := by
    rw [Int.ofNat_natAbs_of_nonneg (by omega), Int.ofNat_natAbs_of_nonneg ha]
  exact_mod_cast hcast

private lemma natAbs_add_one_of_neg (a : ℤ) (ha : a < 0) :
    Int.natAbs (a + 1) + 1 = Int.natAbs a := by
  have hcast : (Int.natAbs (a + 1) : ℤ) + 1 = Int.natAbs a := by
    rw [Int.ofNat_natAbs_of_nonpos (by omega), Int.ofNat_natAbs_of_nonpos (by omega)]
    omega
  exact_mod_cast hcast

private lemma latticeDistance_update {d : ℕ} (x y : Site d) (j : Fin d) (t : ℤ) :
    latticeDistance (Function.update x j t) y + Int.natAbs (x j - y j) =
      latticeDistance x y + Int.natAbs (t - y j) := by
  classical
  unfold latticeDistance
  have hnew : (∑ k : Fin d, Int.natAbs (Function.update x j t k - y k)) =
      Int.natAbs (t - y j) +
        ∑ k ∈ Finset.univ.erase j, Int.natAbs (Function.update x j t k - y k) := by
    simpa using (Finset.add_sum_erase Finset.univ
      (fun k : Fin d => Int.natAbs (Function.update x j t k - y k))
      (Finset.mem_univ j)).symm
  have hold : (∑ k : Fin d, Int.natAbs (x k - y k)) =
      Int.natAbs (x j - y j) +
        ∑ k ∈ Finset.univ.erase j, Int.natAbs (x k - y k) := by
    exact (Finset.add_sum_erase Finset.univ
      (fun k : Fin d => Int.natAbs (x k - y k)) (Finset.mem_univ j)).symm
  rw [hnew, hold]
  have herase :
      (∑ k ∈ Finset.univ.erase j, Int.natAbs (Function.update x j t k - y k)) =
        ∑ k ∈ Finset.univ.erase j, Int.natAbs (x k - y k) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    simp [Function.update_of_ne hkj]
  rw [herase]
  omega

private lemma latticeDistance_add_basis_toward {d : ℕ} (x y : Site d) (j : Fin d)
    (hxy : x j < y j) :
    latticeDistance (x + basisVector j) y + 1 = latticeDistance x y := by
  have hv : x + basisVector j = Function.update x j (x j + 1) := by
    ext k
    by_cases hkj : k = j
    · subst k
      simp [basisVector]
    · simp [basisVector, hkj]
  have hdist := latticeDistance_update x y j (x j + 1)
  rw [hv]
  have habs := natAbs_add_one_of_neg (x j - y j) (by omega)
  omega

private lemma latticeDistance_add_basis_away {d : ℕ} (x y : Site d) (j : Fin d)
    (hxy : y j ≤ x j) :
    latticeDistance (x + basisVector j) y = latticeDistance x y + 1 := by
  have hv : x + basisVector j = Function.update x j (x j + 1) := by
    ext k
    by_cases hkj : k = j
    · subst k
      simp [basisVector]
    · simp [basisVector, hkj]
  have hdist := latticeDistance_update x y j (x j + 1)
  rw [hv]
  have habs := natAbs_add_one_of_nonneg (x j - y j) (by omega)
  omega

private lemma latticeDistance_sub_basis_toward {d : ℕ} (x y : Site d) (j : Fin d)
    (hyx : y j < x j) :
    latticeDistance (x - basisVector j) y + 1 = latticeDistance x y := by
  have hv : x - basisVector j = Function.update x j (x j - 1) := by
    ext k
    by_cases hkj : k = j
    · subst k
      simp [basisVector]
    · simp [basisVector, hkj]
  have hdist := latticeDistance_update x y j (x j - 1)
  rw [hv]
  have habs := natAbs_add_one_of_neg (y j - x j) (by omega)
  have hneg : Int.natAbs (x j - y j) = Int.natAbs (y j - x j) := by
    rw [show x j - y j = -(y j - x j) by omega, Int.natAbs_neg]
  have hnew : Int.natAbs (x j - 1 - y j) = Int.natAbs (y j - x j + 1) := by
    rw [show x j - 1 - y j = -(y j - x j + 1) by omega, Int.natAbs_neg]
  rw [hneg, hnew] at hdist
  omega

private lemma latticeDistance_sub_basis_away {d : ℕ} (x y : Site d) (j : Fin d)
    (hxy : x j ≤ y j) :
    latticeDistance (x - basisVector j) y = latticeDistance x y + 1 := by
  have hv : x - basisVector j = Function.update x j (x j - 1) := by
    ext k
    by_cases hkj : k = j
    · subst k
      simp [basisVector]
    · simp [basisVector, hkj]
  have hdist := latticeDistance_update x y j (x j - 1)
  rw [hv]
  have habs := natAbs_add_one_of_nonneg (y j - x j) (by omega)
  have hneg : Int.natAbs (x j - y j) = Int.natAbs (y j - x j) := by
    rw [show x j - y j = -(y j - x j) by omega, Int.natAbs_neg]
  have hnew : Int.natAbs (x j - 1 - y j) = Int.natAbs (y j - x j + 1) := by
    rw [show x j - 1 - y j = -(y j - x j + 1) by omega, Int.natAbs_neg]
  rw [hneg, hnew] at hdist
  omega

private lemma sum_update_sub_one {d : ℕ} (a : Fin d → ℕ) (j : Fin d)
    (ha : 0 < a j) :
    (∑ k : Fin d, Function.update a j (a j - 1) k) = (∑ k : Fin d, a k) - 1 := by
  classical
  have hnew : (∑ k : Fin d, Function.update a j (a j - 1) k) =
      (a j - 1) + ∑ k ∈ Finset.univ.erase j, a k := by
    calc
      (∑ k : Fin d, Function.update a j (a j - 1) k) =
          Function.update a j (a j - 1) j +
            ∑ k ∈ Finset.univ.erase j, Function.update a j (a j - 1) k :=
        (Finset.add_sum_erase Finset.univ
          (fun k : Fin d => Function.update a j (a j - 1) k) (Finset.mem_univ j)).symm
      _ = (a j - 1) + ∑ k ∈ Finset.univ.erase j, a k := by
        have herase :
            (∑ k ∈ Finset.univ.erase j, Function.update a j (a j - 1) k) =
              ∑ k ∈ Finset.univ.erase j, a k := by
          apply Finset.sum_congr rfl
          intro k hk
          simp [Function.update_of_ne (Finset.mem_erase.mp hk).1]
        rw [herase]
        simp
  have hold : (∑ k : Fin d, a k) = a j + ∑ k ∈ Finset.univ.erase j, a k :=
    (Finset.add_sum_erase Finset.univ (fun k : Fin d => a k)
      (Finset.mem_univ j)).symm
  rw [hnew, hold]
  omega

private lemma factorialProduct_update_sub_one {d : ℕ} (a : Fin d → ℕ) (j : Fin d)
    (ha : 0 < a j) :
    (∏ k : Fin d, Nat.factorial (a k)) =
      a j * (∏ k : Fin d, Nat.factorial (Function.update a j (a j - 1) k)) := by
  classical
  have hprod : (∏ k : Fin d, Nat.factorial (a k)) =
      Nat.factorial (a j) * ∏ k ∈ Finset.univ.erase j, Nat.factorial (a k) :=
    (Finset.mul_prod_erase Finset.univ (fun k : Fin d => Nat.factorial (a k))
      (Finset.mem_univ j)).symm
  have hprod' :
      (∏ k : Fin d, Nat.factorial (Function.update a j (a j - 1) k)) =
        Nat.factorial (a j - 1) * ∏ k ∈ Finset.univ.erase j, Nat.factorial (a k) := by
    calc
      (∏ k : Fin d, Nat.factorial (Function.update a j (a j - 1) k)) =
          Nat.factorial (Function.update a j (a j - 1) j) *
            ∏ k ∈ Finset.univ.erase j, Nat.factorial (Function.update a j (a j - 1) k) :=
        (Finset.mul_prod_erase Finset.univ
          (fun k : Fin d => Nat.factorial (Function.update a j (a j - 1) k))
          (Finset.mem_univ j)).symm
      _ = Nat.factorial (a j - 1) * ∏ k ∈ Finset.univ.erase j, Nat.factorial (a k) := by
        have herase :
            (∏ k ∈ Finset.univ.erase j, Nat.factorial (Function.update a j (a j - 1) k)) =
              ∏ k ∈ Finset.univ.erase j, Nat.factorial (a k) := by
          apply Finset.prod_congr rfl
          intro k hk
          simp [Function.update_of_ne (Finset.mem_erase.mp hk).1]
        rw [herase]
        simp
  have hfac : Nat.factorial (a j) = a j * Nat.factorial (a j - 1) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
    rw [hm]
    simp [Nat.factorial_succ]
  rw [hprod, hprod', hfac]
  ring

private lemma multinomial_recurrence {d : ℕ} (a : Fin d → ℕ)
    (hN : 0 < ∑ k : Fin d, a k) :
    (∑ j : Fin d, if 0 < a j then
      Nat.multinomial Finset.univ (Function.update a j (a j - 1)) else 0) =
      Nat.multinomial Finset.univ a := by
  classical
  let N := ∑ k : Fin d, a k
  let P := ∏ k : Fin d, Nat.factorial (a k)
  have hP : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos fun k hk => Nat.factorial_pos (a k)
  have hspec : P * Nat.multinomial Finset.univ a = Nat.factorial N := by
    simpa [P, N] using (Nat.multinomial_spec Finset.univ a)
  have hfactorial : N * Nat.factorial (N - 1) = Nat.factorial N := by
    have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hN)
    calc
      N * Nat.factorial (N - 1) = ((N - 1) + 1) * Nat.factorial (N - 1) := by
        rw [Nat.sub_add_cancel hNpos]
      _ = Nat.factorial ((N - 1) + 1) := by rw [Nat.factorial_succ]
      _ = Nat.factorial N := by rw [Nat.sub_add_cancel hNpos]
  have hterm : ∀ j : Fin d,
      P * (if 0 < a j then
        Nat.multinomial Finset.univ (Function.update a j (a j - 1)) else 0) =
        a j * Nat.factorial (N - 1) := by
    intro j
    by_cases ha : 0 < a j
    · have hsum := sum_update_sub_one a j ha
      have hprod := factorialProduct_update_sub_one a j ha
      have hspec' := Nat.multinomial_spec Finset.univ (Function.update a j (a j - 1))
      rw [hsum] at hspec'
      have hspec'' :
          (∏ k : Fin d, Nat.factorial (Function.update a j (a j - 1) k)) *
            Nat.multinomial Finset.univ (Function.update a j (a j - 1)) =
            Nat.factorial (N - 1) := by
        simpa [N] using hspec'
      rw [if_pos ha]
      calc
        P * Nat.multinomial Finset.univ (Function.update a j (a j - 1)) =
            a j * ((∏ k : Fin d, Nat.factorial (Function.update a j (a j - 1) k)) *
              Nat.multinomial Finset.univ (Function.update a j (a j - 1))) := by
                dsimp [P]
                rw [hprod]
                ring
        _ = a j * Nat.factorial (N - 1) := by rw [hspec'']
    · have hz : a j = 0 := by omega
      rw [if_neg ha, hz]
      simp
  apply Nat.mul_left_cancel hP
  calc
    P * (∑ j : Fin d, if 0 < a j then
        Nat.multinomial Finset.univ (Function.update a j (a j - 1)) else 0) =
        ∑ j : Fin d, a j * Nat.factorial (N - 1) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          exact hterm j
    _ = N * Nat.factorial (N - 1) := by
          rw [Finset.sum_mul]
    _ = Nat.factorial N := hfactorial
    _ = P * Nat.multinomial Finset.univ a := hspec.symm

private def displacementVector {d : ℕ} (x y : Site d) : Fin d → ℕ :=
  fun j => Int.natAbs (x j - y j)

private lemma shortestPathCount_eq_multinomial {d : ℕ} (x y : Site d) :
    shortestPathCount x y = Nat.multinomial Finset.univ (displacementVector x y) := by
  simp [shortestPathCount, latticeDistance, displacementVector, Nat.multinomial]

private lemma displacement_add_toward {d : ℕ} (x y : Site d) (j : Fin d)
    (hxy : x j < y j) :
    displacementVector (x + basisVector j) y =
      Function.update (displacementVector x y) j (displacementVector x y j - 1) := by
  ext k
  by_cases hkj : k = j
  · subst k
    have hdec : Int.natAbs (x j + 1 - y j) + 1 = Int.natAbs (x j - y j) := by
      convert natAbs_add_one_of_neg (x j - y j) (by omega) using 1 <;> omega
    simp [displacementVector, basisVector]
    omega
  · simp [displacementVector, basisVector, hkj]

private lemma displacement_sub_toward {d : ℕ} (x y : Site d) (j : Fin d)
    (hyx : y j < x j) :
    displacementVector (x - basisVector j) y =
      Function.update (displacementVector x y) j (displacementVector x y j - 1) := by
  ext k
  by_cases hkj : k = j
  · subst k
    have hdec : Int.natAbs (x j - 1 - y j) + 1 = Int.natAbs (x j - y j) := by
      have hbase : Int.natAbs (y j - x j + 1) + 1 = Int.natAbs (y j - x j) :=
        natAbs_add_one_of_neg (y j - x j) (by omega)
      have hnew : Int.natAbs (x j - 1 - y j) = Int.natAbs (y j - x j + 1) := by
        rw [show x j - 1 - y j = -(y j - x j + 1) by omega, Int.natAbs_neg]
      have hbase' : Int.natAbs (x j - y j) = Int.natAbs (y j - x j) := by
        rw [show x j - y j = -(y j - x j) by omega, Int.natAbs_neg]
      rw [hnew, hbase']
      exact hbase
    simp [displacementVector, basisVector]
    omega
  · simp [displacementVector, basisVector, hkj]

private lemma shortestPathCount_add_toward {d : ℕ} (x y : Site d) (j : Fin d)
    (hxy : x j < y j) :
    shortestPathCount (x + basisVector j) y =
      Nat.multinomial Finset.univ
        (Function.update (displacementVector x y) j (displacementVector x y j - 1)) := by
  rw [shortestPathCount_eq_multinomial, displacement_add_toward x y j hxy]

private lemma shortestPathCount_sub_toward {d : ℕ} (x y : Site d) (j : Fin d)
    (hyx : y j < x j) :
    shortestPathCount (x - basisVector j) y =
      Nat.multinomial Finset.univ
        (Function.update (displacementVector x y) j (displacementVector x y j - 1)) := by
  rw [shortestPathCount_eq_multinomial, displacement_sub_toward x y j hyx]

private def neighborPathCount {d : ℕ} (x y : Site d) (j : Fin d) : ℕ :=
  (if x j < y j then shortestPathCount (x + basisVector j) y else 0) +
    (if y j < x j then shortestPathCount (x - basisVector j) y else 0)

private lemma shortestPathCount_step_sum {d : ℕ} (x y : Site d)
    (hD : 0 < latticeDistance x y) :
    (∑ j : Fin d, neighborPathCount x y j) =
      shortestPathCount x y := by
  classical
  let a := displacementVector x y
  have hN : 0 < ∑ k : Fin d, a k := by
    simpa [a, latticeDistance, displacementVector] using hD
  have hterm : ∀ j : Fin d,
      neighborPathCount x y j =
      if 0 < a j then
        Nat.multinomial Finset.univ (Function.update a j (a j - 1)) else 0 := by
    intro j
    dsimp [neighborPathCount]
    by_cases hxy : x j < y j
    · have ha : 0 < a j := by
        dsimp [a, displacementVector]
        exact Int.natAbs_sub_pos_iff.mpr (by omega)
      rw [if_pos hxy, if_neg (by omega : ¬ y j < x j), if_pos ha]
      simpa [a] using shortestPathCount_add_toward x y j hxy
    · by_cases hyx : y j < x j
      · have ha : 0 < a j := by
          dsimp [a, displacementVector]
          exact Int.natAbs_sub_pos_iff.mpr (by omega)
        rw [if_neg hxy, if_pos hyx, if_pos ha]
        simpa [a] using shortestPathCount_sub_toward x y j hyx
      · have hEq : x j = y j := by omega
        have ha : ¬ 0 < a j := by simp [a, displacementVector, hEq]
        rw [if_neg hxy, if_neg hyx, if_neg ha]
  calc
    (∑ j : Fin d, neighborPathCount x y j) =
      ∑ j : Fin d, if 0 < a j then
        Nat.multinomial Finset.univ (Function.update a j (a j - 1)) else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hterm j
    _ = Nat.multinomial Finset.univ a := multinomial_recurrence a hN
    _ = shortestPathCount x y := (shortestPathCount_eq_multinomial x y).symm

private lemma coefficient_succ {d : ℕ} (coupling : ℝ) (ω : Configuration d)
    (x y : Site d) (n : ℕ) :
    coefficient coupling ω x y (n + 1) =
      -(∑ j : Fin d,
        (coefficient coupling ω (x + basisVector j) y n +
          coefficient coupling ω (x - basisVector j) y n)) +
        (coupling * potential ω x : ℂ) * coefficient coupling ω x y n := by
  dsimp [coefficient]
  rw [pow_succ']
  change (hamiltonian coupling ω
      ((hamiltonian coupling ω ^ n) (AndersonAC.Blueprint.delta y))) x = _
  rw [hamiltonian_apply]

private lemma coefficient_vanishes_below_distance {d : ℕ} (coupling : ℝ)
    (ω : Configuration d) (y : Site d) (n : ℕ) :
    ∀ x : Site d, n < latticeDistance x y → coefficient coupling ω x y n = 0 := by
  induction n with
  | zero =>
      intro x hdist
      have hxy : x ≠ y := by
        intro h
        subst y
        have : 0 < latticeDistance x x := hdist
        simp [latticeDistance] at this
      simp [coefficient, AndersonAC.Blueprint.delta, hxy]
  | succ n ih =>
      intro x hdist
      rw [coefficient_succ]
      have hx : coefficient coupling ω x y n = 0 :=
        ih x (by omega)
      have hallplus : ∀ j : Fin d, n < latticeDistance (x + basisVector j) y := by
        intro j
        have htri := latticeDistance_triangle x (x + basisVector j) y
        rw [latticeDistance_step] at htri
        omega
      have hallminus : ∀ j : Fin d, n < latticeDistance (x - basisVector j) y := by
        intro j
        have htri := latticeDistance_triangle x (x - basisVector j) y
        rw [latticeDistance_sub_step] at htri
        omega
      have hallcoeffplus : ∀ j : Fin d,
          coefficient coupling ω (x + basisVector j) y n = 0 := by
        intro j
        exact ih _ (hallplus j)
      have hallcoeffminus : ∀ j : Fin d,
          coefficient coupling ω (x - basisVector j) y n = 0 := by
        intro j
        exact ih _ (hallminus j)
      simp [hx, hallcoeffplus, hallcoeffminus]

private lemma latticeDistance_eq_zero_iff {d : ℕ} (x y : Site d) :
    latticeDistance x y = 0 ↔ x = y := by
  constructor
  · intro h
    funext j
    have hjle : Int.natAbs (x j - y j) ≤ latticeDistance x y := by
      simpa [latticeDistance] using
        (Finset.single_le_sum
          (s := Finset.univ)
          (f := fun k : Fin d => Int.natAbs (x k - y k))
          (fun k hk => Nat.zero_le _) (Finset.mem_univ j))
    have hjzero : Int.natAbs (x j - y j) = 0 := by
      rw [h] at hjle
      omega
    have hsub : x j - y j = 0 := Int.natAbs_eq_zero.mp hjzero
    omega
  · intro hxy
    subst y
    simp [latticeDistance]

private lemma shortestPathCount_pos {d : ℕ} (x y : Site d) :
    0 < shortestPathCount x y := by
  rw [shortestPathCount_eq_multinomial]
  exact Nat.multinomial_pos Finset.univ (displacementVector x y)

private lemma coefficient_at_distance {d : ℕ} (coupling : ℝ) (ω : Configuration d) :
    ∀ n x y, latticeDistance x y = n →
      coefficient coupling ω x y n =
        (-1 : ℂ) ^ n * (shortestPathCount x y : ℂ) := by
  intro n
  induction n with
  | zero =>
      intro x y hdist
      have hxy : x = y := latticeDistance_eq_zero_iff x y |>.mp hdist
      subst y
      simp [coefficient, shortestPathCount, latticeDistance, AndersonAC.Blueprint.delta]
  | succ n ih =>
      intro x y hdist
      have hdistpos : 0 < latticeDistance x y := by rw [hdist]; omega
      have hcenter : coefficient coupling ω x y n = 0 :=
        coefficient_vanishes_below_distance coupling ω y n x (by rw [hdist]; omega)
      let q : ℂ := (-1 : ℂ) ^ n
      let towardPlus : Fin d → ℕ := fun j =>
        if x j < y j then shortestPathCount (x + basisVector j) y else 0
      let towardMinus : Fin d → ℕ := fun j =>
        if y j < x j then shortestPathCount (x - basisVector j) y else 0
      have hplusCoeff : ∀ j : Fin d,
          coefficient coupling ω (x + basisVector j) y n =
            (if x j < y j then q * (shortestPathCount (x + basisVector j) y : ℂ) else 0) := by
        intro j
        by_cases ht : x j < y j
        · have hstep := latticeDistance_add_basis_toward x y j ht
          rw [hdist] at hstep
          have hneighbor : latticeDistance (x + basisVector j) y = n := by omega
          rw [if_pos ht]
          exact ih _ _ hneighbor
        · have hay : y j ≤ x j := by omega
          have hstep := latticeDistance_add_basis_away x y j hay
          rw [hdist] at hstep
          have hneighbor : n < latticeDistance (x + basisVector j) y := by omega
          rw [if_neg ht]
          exact coefficient_vanishes_below_distance coupling ω y n (x + basisVector j) hneighbor
      have hminusCoeff : ∀ j : Fin d,
          coefficient coupling ω (x - basisVector j) y n =
            (if y j < x j then q * (shortestPathCount (x - basisVector j) y : ℂ) else 0) := by
        intro j
        by_cases ht : y j < x j
        · have hstep := latticeDistance_sub_basis_toward x y j ht
          rw [hdist] at hstep
          have hneighbor : latticeDistance (x - basisVector j) y = n := by omega
          rw [if_pos ht]
          exact ih _ _ hneighbor
        · have hay : x j ≤ y j := by omega
          have hstep := latticeDistance_sub_basis_away x y j hay
          rw [hdist] at hstep
          have hneighbor : n < latticeDistance (x - basisVector j) y := by omega
          rw [if_neg ht]
          exact coefficient_vanishes_below_distance coupling ω y n (x - basisVector j) hneighbor
      have hplusCast : ∀ j : Fin d,
          coefficient coupling ω (x + basisVector j) y n = q * (towardPlus j : ℂ) := by
        intro j
        rw [hplusCoeff j]
        by_cases ht : x j < y j <;> simp [towardPlus, q, ht]
      have hminusCast : ∀ j : Fin d,
          coefficient coupling ω (x - basisVector j) y n = q * (towardMinus j : ℂ) := by
        intro j
        rw [hminusCoeff j]
        by_cases ht : y j < x j <;> simp [towardMinus, q, ht]
      have hcount : (∑ j : Fin d, towardPlus j) + (∑ j : Fin d, towardMinus j) =
          shortestPathCount x y := by
        simpa [towardPlus, towardMinus, neighborPathCount, Finset.sum_add_distrib] using
          shortestPathCount_step_sum x y hdistpos
      have hcountCast :
          (↑((∑ j : Fin d, towardPlus j) + (∑ j : Fin d, towardMinus j)) : ℂ) =
            (∑ j : Fin d, (towardPlus j : ℂ)) + ∑ j : Fin d, (towardMinus j : ℂ) := by
        norm_cast
      have hsum :
          (∑ j : Fin d,
            (coefficient coupling ω (x + basisVector j) y n +
              coefficient coupling ω (x - basisVector j) y n)) =
            q * (shortestPathCount x y : ℂ) := by
        calc
          _ = (∑ j : Fin d, q * (towardPlus j : ℂ)) +
                ∑ j : Fin d, q * (towardMinus j : ℂ) := by
              rw [Finset.sum_add_distrib]
              congr 1
              · apply Finset.sum_congr rfl
                intro j hj
                exact hplusCast j
              · apply Finset.sum_congr rfl
                intro j hj
                exact hminusCast j
          _ = q * ((∑ j : Fin d, (towardPlus j : ℂ)) +
                ∑ j : Fin d, (towardMinus j : ℂ)) := by
              rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add]
          _ = q * (shortestPathCount x y : ℂ) := by
              rw [← hcountCast, hcount]
      rw [coefficient_succ, hcenter, mul_zero, add_zero, hsum]
      dsimp [q]
      rw [pow_succ]
      ring

theorem shortest_path_coefficient_statement_proof : ShortestPathCoefficientStatement := by
  intro d coupling ω x y
  refine ⟨?_, ?_⟩
  · intro n hn
    exact coefficient_vanishes_below_distance coupling ω y n x hn
  · refine ⟨?_, ?_⟩
    · exact coefficient_at_distance coupling ω (latticeDistance x y) x y rfl
    · exact shortestPathCount_pos x y

end AndersonAC.SolS9Inf

namespace AndersonAC.SolS9

theorem shortest_path_coefficient_proof :
    AndersonAC.SolS9Inf.ShortestPathCoefficientStatement :=
  AndersonAC.SolS9Inf.shortest_path_coefficient_statement_proof

end AndersonAC.SolS9
