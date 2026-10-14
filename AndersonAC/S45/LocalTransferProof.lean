import AndersonAC.S45.OverlapLemmas
import AndersonAC.S45.HelperStatements2
import AndersonAC.S45.SweepEndpointProof

/-! `AndersonAC.S45.local_transfer` (Lemma 5.5): the J, lag and row parts and the
validity/reserve consequences; the energy-form part is `LocalTransferL`. -/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace AndersonAC.AgentS45

open AndersonAC.S45

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Schur test: `‖M‖² ≤ (max row sum)(max column sum)` of absolute entries. -/
theorem norm_le_schur_test (M : CMat P) (R K : ℝ) (hR : 0 ≤ R) (hK : 0 ≤ K)
    (hrow : ∀ i, (∑ j, ‖M i j‖) ≤ R) (hcol : ∀ j, (∑ i, ‖M i j‖) ≤ K) :
    ‖M‖ ≤ Real.sqrt (R * K) := by
  refine opNorm_le_of_sq M _ (Real.sqrt_nonneg _) fun x => ?_
  rw [Real.sq_sqrt (mul_nonneg hR hK)]
  have hi : ∀ i, ‖(M *ᵥ x) i‖ ^ 2 ≤ R * ∑ j, ‖M i j‖ * ‖x j‖ ^ 2 := by
    intro i
    have h1 : ‖(M *ᵥ x) i‖ ≤ ∑ j, ‖M i j‖ * ‖x j‖ := by
      simp only [Matrix.mulVec, dotProduct]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      simp [norm_mul]
    have h2 : (∑ j, ‖M i j‖ * ‖x j‖) ^ 2 ≤ (∑ j, ‖M i j‖) * ∑ j, ‖M i j‖ * ‖x j‖ ^ 2 := by
      -- weighted Cauchy–Schwarz
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => Real.sqrt ‖M i j‖)
        (fun j => Real.sqrt ‖M i j‖ * ‖x j‖)
      have e1 : ∀ j, Real.sqrt ‖M i j‖ * (Real.sqrt ‖M i j‖ * ‖x j‖) = ‖M i j‖ * ‖x j‖ :=
        fun j => by rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
      have e2 : ∀ j, Real.sqrt ‖M i j‖ ^ 2 = ‖M i j‖ := fun j => Real.sq_sqrt (norm_nonneg _)
      have e3 : ∀ j, (Real.sqrt ‖M i j‖ * ‖x j‖) ^ 2 = ‖M i j‖ * ‖x j‖ ^ 2 :=
        fun j => by rw [mul_pow, e2]
      simp only [e1, e2, e3] at hcs
      exact hcs
    calc ‖(M *ᵥ x) i‖ ^ 2 ≤ (∑ j, ‖M i j‖ * ‖x j‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ j, ‖M i j‖) * ∑ j, ‖M i j‖ * ‖x j‖ ^ 2 := h2
      _ ≤ R * ∑ j, ‖M i j‖ * ‖x j‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hrow i) (Finset.sum_nonneg fun _ _ => by positivity)
  calc (∑ i, ‖(M *ᵥ x) i‖ ^ 2) ≤ ∑ i, R * ∑ j, ‖M i j‖ * ‖x j‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => hi i
    _ = R * ∑ j, (∑ i, ‖M i j‖) * ‖x j‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
    _ ≤ R * ∑ j, K * ‖x j‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)) hR
    _ = R * K * ∑ j, ‖x j‖ ^ 2 := by rw [← Finset.mul_sum]; ring

/-! ### Bookkeeping over blocks and distinct pivots -/

theorem partition_sum {ι M : Type*} [Fintype ι] [AddCommMonoid M] (len : ℕ)
    (blocks : ι → Finset ℕ) (hb : ∀ k < len, ∃! T, k ∈ blocks T)
    (hsub : ∀ T, blocks T ⊆ Finset.range len) (g : ℕ → M) :
    (∑ T, ∑ k ∈ blocks T, g k) = ∑ k ∈ Finset.range len, g k := by
  classical
  have h1 : ∀ T, (∑ k ∈ blocks T, g k) = ∑ k ∈ Finset.range len, if k ∈ blocks T then g k else 0 :=
    fun T => by rw [← Finset.sum_filter]; congr 1; ext k; simp only [Finset.mem_filter,
      Finset.mem_range]; exact ⟨fun h => ⟨Finset.mem_range.1 (hsub T h), h⟩, fun h => h.2⟩
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨T, hT, huniq⟩ := hb k (Finset.mem_range.1 hk)
  rw [Finset.sum_eq_single T]
  · simp [hT]
  · intro T' _ hT'; rw [if_neg]; exact fun h => hT' (huniq T' h)
  · simp

theorem pivot_sum (len : ℕ) (pv : ℕ → Option P)
    (hinj : ∀ k l, k < len → l < len → ∀ x, pv k = some x → pv l = some x → k = l)
    (f : P → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ k ∈ Finset.range len, (pv k).elim 0 f) ≤ ∑ x, f x := by
  classical
  have h1 : ∀ k, (pv k).elim 0 f = ∑ x, if pv k = some x then f x else 0 := by
    intro k
    cases h : pv k with
    | none => simp
    | some y => simp [Finset.sum_ite_eq']
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.range len).filter fun k => pv k = some x).card ≤ 1 := by
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at ha hb
    exact hinj a b ha.1 hb.1 x ha.2 hb.2
  have : (((Finset.range len).filter fun k => pv k = some x).card : ℝ) ≤ 1 := by exact_mod_cast hc
  nlinarith [hf x]

theorem exp_far {u R d : ℝ} (hu : 0 ≤ u) (hd : R ≤ d) :
    Real.exp (-(2 * u) * d) ≤ Real.exp (-u * R) * Real.exp (-u * d) := by
  rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith

/-- Scalar records: bounded overlap of the local budgets plus far tails. -/
theorem scalar_transfer {ι E : Type*} [Fintype ι] [SeminormedAddCommGroup E] (len : ℕ)
    (pv : ℕ → Option P)
    (hinj : ∀ k l, k < len → l < len → ∀ x, pv k = some x → pv l = some x → k = l)
    (blocks : ι → Finset ℕ) (hb : ∀ k < len, ∃! T, k ∈ blocks T)
    (hsub : ∀ T, blocks T ⊆ Finset.range len) (inner tile : ι → Finset P)
    (dist : P → P → ℝ) (Cov β A u R : ℝ) (hu : 0 ≤ u) (hA : 0 ≤ A) (hβ : 0 ≤ β)
    (hov : ∀ i, ((Finset.univ.filter fun T => i ∈ inner T).card : ℝ) ≤ Cov)
    (htile : ∀ k < len, ∀ x, pv k = some x → ∀ T, k ∈ blocks T → x ∈ tile T)
    (hbuf : ∀ T, ∀ x ∈ tile T, ∀ i, i ∉ inner T → R ≤ dist i x)
    (s : ℕ → P → E) (hnone : ∀ k < len, pv k = none → s k = 0)
    (htail : ∀ k < len, ∀ x, pv k = some x → ∀ i,
      ‖s k i‖ ≤ A * Real.exp (-(2 * u) * dist i x))
    (hbud : ∀ T, ∀ i ∈ inner T, ‖∑ k ∈ blocks T, s k i‖ ≤ β) (i : P) :
    ‖∑ k ∈ Finset.range len, s k i‖ ≤
      Cov * β + A * Real.exp (-u * R) * ∑ x, Real.exp (-u * dist i x) := by
  classical
  rw [← partition_sum len blocks hb hsub (fun k => s k i),
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun T => i ∈ inner T)]
  set F := Finset.univ.filter fun T => i ∈ inner T
  have h1 : ‖∑ T ∈ F, ∑ k ∈ blocks T, s k i‖ ≤ Cov * β := by
    refine (norm_sum_le _ _).trans ?_
    calc (∑ T ∈ F, ‖∑ k ∈ blocks T, s k i‖) ≤ ∑ T ∈ F, β :=
          Finset.sum_le_sum fun T hT => hbud T i (Finset.mem_filter.1 hT).2
      _ = F.card * β := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Cov * β := mul_le_mul_of_nonneg_right (hov i) hβ
  set g : ℕ → ℝ := fun k => A * Real.exp (-u * R) * (pv k).elim 0 (fun x => Real.exp (-u * dist i x))
  have hg0 : ∀ k, 0 ≤ g k := fun k => by
    simp only [g]; cases pv k <;> simp <;> positivity
  have hkey : ∀ T, T ∉ F → ∀ k ∈ blocks T, ‖s k i‖ ≤ g k := by
    intro T hT k hk
    have hkl : k < len := Finset.mem_range.1 (hsub T hk)
    have hiT : i ∉ inner T := fun h => hT (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    cases hpv : pv k with
    | none => rw [hnone k hkl hpv]; simp [g, hpv]
    | some x =>
      have hx := htile k hkl x hpv T hk
      have hd := hbuf T x hx i hiT
      calc ‖s k i‖ ≤ A * Real.exp (-(2 * u) * dist i x) := htail k hkl x hpv i
        _ ≤ A * (Real.exp (-u * R) * Real.exp (-u * dist i x)) :=
            mul_le_mul_of_nonneg_left (exp_far hu hd) hA
        _ = g k := by simp [g, hpv]; ring
  have h2 : ‖∑ T ∈ Finset.univ.filter (fun T => ¬ i ∈ inner T), ∑ k ∈ blocks T, s k i‖ ≤
      A * Real.exp (-u * R) * ∑ x, Real.exp (-u * dist i x) := by
    refine (norm_sum_le _ _).trans ?_
    calc (∑ T ∈ Finset.univ.filter (fun T => ¬ i ∈ inner T), ‖∑ k ∈ blocks T, s k i‖)
        ≤ ∑ T ∈ Finset.univ.filter (fun T => ¬ i ∈ inner T), ∑ k ∈ blocks T, g k := by
          refine Finset.sum_le_sum fun T hT => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun k hk => hkey T ?_ k hk)
          intro hF; exact (Finset.mem_filter.1 hT).2 (Finset.mem_filter.1 hF).2
      _ ≤ ∑ T, ∑ k ∈ blocks T, g k :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun T _ _ => Finset.sum_nonneg fun k _ => hg0 k
      _ = ∑ k ∈ Finset.range len, g k := partition_sum len blocks hb hsub g
      _ = A * Real.exp (-u * R) *
            ∑ k ∈ Finset.range len, (pv k).elim 0 (fun x => Real.exp (-u * dist i x)) := by
          rw [Finset.mul_sum]
      _ ≤ A * Real.exp (-u * R) * ∑ x, Real.exp (-u * dist i x) :=
          mul_le_mul_of_nonneg_left (pivot_sum len pv hinj _ fun x => (Real.exp_pos _).le)
            (by positivity)
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

/-- Matrix records: bounded overlap of local budgets plus far tails (Schur test). -/
theorem matrix_transfer {ι : Type*} [Fintype ι] (len : ℕ) (pv : ℕ → Option P)
    (hinj : ∀ k l, k < len → l < len → ∀ x, pv k = some x → pv l = some x → k = l)
    (blocks : ι → Finset ℕ) (hb : ∀ k < len, ∃! T, k ∈ blocks T)
    (hsub : ∀ T, blocks T ⊆ Finset.range len) (inner tile : ι → Finset P)
    (dist : P → P → ℝ) (hdist : ∀ i j, 0 ≤ dist i j) (Cov β A u R S : ℝ) (hu : 0 ≤ u)
    (hA : 0 ≤ A) (hβ : 0 ≤ β) (hCov : 0 ≤ Cov) (hS0 : 0 ≤ S)
    (hov : ∀ i, ((Finset.univ.filter fun T => i ∈ inner T).card : ℝ) ≤ Cov)
    (htile : ∀ k < len, ∀ x, pv k = some x → ∀ T, k ∈ blocks T → x ∈ tile T)
    (hbuf : ∀ T, ∀ x ∈ tile T, ∀ i, i ∉ inner T → R ≤ dist i x)
    (hS1 : ∀ x, (∑ j, Real.exp (-u * dist j x)) ≤ S)
    (hS2 : ∀ i, (∑ x, Real.exp (-u * dist i x)) ≤ S)
    (J : ℕ → CMat P) (hnone : ∀ k < len, pv k = none → J k = 0)
    (htail : ∀ k < len, ∀ x, pv k = some x → ∀ i j,
      ‖J k i j‖ ≤ A * Real.exp (-(2 * u) * (dist i x + dist j x)))
    (hbud : ∀ T, ‖mask (inner T) (∑ k ∈ blocks T, J k)‖ ≤ β) :
    ‖∑ k ∈ Finset.range len, J k‖ ≤ Cov * β + A * Real.exp (-u * R) * S ^ 2 := by
  classical
  set JT : ι → CMat P := fun T => ∑ k ∈ blocks T, J k
  have hsplit : (∑ k ∈ Finset.range len, J k) =
      (∑ T, mask (inner T) (JT T)) + ∑ T, (JT T - mask (inner T) (JT T)) := by
    rw [← partition_sum len blocks hb hsub J, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun T _ => by abel
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add (norm_sum_mask_le inner Cov β hCov hβ hov JT hbud) ?_)
  set E := ∑ T, (JT T - mask (inner T) (JT T))
  set g : P → P → ℕ → ℝ := fun i j k => A * Real.exp (-u * R) *
    (pv k).elim 0 (fun x => Real.exp (-u * dist i x) * Real.exp (-u * dist j x))
  have hg0 : ∀ i j k, 0 ≤ g i j k := fun i j k => by
    simp only [g]; cases pv k <;> simp <;> positivity
  have hentry : ∀ i j, ‖E i j‖ ≤ ∑ k ∈ Finset.range len, g i j k := by
    intro i j
    have e1 : E i j = ∑ T, (if i ∈ inner T ∧ j ∈ inner T then 0 else JT T i j) := by
      simp only [E, Matrix.sum_apply, Matrix.sub_apply, mask_apply']
      refine Finset.sum_congr rfl fun T _ => ?_
      split_ifs <;> simp
    rw [e1, ← partition_sum len blocks hb hsub (g i j)]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun T _ => ?_)
    split_ifs with hin
    · rw [norm_zero]; exact Finset.sum_nonneg fun k _ => hg0 i j k
    · simp only [JT, Matrix.sum_apply]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
      have hkl : k < len := Finset.mem_range.1 (hsub T hk)
      cases hpv : pv k with
      | none => rw [hnone k hkl hpv]; simp [g, hpv]
      | some x =>
        have hx := htile k hkl x hpv T hk
        have hd : R ≤ dist i x + dist j x := by
          by_cases hi : i ∈ inner T
          · have hj : j ∉ inner T := fun hj => hin ⟨hi, hj⟩
            linarith [hbuf T x hx j hj, hdist i x]
          · linarith [hbuf T x hx i hi, hdist j x]
        calc ‖J k i j‖ ≤ A * Real.exp (-(2 * u) * (dist i x + dist j x)) := htail k hkl x hpv i j
          _ ≤ A * (Real.exp (-u * R) * Real.exp (-u * (dist i x + dist j x))) :=
              mul_le_mul_of_nonneg_left (exp_far hu hd) hA
          _ = g i j k := by
              simp only [g, hpv, Option.elim]
              rw [show -u * (dist i x + dist j x) = -u * dist i x + -u * dist j x by ring,
                Real.exp_add]; ring
  set X := A * Real.exp (-u * R) * S ^ 2
  have hX : 0 ≤ X := by positivity
  have hrow : ∀ i, (∑ j, ‖E i j‖) ≤ X := by
    intro i
    calc (∑ j, ‖E i j‖) ≤ ∑ j, ∑ k ∈ Finset.range len, g i j k := Finset.sum_le_sum fun j _ => hentry i j
      _ = ∑ k ∈ Finset.range len, A * Real.exp (-u * R) *
            (pv k).elim 0 (fun x => Real.exp (-u * dist i x) * ∑ j, Real.exp (-u * dist j x)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [g]; cases pv k <;> simp [Finset.mul_sum]
      _ ≤ ∑ k ∈ Finset.range len, A * Real.exp (-u * R) *
            (pv k).elim 0 (fun x => Real.exp (-u * dist i x) * S) := by
          refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
          cases pv k with
          | none => simp
          | some x => exact mul_le_mul_of_nonneg_left (hS1 x) (Real.exp_pos _).le
      _ = A * Real.exp (-u * R) *
            ∑ k ∈ Finset.range len, (pv k).elim 0 (fun x => Real.exp (-u * dist i x) * S) := by
          rw [Finset.mul_sum]
      _ ≤ A * Real.exp (-u * R) * ∑ x, Real.exp (-u * dist i x) * S :=
          mul_le_mul_of_nonneg_left (pivot_sum len pv hinj _ fun x => by positivity) (by positivity)
      _ ≤ X := by
          rw [← Finset.sum_mul]
          have := mul_le_mul_of_nonneg_right (hS2 i) hS0
          calc A * Real.exp (-u * R) * ((∑ x, Real.exp (-u * dist i x)) * S)
              ≤ A * Real.exp (-u * R) * (S * S) := mul_le_mul_of_nonneg_left this (by positivity)
            _ = X := by ring
  have hcol : ∀ j, (∑ i, ‖E i j‖) ≤ X := by
    intro j
    calc (∑ i, ‖E i j‖) ≤ ∑ i, ∑ k ∈ Finset.range len, g i j k := Finset.sum_le_sum fun i _ => hentry i j
      _ = ∑ k ∈ Finset.range len, A * Real.exp (-u * R) *
            (pv k).elim 0 (fun x => Real.exp (-u * dist j x) * ∑ i, Real.exp (-u * dist i x)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [g]; cases pv k <;> simp [Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm]
      _ ≤ ∑ k ∈ Finset.range len, A * Real.exp (-u * R) *
            (pv k).elim 0 (fun x => Real.exp (-u * dist j x) * S) := by
          refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
          cases pv k with
          | none => simp
          | some x => exact mul_le_mul_of_nonneg_left (hS1 x) (Real.exp_pos _).le
      _ = A * Real.exp (-u * R) *
            ∑ k ∈ Finset.range len, (pv k).elim 0 (fun x => Real.exp (-u * dist j x) * S) := by
          rw [Finset.mul_sum]
      _ ≤ A * Real.exp (-u * R) * ∑ x, Real.exp (-u * dist j x) * S :=
          mul_le_mul_of_nonneg_left (pivot_sum len pv hinj _ fun x => by positivity) (by positivity)
      _ ≤ X := by
          rw [← Finset.sum_mul]
          have := mul_le_mul_of_nonneg_right (hS2 j) hS0
          calc A * Real.exp (-u * R) * ((∑ x, Real.exp (-u * dist j x)) * S)
              ≤ A * Real.exp (-u * R) * (S * S) := mul_le_mul_of_nonneg_left this (by positivity)
            _ = X := by ring
  have h := norm_le_schur_test E X X hX hX hrow hcol
  rwa [Real.sqrt_mul_self hX] at h

/-! ### Smallness of the far tails -/

/-- The far-tail size `t^{-C₀} e^{-(c/2) t^{-3}} (C₁ (c t³/2)^{-d})²` is at most `t` for small `t`. -/
theorem tail_small (C₀ C₁ c : ℝ) (d : ℕ) (hc : 0 < c) :
    ∃ t1 > 0, ∀ t, 0 < t → t < t1 →
      power t (-C₀) * Real.exp (-(c * t ^ 3 / 2) * power t (-6)) *
        (C₁ * power (c * t ^ 3 / 2) (-(d : ℝ))) ^ 2 ≤ t := by
  set a := c / 2 with ha
  have ha0 : 0 < a := by positivity
  set K := C₁ ^ 2 * (power a (-(d : ℝ))) ^ 2 with hK
  set q := C₀ + 6 * d + 1 with hq
  have hlim := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero q a ha0
  have hev : ∀ᶠ z in Filter.atTop, K * (z ^ q * Real.exp (-a * z)) ≤ 1 := by
    have h2 := hlim.const_mul K
    rw [mul_zero] at h2
    exact h2.eventually (ge_mem_nhds one_pos)
  obtain ⟨Z, hZ⟩ := Filter.eventually_atTop.1 hev
  refine ⟨1 / max Z 1, by positivity, fun t ht htt => ?_⟩
  have hM : 0 < max Z 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set z := 1 / t with hzdef
  have hz : max Z 1 < z := by
    rw [hzdef, lt_div_iff₀ ht]; rw [lt_div_iff₀ hM] at htt; linarith
  have hz1 : 1 ≤ z := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hz)
  have hzZ : Z ≤ z := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hz)
  have hz0 : 0 < z := by positivity
  have htz : t = z⁻¹ := by rw [hzdef, one_div, inv_inv]
  -- rewrite everything in z
  have e1 : power t (-C₀) = z ^ C₀ := by
    show t ^ (-C₀) = _
    rw [htz, Real.inv_rpow hz0.le, Real.rpow_neg hz0.le, inv_inv]
  have e2 : power t (-6) = z ^ 3 * z ^ 3 := by
    show t ^ (-6 : ℝ) = _
    rw [htz, Real.inv_rpow hz0.le, Real.rpow_neg hz0.le, inv_inv,
      show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  have e3 : power (c * t ^ 3 / 2) (-(d : ℝ)) = power a (-(d : ℝ)) * z ^ (3 * (d : ℝ)) := by
    show (c * t ^ 3 / 2) ^ (-(d : ℝ)) = a ^ (-(d : ℝ)) * _
    rw [show c * t ^ 3 / 2 = a * t ^ 3 by rw [ha]; ring, Real.mul_rpow ha0.le (by positivity)]
    congr 1
    rw [htz, inv_pow, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv,
      ← Real.rpow_natCast z 3, ← Real.rpow_mul hz0.le]
    norm_num
  have e4 : -(c * t ^ 3 / 2) * (z ^ 3 * z ^ 3) = -(a * z ^ 3) := by
    have : t * z = 1 := by rw [htz, inv_mul_cancel₀ hz0.ne']
    have h3 : t ^ 3 * z ^ 3 = 1 := by rw [← mul_pow, this, one_pow]
    rw [ha]; linear_combination (-(c / 2) * z ^ 3) * h3
  rw [e1, e2, e3, e4]
  have hexp : Real.exp (-(a * z ^ 3)) ≤ Real.exp (-a * z) := by
    apply Real.exp_le_exp.2
    have : z ≤ z ^ 3 := by
      nlinarith [mul_nonneg (mul_nonneg hz0.le (sub_nonneg.2 hz1)) (by linarith : (0 : ℝ) ≤ z + 1)]
    nlinarith
  have hkey := hZ z hzZ
  have hpow : z ^ C₀ * (z ^ (3 * (d : ℝ))) ^ 2 * z = z ^ q := by
    have h1 : (z ^ (3 * (d : ℝ))) ^ 2 = z ^ (6 * (d : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hz0.le]; norm_num; ring_nf
    rw [h1]
    calc z ^ C₀ * z ^ (6 * (d : ℝ)) * z = z ^ C₀ * z ^ (6 * (d : ℝ)) * z ^ (1 : ℝ) := by
          rw [Real.rpow_one]
      _ = z ^ q := by rw [← Real.rpow_add hz0, ← Real.rpow_add hz0]
  have hgoal : z ^ C₀ * Real.exp (-(a * z ^ 3)) *
      (C₁ * (power a (-(d : ℝ)) * z ^ (3 * (d : ℝ)))) ^ 2 * z ≤ 1 := by
    calc z ^ C₀ * Real.exp (-(a * z ^ 3)) *
          (C₁ * (power a (-(d : ℝ)) * z ^ (3 * (d : ℝ)))) ^ 2 * z
        = K * ((z ^ C₀ * (z ^ (3 * (d : ℝ))) ^ 2 * z) * Real.exp (-(a * z ^ 3))) := by
          rw [hK]; ring
      _ ≤ K * (z ^ q * Real.exp (-a * z)) := by
          rw [hpow]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hz0.le _)) (by positivity)
      _ ≤ 1 := hkey
  rw [htz]
  have hz' : 0 < z⁻¹ := inv_pos.2 hz0
  calc z ^ C₀ * Real.exp (-(a * z ^ 3)) * (C₁ * (power a (-(d : ℝ)) * z ^ (3 * (d : ℝ)))) ^ 2
      = (z ^ C₀ * Real.exp (-(a * z ^ 3)) *
          (C₁ * (power a (-(d : ℝ)) * z ^ (3 * (d : ℝ)))) ^ 2 * z) * z⁻¹ := by
        rw [mul_assoc _ z, mul_inv_cancel₀ hz0.ne', mul_one]
    _ ≤ 1 * z⁻¹ := mul_le_mul_of_nonneg_right hgoal hz'.le
    _ = z⁻¹ := one_mul _

/-! ### Sequence bookkeeping -/

theorem step_none {q : Sequence P} {t : ℝ} {r : P → ℂ} (hwf : q.wellFormed t r) {k : ℕ}
    (hk : k < q.length) (hpv : q.pivot k = none) :
    q.stepJ t r k = 0 ∧ q.stepLag t r k = 0 ∧ ∀ cols, q.stepRow t r cols k = 0 := by
  have h := hwf.2 k hk
  rw [hpv] at h
  simp only at h
  refine ⟨by simp [Sequence.stepJ, hpv], ?_, fun cols => ?_⟩
  · funext i; simp [Sequence.stepLag, h]
  · funext i; simp [Sequence.stepRow, h]

/-- The type of `AndersonAC.S45.scalar_records` at universe 0. -/
def ScalarRecordsStmt : Prop :=
  ∀ (P : Type) [Fintype P] [DecidableEq P]
    (q : Sequence P) (t : ℝ) (r : P → ℂ) (cols : Finset P)
    (_ht : 0 < t) (_hseq : q.wellFormed t r)
    (_hu0 : ∀ i ∈ (q.state 0).live, (q.state 0).ambientLag t r i = 0),
    ∀ i ∈ (q.state q.length).live,
      q.lagRecord t r (Finset.range q.length) i = (q.state q.length).ambientLag t r i ∧
      (∑ j ∈ cols ∩ (q.state q.length).live, ‖((q.state q.length).ambient r).h t i j‖^4) ≤
        (∑ j ∈ cols ∩ (q.state 0).live, ‖((q.state 0).ambient r).h t i j‖^4) +
          rowCap t * q.rowRecord t r cols (Finset.range q.length) i

theorem le_power_of_le_one {t e : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (he : e ≤ 1) :
    t ≤ power t e := by
  show t ≤ t ^ e
  calc t = t ^ (1 : ℝ) := (Real.rpow_one t).symm
    _ ≤ t ^ e := Real.rpow_le_rpow_of_exponent_ge ht ht1 he

theorem power_split {t a b : ℝ} (ht : 0 < t) : power t (a + b) = power t a * power t b :=
  Real.rpow_add ht a b

/-- Entries of the ambient `h` on live coordinates. -/
theorem ambient_h_live (a : LiveState P) (r : P → ℂ) (t : ℝ) {i j : P} (hi : i ∈ a.live)
    (hj : j ∈ a.live) : (a.ambient r).h t i j = (a.state r).h t ⟨i, hi⟩ ⟨j, hj⟩ := by
  show (Real.sqrt t : ℂ) * mask a.live a.g i j = (Real.sqrt t : ℂ) * restrict a.g a.live ⟨i, hi⟩ ⟨j, hj⟩
  rw [mask, pad_apply_mem a.live _ hi hj]

theorem ambient_h_dead (a : LiveState P) (r : P → ℂ) (t : ℝ) (i : P) {j : P} (hj : j ∉ a.live) :
    (a.ambient r).h t i j = 0 := by
  show (Real.sqrt t : ℂ) * mask a.live a.g i j = 0
  simp [mask, pad, hj]

/-! ### Lemma 5.5 -/

set_option maxHeartbeats 1000000 in
theorem local_transfer_of (hL : LocalTransferL) (hsr : ScalarRecordsStmt) :
    ∀ (d : ℕ) (C c : ℝ), 1 ≤ C → 0 < c →
    ∃ C' > 0, ∃ t0 > 0, ∀ (n m : ℕ) (t b θ : ℝ)
    (dist : Fin n → Fin n → ℝ) (r : Fin n → ℂ) (res : Finset (Fin n))
    (cover : TileCover (P := Fin n) (I := Fin m) d t b C dist)
    (q : Sequence (Fin n)) (blocks : Fin cover.count → Finset ℕ) (D0 : RMat (Fin n)),
    0 < t → t < t0 → 0 < b → b ≤ t → 1 / 4 ≤ θ → θ ≤ 5 / 8 →
    ShellBounds d C dist → q.wellFormed t r → (q.state 0).live = Finset.univ →
    (∀ k < q.length, ∃! T, k ∈ blocks T) → (∀ T, blocks T ⊆ Finset.range q.length) →
    (∀ k < q.length, ∀ x, q.pivot k = some x → ∀ T, k ∈ blocks T → x ∈ cover.tile T) →
    (∀ k l, k < q.length → l < q.length → ∀ x y,
      q.pivot k = some x → q.pivot l = some y → cover.site x = cover.site y → k = l) →
    TraceTails q t C c r res dist →
    (∀ k < q.length, (q.stepL t r k).IsSymm ∧ q.stepL t r k *ᵥ (fun _ => 1) = 0) →
    formComparable (qform D0) (spatialEnergy cover.site b cover.energy) C →
    (∀ i, (q.state 0).ambientLag t r i = 0) →
    (∀ i, ((q.state 0).ambient r).fourthRow t Finset.univ i ≤ 3 / 4 * rowCap t) →
    (∀ i ∈ res, ((q.state 0).ambient r).fourthRow t res i ≤ θ^2 * rowCap t) →
    (∀ T, localBudget cover T (q.Jrecord t r (blocks T)) (q.Lrecord t r (blocks T))
      (q.lagRecord t r (blocks T)) (q.rowRecord t r Finset.univ (blocks T))
      (q.rowRecord t r res (blocks T))) →
    ‖q.Jrecord t r (Finset.range q.length)‖ ≤ C' * power t (delta / 8) ∧
    formAbsLe (qform (q.Lrecord t r (Finset.range q.length))) (qform D0)
      (C' * power t (delta / 8)) ∧
    (∀ i, ‖q.lagRecord t r (Finset.range q.length) i‖ ≤ C' * power t (11 * delta / 25)) ∧
    (∀ i, |q.rowRecord t r Finset.univ (Finset.range q.length) i| ≤ C' * power t (delta / 2000) ∧
      |q.rowRecord t r res (Finset.range q.length) i| ≤ C' * power t (delta / 2000)) ∧
    q.valid t r D0 q.length ∧
    (∀ i ∈ res ∩ (q.state q.length).live,
      ((q.state q.length).ambient r).fourthRow t res i ≤
        (θ^2 + C' * power t (delta / 2000)) * rowCap t) := by
  intro d C c hC hc
  have hC0 : 0 < C := by linarith
  obtain ⟨CL, hCL, tL, htL, hLmain⟩ := hL d C c hC hc
  obtain ⟨t1, ht1, htail⟩ := tail_small C C c d hc
  set C' : ℝ := max (C + 1) CL with hC'def
  have hC'pos : 0 < C' := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hC1 : C + 1 ≤ C' := le_max_left _ _
  have hCLle : CL ≤ C' := le_max_right _ _
  obtain ⟨t2, ht2, hs2⟩ := power_small (e := delta / 40) (by norm_num [delta]) (a := 1 / C')
    (by positivity)
  obtain ⟨t3, ht3, hs3⟩ := power_small (e := delta / 2000) (by norm_num [delta])
    (a := 1 / (4 * C')) (by positivity)
  obtain ⟨t4, ht4, hs4⟩ := power_small (e := delta / 50) (by norm_num [delta]) (a := 1 / C')
    (by positivity)
  obtain ⟨t5, ht5, hs5⟩ := power_small (e := 3) (by norm_num) (a := 2 / c) (by positivity)
  refine ⟨C', hC'pos, min (min (min tL t1) (min t2 t3)) (min (min t4 t5) 1),
    by positivity, ?_⟩
  intro n m t b θ dist r res cover q blocks D0 ht htt hb hbt hθ1 hθ2 hshell hwf hlive0 hblk hbsub
    htile hdistinct htails hstepL hcomp hu0 hrow0 hres0 hbud
  have httL : t < tL := lt_of_lt_of_le htt (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
    (min_le_left _ _)))
  have htt1 : t < t1 := lt_of_lt_of_le htt (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
    (min_le_right _ _)))
  have htt2 : t < t2 := lt_of_lt_of_le htt (le_trans (min_le_left _ _) (le_trans (min_le_right _ _)
    (min_le_left _ _)))
  have htt3 : t < t3 := lt_of_lt_of_le htt (le_trans (min_le_left _ _) (le_trans (min_le_right _ _)
    (min_le_right _ _)))
  have htt4 : t < t4 := lt_of_lt_of_le htt (le_trans (min_le_right _ _) (le_trans (min_le_left _ _)
    (min_le_left _ _)))
  have htt5 : t < t5 := lt_of_lt_of_le htt (le_trans (min_le_right _ _) (le_trans (min_le_left _ _)
    (min_le_right _ _)))
  have ht1' : t ≤ 1 := (lt_of_lt_of_le htt (le_trans (min_le_right _ _) (min_le_right _ _))).le
  -- the L part
  have hLpart := hLmain n m t b θ dist r res cover q blocks D0 ht httL hb hbt hθ1 hθ2 hshell hwf
    hlive0 hblk hbsub htile hdistinct htails hstepL hcomp hu0 hrow0 hres0 hbud
  -- kernel parameters
  set u : ℝ := c * t ^ 3 / 2 with hudef
  have hu0' : 0 < u := by positivity
  have hu1 : u ≤ 1 := by
    have h := hs5 t ht htt5
    have : power t 3 = t ^ 3 := by
      show t ^ (3 : ℝ) = t ^ 3; exact_mod_cast Real.rpow_natCast t 3
    rw [this] at h
    rw [hudef]
    have := mul_lt_mul_of_pos_left h hc
    rw [mul_div_cancel₀ _ (ne_of_gt hc)] at this
    linarith
  set A : ℝ := power t (-C) with hAdef
  have hA0 : 0 ≤ A := (Real.rpow_pos_of_pos ht _).le
  set R : ℝ := power t (-6) with hRdef
  set S : ℝ := C * power u (-(d : ℝ)) with hSdef
  have hS1' : 1 ≤ power u (-(d : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0' hu1 (by simp)
  have hS0 : 0 ≤ S := by positivity
  have hSge : 1 ≤ S := by nlinarith
  have hcount1 : ∀ x, (∑ j, Real.exp (-u * dist j x)) ≤ S := by
    intro x
    have := hshell.count u hu0' hu1 x
    calc (∑ j, Real.exp (-u * dist j x)) = ∑ j, Real.exp (-u * dist x j) :=
          Finset.sum_congr rfl fun j _ => by rw [hshell.symmetric]
      _ ≤ S := this
  have hcount2 : ∀ i, (∑ x, Real.exp (-u * dist i x)) ≤ S := fun i => hshell.count u hu0' hu1 i
  have htailt : A * Real.exp (-u * R) * S ^ 2 ≤ t := htail t ht htt1
  have hTAIL : ∀ e, e ≤ 1 → A * Real.exp (-u * R) * S ^ 2 ≤ power t e := fun e he =>
    htailt.trans (le_power_of_le_one ht ht1' he)
  have hTAIL1 : ∀ i, A * Real.exp (-u * R) * ∑ x, Real.exp (-u * dist i x) ≤
      A * Real.exp (-u * R) * S ^ 2 := by
    intro i
    refine mul_le_mul_of_nonneg_left ((hcount2 i).trans ?_) (by positivity)
    nlinarith
  -- pivots, overlap, buffer
  have hinj : ∀ k l, k < q.length → l < q.length → ∀ x, q.pivot k = some x →
      q.pivot l = some x → k = l :=
    fun k l hk hl x hx hy => hdistinct k l hk hl x x hx hy rfl
  have hov : ∀ i, ((Finset.univ.filter fun T => i ∈ cover.inner T).card : ℝ) ≤ C :=
    fun i => cover.overlap i
  have hbuf : ∀ T, ∀ x ∈ cover.tile T, ∀ i, i ∉ cover.inner T → R ≤ dist i x := cover.buffer
  have hexpu : ∀ z : ℝ, Real.exp (-c * t ^ 3 * z) = Real.exp (-(2 * u) * z) := fun z => by
    rw [hudef]; ring_nf
  -- J
  have hJ : ‖q.Jrecord t r (Finset.range q.length)‖ ≤ (C + 1) * power t (delta / 8) := by
    have h := matrix_transfer q.length q.pivot hinj blocks hblk hbsub cover.inner cover.tile dist
      hshell.nonneg C (power t (delta / 8)) A u R S hu0'.le hA0
      (Real.rpow_pos_of_pos ht _).le hC0.le hS0 hov htile hbuf hcount1 hcount2
      (fun k => q.stepJ t r k) (fun k hk hpv => (step_none hwf hk hpv).1)
      (fun k hk x hpv i j => by rw [← hexpu]; exact htails.J k hk x hpv i j)
      (fun T => (hbud T).2.2.1)
    have h2 := hTAIL (delta / 8) (by norm_num [delta])
    calc ‖q.Jrecord t r (Finset.range q.length)‖ ≤ C * power t (delta / 8) +
          A * Real.exp (-u * R) * S ^ 2 := h
      _ ≤ (C + 1) * power t (delta / 8) := by linarith
  -- lag
  have hlag : ∀ i, ‖q.lagRecord t r (Finset.range q.length) i‖ ≤
      (C + 1) * power t (11 * delta / 25) := by
    intro i
    have h := scalar_transfer q.length q.pivot hinj blocks hblk hbsub cover.inner cover.tile dist
      C (power t (11 * delta / 25)) A u R hu0'.le hA0 (Real.rpow_pos_of_pos ht _).le hov htile hbuf
      (fun k => q.stepLag t r k) (fun k hk hpv => (step_none hwf hk hpv).2.1)
      (fun k hk x hpv i => by rw [← hexpu]; exact htails.lag k hk x hpv i)
      (fun T i hi => by
        have := (hbud T).1 i hi
        simpa [Sequence.lagRecord, Finset.sum_apply] using this) i
    have h2 := (hTAIL1 i).trans (hTAIL (11 * delta / 25) (by norm_num [delta]))
    have e : q.lagRecord t r (Finset.range q.length) i =
        ∑ k ∈ Finset.range q.length, q.stepLag t r k i := by
      simp [Sequence.lagRecord, Finset.sum_apply]
    rw [e]; linarith
  -- rows
  have hrowb : ∀ (cols : Finset (Fin n)), (cols = Finset.univ ∨ cols = res) → ∀ i,
      |q.rowRecord t r cols (Finset.range q.length) i| ≤ (C + 1) * power t (delta / 2000) := by
    intro cols hcols i
    have h := scalar_transfer q.length q.pivot hinj blocks hblk hbsub cover.inner cover.tile dist
      C (power t (delta / 2000)) A u R hu0'.le hA0 (Real.rpow_pos_of_pos ht _).le hov htile hbuf
      (fun k => q.stepRow t r cols k) (fun k hk hpv => (step_none hwf hk hpv).2.2 cols)
      (fun k hk x hpv i => by
        rw [← hexpu]
        have h3 := htails.rows k hk x hpv i
        rcases hcols with rfl | rfl
        · rw [Real.norm_eq_abs]; linarith [abs_nonneg (q.stepRow t r res k i)]
        · rw [Real.norm_eq_abs]; linarith [abs_nonneg (q.stepRow t r Finset.univ k i)])
      (fun T i hi => by
        have := (hbud T).2.1 i hi
        rw [Real.norm_eq_abs]
        rcases hcols with rfl | rfl
        · simpa [Sequence.rowRecord, Finset.sum_apply] using this.1
        · simpa [Sequence.rowRecord, Finset.sum_apply] using this.2) i
    have h2 := (hTAIL1 i).trans (hTAIL (delta / 2000) (by norm_num [delta]))
    have e : q.rowRecord t r cols (Finset.range q.length) i =
        ∑ k ∈ Finset.range q.length, q.stepRow t r cols k i := by
      simp [Sequence.rowRecord, Finset.sum_apply]
    rw [e, ← Real.norm_eq_abs]; linarith
  -- smallness for validity
  have hp40 : C' * power t (delta / 40) ≤ 1 := by
    have := hs2 t ht htt2
    rw [lt_div_iff₀ hC'pos] at this; linarith
  have hp2000 : C' * power t (delta / 2000) ≤ 1 / 4 := by
    have := hs3 t ht htt3
    rw [lt_div_iff₀ (by positivity)] at this; linarith
  have hp50 : C' * power t (delta / 50) ≤ 1 := by
    have := hs4 t ht htt4
    rw [lt_div_iff₀ hC'pos] at this; linarith
  have hpw : ∀ e, 0 ≤ power t e := fun e => (Real.rpow_pos_of_pos ht _).le
  have hrc : 0 ≤ rowCap t := hpw _
  have e8 : power t (delta / 8) = power t (delta / 40) * power t (delta / 10) := by
    rw [← power_split ht]; norm_num [delta]
  have e44 : power t (11 * delta / 25) = power t (delta / 50) * power t S45.beta := by
    rw [← power_split ht]; norm_num [delta, S45.beta]
  -- formAbsLe monotonicity
  have hLmono : ∀ a', CL * power t (delta / 8) ≤ a' →
      formAbsLe (qform (q.Lrecord t r (Finset.range q.length))) (qform D0) a' := by
    intro a' ha' f
    have h := hLpart f
    have hpos : 0 < CL * power t (delta / 8) := by
      have := Real.rpow_pos_of_pos ht (delta / 8); positivity
    have hR0 : 0 ≤ qform D0 f := by
      by_contra hneg
      push_neg at hneg
      have : CL * power t (delta / 8) * qform D0 f < 0 := mul_neg_of_pos_of_neg hpos hneg
      linarith [abs_nonneg (qform (q.Lrecord t r (Finset.range q.length)) f)]
    exact h.trans (mul_le_mul_of_nonneg_right ha' hR0)
  -- scalar records
  have hlag0 : ∀ i ∈ (q.state 0).live, (q.state 0).ambientLag t r i = 0 := fun i _ => hu0 i
  refine ⟨hJ.trans (mul_le_mul_of_nonneg_right hC1 (hpw _)),
    hLmono _ (mul_le_mul_of_nonneg_right hCLle (hpw _)),
    fun i => (hlag i).trans (mul_le_mul_of_nonneg_right hC1 (hpw _)),
    fun i => ⟨(hrowb _ (Or.inl rfl) i).trans (mul_le_mul_of_nonneg_right hC1 (hpw _)),
      (hrowb _ (Or.inr rfl) i).trans (mul_le_mul_of_nonneg_right hC1 (hpw _))⟩,
    ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- J validity
    refine hJ.trans ?_
    rw [e8]
    have : (C + 1) * power t (delta / 40) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_right hC1 (hpw _)) hp40
    nlinarith [hpw (delta / 10), hpw (delta / 40)]
  · refine hLmono _ ?_
    rw [e8]
    have : CL * power t (delta / 40) ≤ 1 := le_trans (mul_le_mul_of_nonneg_right hCLle (hpw _)) hp40
    nlinarith [hpw (delta / 10), hpw (delta / 40)]
  · -- rows on live
    intro i
    have hsr' := (hsr (Fin n) q t r Finset.univ ht hwf hlag0 i.1 i.2).2
    rw [hlive0, Finset.univ_inter, Finset.univ_inter] at hsr'
    have e1 : ((q.state q.length).state r).fourthRow t Finset.univ i =
        ∑ j ∈ (q.state q.length).live, ‖((q.state q.length).ambient r).h t i j‖ ^ 4 := by
      simp only [State.fourthRow]
      rw [← Finset.sum_coe_sort (q.state q.length).live]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ambient_h_live _ r t i.2 j.2]
    have h0 := hrow0 i.1
    simp only [State.fourthRow] at h0
    have hrr := hrowb Finset.univ (Or.inl rfl) i.1
    have hrr' : q.rowRecord t r Finset.univ (Finset.range q.length) i ≤ (C + 1) * power t (delta / 2000) :=
      (le_abs_self _).trans hrr
    have hc1 : (C + 1) * power t (delta / 2000) ≤ 1 / 4 :=
      le_trans (mul_le_mul_of_nonneg_right hC1 (hpw _)) hp2000
    rw [e1]
    calc _ ≤ _ := hsr'
      _ ≤ 3 / 4 * rowCap t + rowCap t * ((C + 1) * power t (delta / 2000)) :=
          add_le_add h0 (mul_le_mul_of_nonneg_left hrr' hrc)
      _ ≤ 3 / 4 * rowCap t + rowCap t * (1 / 4) := by
          nlinarith [mul_le_mul_of_nonneg_left hc1 hrc]
      _ = rowCap t := by ring
  · -- lag on live
    intro i
    have hsr' := (hsr (Fin n) q t r Finset.univ ht hwf hlag0 i.1 i.2).1
    have e1 : (q.state q.length).ambientLag t r i.1 = ((q.state q.length).state r).lag t i := by
      simp [LiveState.ambientLag, i.2]
    rw [← e1, ← hsr']
    refine (hlag i.1).trans ?_
    rw [e44]
    have : (C + 1) * power t (delta / 50) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_right hC1 (hpw _)) hp50
    nlinarith [hpw S45.beta, hpw (delta / 50)]
  · -- reserve rows
    intro i hi
    obtain ⟨hires, hilive⟩ := Finset.mem_inter.1 hi
    have hsr' := (hsr (Fin n) q t r res ht hwf hlag0 i hilive).2
    rw [hlive0, Finset.inter_univ] at hsr'
    have e1 : ((q.state q.length).ambient r).fourthRow t res i =
        ∑ j ∈ res ∩ (q.state q.length).live, ‖((q.state q.length).ambient r).h t i j‖ ^ 4 := by
      simp only [State.fourthRow]
      rw [← Finset.sum_filter_add_sum_filter_not res (· ∈ (q.state q.length).live)]
      rw [Finset.sum_eq_zero (s := res.filter fun j => j ∉ (q.state q.length).live) (fun j hj => by
        rw [ambient_h_dead _ r t i (Finset.mem_filter.1 hj).2]; simp), add_zero]
      rw [Finset.filter_mem_eq_inter]
    have h0 := hres0 i hires
    have hrr := hrowb res (Or.inr rfl) i
    have hrr' : q.rowRecord t r res (Finset.range q.length) i ≤ C' * power t (delta / 2000) :=
      ((le_abs_self _).trans hrr).trans (mul_le_mul_of_nonneg_right hC1 (hpw _))
    rw [e1]
    calc _ ≤ _ := hsr'
      _ ≤ θ ^ 2 * rowCap t + rowCap t * (C' * power t (delta / 2000)) :=
          add_le_add h0 (mul_le_mul_of_nonneg_left hrr' hrc)
      _ = (θ ^ 2 + C' * power t (delta / 2000)) * rowCap t := by ring

end AndersonAC.AgentS45
