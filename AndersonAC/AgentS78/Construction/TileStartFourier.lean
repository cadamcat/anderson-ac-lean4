import AndersonAC.AgentS78.Construction.TileStartLift
import AndersonAC.AgentS78.InitialComparison
import AndersonAC.S3.ChargeEstimate
import AndersonAC.S3Circ.Circulant

/-!
# WP10 tile phase: Fourier and volume clauses of the duplicated stage start

agent-s78start (2026-10-14). `Λ⁺_Σ(y) = Λ⁺(y_Σ)` on neutral live port charges obeys the
§3 charge estimate `Λ⁺(y_Σ) ≤ C ‖y‖₁^{4/3} ‖y‖₂^{2/3}` (Lemma 3.2, two ports per site), and
the live port count is at least `t^{-(1+δ+κ)}` (the `Prestate.volume` clause).
-/

noncomputable section
set_option autoImplicit false

open scoped BigOperators

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

/-- Torus inverse gradient energy `Λ⁺`. -/
abbrev LamPlus (d m : ℕ) : (Torus d m → ℝ) → ℝ :=
  inverseEnergy Finset.univ (gradientEnergy (nnGraph d m))

/-- The site charge of a live port charge, on the torus. -/
def liveSiteCharge (z : RunRecord d m) (y : liveStart z → ℝ) : Torus d m → ℝ :=
  fun i => ∑ x : liveStart z, if x.1.1 = i then y x else 0

theorem extend_sumCharge (θ : ℝ) (z : RunRecord d m) (y : liveStart z → ℝ) :
    extendFun (actEquiv z) ((livePortMap θ z).sumCharge y) = liveSiteCharge z y := by
  funext i
  unfold extendFun liveSiteCharge S45.PortMap.sumCharge
  split_ifs with hi
  · refine Finset.sum_congr rfl fun x _ => ?_
    simp [livePortMap_site_eq_iff]
  · symm
    refine Finset.sum_eq_zero fun x _ => ?_
    have : x.1.1 ≠ i := fun h => hi (h ▸ mem_liveStart_iff.mp x.2)
    simp [this]

theorem liveSiteCharge_sum (z : RunRecord d m) (y : liveStart z → ℝ) :
    ∑ i, liveSiteCharge z y i = ∑ x, y x := by
  unfold liveSiteCharge
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp

theorem liveSiteCharge_cx (z : RunRecord d m) (y : liveStart z → ℝ) :
    cx (liveSiteCharge z y) =
      AndersonAC.S3.siteSum (d := d) (L := OAI.Anderson.sideLength m)
        (fun x : liveStart z => x.1.1) (cx y) := by
  funext i
  unfold cx liveSiteCharge AndersonAC.S3.siteSum
  rw [Finset.sum_filter]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

theorem live_atMostTwo (z : RunRecord d m) :
    AndersonAC.S3.atMostTwo (d := d) (L := OAI.Anderson.sideLength m)
      (fun x : liveStart z => x.1.1) := by
  intro i
  calc (Finset.univ.filter (fun x : liveStart z => x.1.1 = i)).card
      ≤ (Finset.univ : Finset Bool).card := by
        refine Finset.card_le_card_of_injOn (fun x => x.1.2) (fun _ _ => Finset.mem_univ _) ?_
        intro x hx x' hx' h
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx hx'
        exact Subtype.ext (Prod.ext (hx.trans hx'.symm) h)
    _ = 2 := rfl

/-- **Fourier clause** of the stage-start prestate (Lemma 3.2 with two ports per site). -/
theorem live_fourier (hd : 3 ≤ d) : ∃ C > 0, ∀ (m : ℕ), 0 < m → ∀ (z : RunRecord d m)
    (θ : ℝ) (y : liveStart z → ℝ), S45.neutral y →
    LamPlus d m (extendFun (actEquiv z) ((livePortMap θ z).sumCharge y)) ≤
      C * S45.power (S45.l1 y) (4 / 3) * S45.power (S45.l2sq y) (1 / 3) := by
  obtain ⟨C, hC, hF⟩ := AndersonAC.S3.fourier_charge_of AndersonAC.S3.circulantCalculus_proof hd
  refine ⟨C, hC, fun m hm z θ y hy => ?_⟩
  rw [extend_sumCharge]
  have hsum : ∑ i, liveSiteCharge z y i = 0 := by rw [liveSiteCharge_sum]; exact hy
  show inverseEnergy Finset.univ (gradientEnergy (nnGraph d m)) (liveSiteCharge z y) ≤ _
  rw [lambda_eq_laplacianPlus hm _ hsum, liveSiteCharge_cx]
  have h := hF (OAI.Anderson.sideLength m) (sideLength_ge_four hm) (liveStart z)
    (fun x : liveStart z => x.1.1) (live_atMostTwo z) (cx y)
  have h1 : AndersonAC.S3.normOne (cx y) = S45.l1 y := by
    unfold AndersonAC.S3.normOne S45.l1 cx
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.norm_real]
  have h2 : AndersonAC.S3.normSq (cx y) = S45.l2sq y := by
    unfold AndersonAC.S3.normSq S45.l2sq cx
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.norm_real]
  rw [h1, h2] at h
  have h3 : Real.rpow (Real.sqrt (S45.l2sq y)) (2 / 3) = S45.power (S45.l2sq y) (1 / 3) := by
    have h0 : 0 ≤ S45.l2sq y := Finset.sum_nonneg fun _ _ => by positivity
    unfold S45.power
    rw [Real.sqrt_eq_rpow]
    change (S45.l2sq y ^ (1 / 2 : ℝ)) ^ (2 / 3 : ℝ) = S45.l2sq y ^ (1 / 3 : ℝ)
    rw [← Real.rpow_mul h0]; norm_num
  rw [h3] at h
  exact h

theorem liveStart_card_ge (z : RunRecord d m) :
    z.endpoint.active.card ≤ (liveStart z).card := by
  refine Finset.card_le_card_of_injOn (fun i => ((i, false) : Port d m)) ?_ ?_
  · intro i hi; exact mem_liveStart_iff.mpr hi
  · intro i _ i' _ h; exact congrArg Prod.fst h

theorem torus_card (d m : ℕ) : (Fintype.card (Torus d m) : ℝ) = (4 : ℝ) ^ (20 * m * d) := by
  rw [show Fintype.card (Torus d m) = (OAI.Anderson.sideLength m) ^ d by
    simp [Fintype.card_fun, ZMod.card]]
  unfold OAI.Anderson.sideLength
  push_cast
  rw [← pow_mul]

/-- **Volume clause** of the stage-start prestate: `1/|P₀| ≤ t^{1+δ+κ}` for the live ports. -/
theorem live_volume (hd : 3 ≤ d) (hm : 0 < m) (z : RunRecord d m)
    (hcount : Fintype.card (Torus d m) ≤ 2 * z.endpoint.active.card) {t : ℝ}
    (ht1 : t ≤ 1) (htlow : 1 / (4 : ℝ) ^ (m + 1) ≤ t) :
    1 / (Fintype.card (liveStart z) : ℝ) ≤
      1 * S45.power t (1 + S45.delta + S45.kappa) := by
  have hN := torus_card d m
  have hA : (Fintype.card (Torus d m) : ℝ) ≤ 2 * (liveStart z).card := by
    have := liveStart_card_ge z
    exact_mod_cast hcount.trans (by omega)
  have hpos4 : (0 : ℝ) < (4 : ℝ) ^ (m + 1) := by positivity
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) htlow
  rw [Fintype.card_coe, one_mul]
  have hLpos : (0 : ℝ) < (liveStart z).card := by
    have : (0 : ℝ) < Fintype.card (Torus d m) := by rw [hN]; positivity
    linarith
  -- t^{1+δ+κ} ≥ t^2 ≥ 4^{-2(m+1)}
  have hexp : S45.power t 2 ≤ S45.power t (1 + S45.delta + S45.kappa) := by
    unfold S45.power
    apply Real.rpow_le_rpow_of_exponent_ge ht0 ht1
    norm_num [S45.delta, S45.kappa]
  have ht2 : S45.power t 2 = t ^ 2 := by
    show t ^ (2:ℝ) = t ^ 2; exact Real.rpow_two t
  have hlow2 : (1 / (4 : ℝ) ^ (m + 1)) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by positivity) htlow 2
  have hbig : 2 * (4 : ℝ) ^ (2 * (m + 1)) ≤ (4 : ℝ) ^ (20 * m * d) := by
    have h1 : 2 * (m + 1) + 1 ≤ 20 * m * d := by nlinarith
    calc 2 * (4 : ℝ) ^ (2 * (m + 1)) ≤ 4 * (4 : ℝ) ^ (2 * (m + 1)) := by
          have : (0:ℝ) ≤ (4 : ℝ) ^ (2 * (m + 1)) := by positivity
          linarith
      _ = (4 : ℝ) ^ (2 * (m + 1) + 1) := by ring
      _ ≤ (4 : ℝ) ^ (20 * m * d) := pow_le_pow_right₀ (by norm_num) h1
  calc 1 / ((liveStart z).card : ℝ) ≤ 2 / (4 : ℝ) ^ (20 * m * d) := by
        rw [div_le_div_iff₀ hLpos (by positivity)]; rw [← hN]; linarith
    _ ≤ (1 / (4 : ℝ) ^ (m + 1)) ^ 2 := by
        rw [div_pow, one_pow, ← pow_mul, div_le_div_iff₀ (by positivity) (by positivity),
          show (m + 1) * 2 = 2 * (m + 1) by ring]
        linarith [hbig]
    _ ≤ t ^ 2 := hlow2
    _ = S45.power t 2 := ht2.symm
    _ ≤ _ := hexp

end AndersonAC.AgentS78
