import AndersonAC.AgentS78.Construction.TileCoverMulti

/-!
# the §5 tile covers — assembly. `TileCoverStatement d` from the analytic sub-statements of
TileCoverParts.lean (grid Poincaré, torus connectivity, metric, shell and kernel bounds).
Tile side `L = 4^k` with `k` least such that `t^{-6} ≤ 4^k` (so `L ≤ 64 t^{-6}` for `t ≤ 2`);
the cube tiling when `5L ≤ N`, else one tile (then `N < 5L ≤ 320 t^{-6}`).
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

theorem statement_body_of_axioms {d m : ℕ} {t : ℝ} {τ : TorusTiling d m} {B ℓ Pc D C Cs Ck : ℝ}
    (hτ : TilingAxioms τ t (5 ^ d + 50 * d) B ℓ Pc)
    (hconn : (nnGraph d m).Connected)
    (hshell : ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ x : Torus d m,
      (∑ y, Real.exp (-u * physicalDistance d m x y)) ≤ Cs * S45.power u (-(d : ℝ)) ∧
      (∑ y, physicalDistance d m x y ^ 2 * Real.exp (-u * physicalDistance d m x y)) ≤
        Cs * S45.power u (-(d : ℝ) - 2))
    (hker : ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ v : Torus d m → ℝ,
      (∑ x, ∑ y, Real.exp (-u * physicalDistance d m x y) * (v x - v y) ^ 2) ≤
        Ck * S45.power u (-(d : ℝ) - 2) * torusEnergy d m v)
    (hdiam : ∀ T, ∀ x ∈ τ.tile T, ∀ y ∈ τ.tile T, physicalDistance d m x y ≤ D)
    (hB : 3 * B ≤ C * S45.power t (-6 * (d : ℝ))) (hD : D ≤ C * S45.power t (-6))
    (hCA : 5 ^ d + 50 * d ≤ C) (hC1 : 2 + 4 * d * (5 ^ d + 50 * d) ≤ C)
    (hC2 : 8 * Cs + 4 * Ck ≤ C) (hC3 : 2 * Cs ≤ C) (hCs : 0 ≤ Cs) (hCk : 0 ≤ Ck) :
    (∀ x, ∃! T, x ∈ τ.tile T) ∧
      (∀ T, ((τ.tile T).card : ℝ) ≤ C * S45.power t (-6 * (d : ℝ))) ∧
      (∀ T, ((τ.inner T).card : ℝ) ≤ C * S45.power t (-6 * (d : ℝ))) ∧
      (∀ T, ∀ x ∈ τ.tile T, ∀ y ∈ τ.tile T,
        physicalDistance d m x y ≤ C * S45.power t (-6)) ∧
      ∀ (P : Type) [Fintype P] [DecidableEq P] (ι : P → Port d m), Function.Injective ι →
        S45.ShellBounds d C (pullDist ι) ∧
        ∀ b : ℝ, 0 < b →
          ∃ cov : S45.TileCover (P := P) (I := Torus d m) d t b C (pullDist ι),
            cov.site = (fun x => (ι x).1) ∧ cov.energy = torusEnergy d m ∧
            ∃ e : Fin cov.count ≃ Fin τ.count,
              (∀ T x, x ∈ cov.tile T ↔ (ι x).1 ∈ τ.tile (e T)) ∧
              (∀ T x, x ∈ cov.inner T ↔ (ι x).1 ∈ τ.inner (e T)) ∧
              (∀ T, ((cov.inner T).card : ℝ) ≤ C * S45.power t (-6 * (d : ℝ))) := by
  obtain ⟨T₀, -, -⟩ := hτ.partition 0
  have hB0 : 0 ≤ B := le_trans (by positivity) (hτ.outer_card T₀)
  have hBC : B ≤ C * S45.power t (-6 * (d : ℝ)) := by linarith
  have hinnerB : ∀ T, ((τ.inner T).card : ℝ) ≤ B := fun T =>
    le_trans (by exact_mod_cast Finset.card_le_card (hτ.inner_outer T)) (hτ.outer_card T)
  refine ⟨hτ.partition, fun T => ?_, fun T => (hinnerB T).trans hBC,
    fun T x hx y hy => (hdiam T x hx y hy).trans hD, fun P _ _ ι hι => ⟨?_, fun b hb => ?_⟩⟩
  · exact le_trans (by exact_mod_cast Finset.card_le_card (hτ.tile_inner T)) ((hinnerB T).trans hBC)
  · refine
      { nonneg := fun i j => Nat.cast_nonneg _
        symmetric := fun i j => by simp only [pullDist, physicalDistance, SimpleGraph.dist_comm]
        triangle := fun i j k => by
          simp only [pullDist, physicalDistance]
          exact_mod_cast hconn.dist_triangle
        self := fun i => by simp [pullDist, physicalDistance]
        count := fun u hu hu1 i => ?_
        second := fun u hu hu1 i => ?_ }
    · have h1 := sum_port_le ι hι (fun y => Real.exp (-u * physicalDistance d m (ι i).1 y))
        (fun y => (Real.exp_pos _).le)
      have h2 := (hshell u hu hu1 (ι i).1).1
      have hp : 0 ≤ S45.power u (-(d : ℝ)) := Real.rpow_nonneg hu.le _
      have h3 : 2 * (Cs * S45.power u (-(d : ℝ))) ≤ C * S45.power u (-(d : ℝ)) := by
        nlinarith
      exact h1.trans (by linarith)
    · have h1 := sum_port_le ι hι (fun y => physicalDistance d m (ι i).1 y ^ 2 *
        Real.exp (-u * physicalDistance d m (ι i).1 y))
        (fun y => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      have h2 := (hshell u hu hu1 (ι i).1).2
      have hp : 0 ≤ S45.power u (-(d : ℝ) - 2) := Real.rpow_nonneg hu.le _
      have h3 : 2 * (Cs * S45.power u (-(d : ℝ) - 2)) ≤ C * S45.power u (-(d : ℝ) - 2) := by
        nlinarith
      exact h1.trans (by linarith)
  · obtain ⟨cov, h1, h2, e, h3, h4, h5⟩ := hτ.exists_cover hconn
      (fun u hu hu1 x => (hshell u hu hu1 x).1) hker hCA hC1 hB hC2 hCs hCk ι hι b hb
    exact ⟨cov, h1, h2, e, h3, h4, fun T => (h5 T).trans (by linarith)⟩

/-- **The §5 tile covers**, from the analytic sub-statements. -/
theorem tileCover_of_parts (hGP : GridPoincareStatement) (hconn : TorusConnectedStatement)
    (hMet : TorusMetricStatement) (d : ℕ) (hsh : TorusShellStatement d)
    (hker : TorusKernelStatement d) : TileCoverStatement d := by
  classical
  obtain ⟨Cs, hCs, hshell⟩ := hsh
  obtain ⟨Ck, hCk, hkern⟩ := hker
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h5d : (1 : ℝ) ≤ 5 ^ d := one_le_pow₀ (by norm_num)
  have h320 : (0 : ℝ) ≤ 320 ^ d := by positivity
  set A : ℝ := 5 ^ d + 50 * d with hA
  have hA1 : 1 ≤ A := by rw [hA]; linarith
  set C : ℝ := 3 * 320 ^ d + 2 + 4 * d * A + A + 8 * Cs + 4 * Ck + 320 * d + 1 with hC
  have hdA : 0 ≤ 4 * d * A := by positivity
  refine ⟨C, by rw [hC]; linarith, ?_⟩
  intro m t ht0 ht2
  set s := S45.power t (-6) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos ht0 _
  have hs64 : 1 / 64 ≤ s := by
    have := Real.rpow_le_rpow_of_nonpos ht0 ht2 (by norm_num : (-6 : ℝ) ≤ 0)
    have h2 : (2 : ℝ) ^ (-6 : ℝ) = 1 / 64 := by
      rw [Real.rpow_neg (by norm_num)]; norm_num
    rw [h2] at this; exact this
  have hpow : S45.power t (-6 * (d : ℝ)) = s ^ d := by
    rw [hs]
    show t ^ ((-6 : ℝ) * d) = (t ^ (-6 : ℝ)) ^ d
    rw [Real.rpow_mul ht0.le, Real.rpow_natCast]
  have hex : ∃ k : ℕ, s ≤ 4 ^ k := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt s (by norm_num : (1 : ℝ) < 4)
    exact ⟨k, hk.le⟩
  set k₀ := Nat.find hex with hk₀def
  have hk₀ : s ≤ 4 ^ k₀ := Nat.find_spec hex
  have hk₀' : (4 : ℝ) ^ k₀ ≤ 64 * s := by
    rcases Nat.eq_zero_or_pos k₀ with h | h
    · rw [h]; simp; linarith
    · have hmin := Nat.find_min hex (Nat.sub_lt h one_pos)
      push Not at hmin
      have : (4 : ℝ) ^ k₀ = 4 * 4 ^ (k₀ - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [← hk₀def] at hmin
      linarith
  set L : ℕ := 4 ^ k₀ with hLdef
  have hLr : (L : ℝ) = 4 ^ k₀ := by rw [hLdef]; push_cast; rfl
  have hL0 : 0 < L := by positivity
  have hshell' := hshell m
  have hkern' := hkern m
  have hCA : A ≤ C := by rw [hC]; linarith
  have hC1 : 2 + 4 * d * A ≤ C := by rw [hC]; linarith
  have hC2 : 8 * Cs + 4 * Ck ≤ C := by rw [hC]; linarith
  have hC3 : 2 * Cs ≤ C := by rw [hC]; linarith
  have hsd : 0 ≤ s ^ d := by positivity
  have h3B : ∀ B : ℝ, B ≤ (320 * s) ^ d → 3 * B ≤ C * S45.power t (-6 * (d : ℝ)) := by
    intro B hB
    rw [hpow, mul_pow] at *
    have : 3 * (320 ^ d * s ^ d) ≤ C * s ^ d := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (by rw [hC]; linarith) hsd
    linarith
  have hDC : ∀ D : ℝ, D ≤ 320 * d * s → D ≤ C * S45.power t (-6) := by
    intro D hD
    rw [← hs]
    have : 320 * d * s ≤ C * s := mul_le_mul_of_nonneg_right (by rw [hC]; linarith) hs0.le
    linarith
  by_cases hreg : 5 * L ≤ OAI.Anderson.sideLength m
  · -- the cube tiling
    have hk20 : k₀ ≤ 20 * m := by
      have : 4 ^ k₀ ≤ 4 ^ (20 * m) := by
        have h := hreg
        unfold OAI.Anderson.sideLength at h
        rw [hLdef] at h
        omega
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
    obtain ⟨M, hM⟩ : L ∣ OAI.Anderson.sideLength m := by
      rw [hLdef]; unfold OAI.Anderson.sideLength; exact pow_dvd_pow 4 hk20
    have hML : OAI.Anderson.sideLength m = M * L := by rw [hM, mul_comm]
    have h5 : 5 ≤ M := by
      rw [hML] at hreg
      exact Nat.le_of_mul_le_mul_right hreg hL0
    have hτ := multi_axioms (m := m) (d := d) M L hML hL0 h5 hGP hMet t (by rw [hLr]; exact hk₀)
    refine ⟨multiTiling M L, statement_body_of_axioms hτ (hconn d m) hshell' hkern'
      (fun T x hx y hy => multi_diam (m := m) M L hML hL0 h5 hMet T x y hx hy)
      (h3B _ ?_) (hDC _ ?_) hCA hC1 hC2 hC3 hCs.le hCk.le⟩
    · have : ((5 * L : ℕ) : ℝ) ≤ 320 * s := by push_cast; rw [hLr]; linarith
      exact pow_le_pow_left₀ (by positivity) this d
    · rw [hLr]
      have : (d : ℝ) * 4 ^ k₀ ≤ d * (64 * s) := mul_le_mul_of_nonneg_left hk₀' hd0
      nlinarith
  · -- one tile
    push Not at hreg
    have hτ := single_axioms (m := m) (d := d) hGP t
    have hN : (OAI.Anderson.sideLength m : ℝ) ≤ 320 * s := by
      have : ((OAI.Anderson.sideLength m : ℕ) : ℝ) ≤ ((5 * L : ℕ) : ℝ) := by
        exact_mod_cast hreg.le
      push_cast at this; rw [hLr] at this; linarith
    refine ⟨singleTiling, statement_body_of_axioms hτ (hconn d m) hshell' hkern'
      (D := d * OAI.Anderson.sideLength m) ?_ (h3B _ ?_) (hDC _ ?_) hCA hC1 hC2 hC3 hCs.le hCk.le⟩
    · intro T x _ y _
      rw [hMet]
      have : l1Dist x y ≤ d * OAI.Anderson.sideLength m := by
        unfold l1Dist circDist
        calc ∑ k, min (y k - x k).val (OAI.Anderson.sideLength m - (y k - x k).val)
            ≤ ∑ _k : Fin d, OAI.Anderson.sideLength m :=
              Finset.sum_le_sum fun k _ => (min_le_left _ _).trans (ZMod.val_lt _).le
          _ = d * OAI.Anderson.sideLength m := by simp
      exact_mod_cast this
    · exact pow_le_pow_left₀ (by positivity) hN d
    · exact mul_le_mul_of_nonneg_left hN hd0 |>.trans (by nlinarith)

end AndersonAC.AgentS78
