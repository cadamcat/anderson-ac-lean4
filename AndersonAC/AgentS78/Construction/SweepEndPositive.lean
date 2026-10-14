import AndersonAC.S45.CumulativeSchurProof
import AndersonAC.S45.SweepEndpointProof
import AndersonAC.S45.SchurProof
import AndersonAC.AgentS78.Construction.TileCoreA3

/-!
# Per-step positivity along a valid sweep (generic port type)

 . The hypothesis of `S45.ordinary_sweep_endpoint`

  `∀ k < q.length, ∀ x live, 1 − K_xx ≠ 0 ∧ 0 < q_x − p_x F_xx`

follows, for any sequence starting from all ports with `‖K₀‖ ≤ 1/2`, broad damping bounds and
symmetric/Ward prefix states, from the validity of every prefix (05:155–239, the cumulative
Schur identity of Lemma `cumulative-schur`; the same argument as
`prefix_schur_and_bounds` for tile prefixes, here for an arbitrary port type, so that it
applies to the transported sweep on `initialPorts (Fin n)`).
-/

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78send

open AndersonAC.S45

section Helpers
variable {P : Type*} [Fintype P] [DecidableEq P]

theorem seq_truncate_wellFormed {q : Sequence P} {t : ℝ} {r : P → ℂ}
    (hq : q.wellFormed t r) {s : ℕ} (hs : s ≤ q.length) :
    ({ q with length := s } : Sequence P).wellFormed t r :=
  ⟨fun k hk => hq.1 k (hk.trans hs), fun k hk => hq.2 k (lt_of_lt_of_le hk hs)⟩

/-- `L ≃ Lᶜᶜ` as subtypes. -/
def complComplEquiv (L : Finset P) : L ≃ (↑(Lᶜᶜ) : Type _) where
  toFun i := ⟨i.1, Finset.mem_compl.mpr (fun h => (Finset.mem_compl.mp h) i.2)⟩
  invFun j := ⟨j.1, by
    by_contra h
    exact (Finset.mem_compl.mp j.2) (Finset.mem_compl.mpr h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem K_submatrix_of_pad_schur (L : Finset P) (K : Matrix L L ℂ) (A : CMat P)
    (hpad : pad L (1 - K) = pad Lᶜᶜ (schur A Lᶜ)) :
    K = (1 - schur A Lᶜ).submatrix (complComplEquiv L) (complComplEquiv L) := by
  ext i j
  have h1 := congrFun (congrFun hpad i.1) j.1
  have hicc : i.1 ∈ Lᶜᶜ := (complComplEquiv L i).2
  have hjcc : j.1 ∈ Lᶜᶜ := (complComplEquiv L j).2
  rw [AgentS45.pad_apply_mem L (1 - K) i.2 j.2,
    AgentS45.pad_apply_mem Lᶜᶜ (schur A Lᶜ) hicc hjcc] at h1
  simp only [Matrix.sub_apply, Matrix.one_apply, submatrix_apply, complComplEquiv,
    Equiv.coe_fn_mk, Subtype.mk.injEq] at h1 ⊢
  linear_combination -h1

theorem norm_K_le_of_pad_schur (L : Finset P) (K : Matrix L L ℂ) (B : CMat P) (ρ : ℝ)
    (hρ : 0 ≤ ρ ∧ ρ < 1) (hB : ‖B‖ ≤ ρ)
    (hpad : pad L (1 - K) = pad Lᶜᶜ (schur (1 - B) Lᶜ)) :
    ‖K‖ ≤ ρ := by
  have hcon := (AgentS45.schur_contraction_proof B Lᶜ ρ hρ hB).2
  have hsub := K_submatrix_of_pad_schur L K (1 - B) hpad
  rw [hsub, AgentS45.norm_submatrix_equiv]
  exact hcon

theorem F_diag_le_sqrt_of_row_cap {ι : Type*} [Fintype ι] [DecidableEq ι]
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (s : State ι) (i : ι)
    (hrow : s.fourthRow t Finset.univ i ≤ rowCap t) :
    s.F t i i ≤ Real.sqrt t := by
  have hfour : ‖s.h t i i‖ ^ 4 ≤ rowCap t :=
    (Finset.single_le_sum (fun j _ => pow_nonneg (norm_nonneg _) 4)
      (Finset.mem_univ i)).trans hrow
  have hcap : rowCap t ≤ t := by
    calc rowCap t = power t (1 + delta) := rfl
      _ ≤ power t 1 :=
        Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num [delta])
      _ = t := Real.rpow_one t
  have hsq : (s.F t i i) ^ 2 ≤ (Real.sqrt t) ^ 2 := by
    rw [Real.sq_sqrt ht.le]
    have hF : (s.F t i i) ^ 2 = ‖s.h t i i‖ ^ 4 := by
      simp only [State.F, entryAbsSquare]
      ring
    rw [hF]
    exact hfour.trans hcap
  have hF0 : 0 ≤ s.F t i i := by simp [State.F, entryAbsSquare]
  exact (sq_le_sq₀ hF0 (Real.sqrt_nonneg t)).mp hsq

end Helpers

/-- Smallness of the scale needed by `seq_step_positive`. -/
def PositiveScale (C t : ℝ) : Prop :=
  0 < t ∧ t ≤ 1 ∧ power t (delta / 10) ≤ 1 / 4 ∧ power t beta / (1 / C) ≤ 1 / 2 ∧
    2 * (1 + C ^ 2) * power t beta ≤ 1 / (2 * C) ∧ C * Real.sqrt t < 1 / (2 * C)

theorem exists_positiveScale (C : ℝ) (hC : 1 ≤ C) :
    ∃ t0 > 0, ∀ t, 0 < t → t < t0 → PositiveScale C t := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  obtain ⟨t1, ht1, h1⟩ := AgentS45.power_small (e := delta / 10)
    (by norm_num [delta]) (a := 1 / 4) (by norm_num)
  obtain ⟨t2, ht2, h2⟩ := AgentS45.power_small (e := beta)
    (by norm_num [beta, delta]) (a := 1 / (4 * C * (1 + C ^ 2))) (by positivity)
  obtain ⟨t3, ht3, h3⟩ := AgentS45.power_small (e := 1 / 2)
    (by norm_num) (a := 1 / (36 * C ^ 2)) (by positivity)
  refine ⟨min 1 (min t1 (min t2 t3)), lt_min one_pos (lt_min ht1 (lt_min ht2 ht3)),
    fun t ht htt => ?_⟩
  have htt1 : t < t1 := lt_of_lt_of_le htt ((min_le_right _ _).trans (min_le_left _ _))
  have htt2 : t < t2 := lt_of_lt_of_le htt
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have htt3 : t < t3 := lt_of_lt_of_le htt
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hp1 : power t (delta / 10) ≤ 1 / 4 := (h1 t ht htt1).le
  have hp2 := h2 t ht htt2
  have hp3 := h3 t ht htt3
  have hsqrt : Real.sqrt t = power t (1 / 2) := Real.sqrt_eq_rpow t
  have hC2 : 1 ≤ C ^ 2 := by nlinarith
  refine ⟨ht, (lt_of_lt_of_le htt (min_le_left _ _)).le, hp1, ?_, ?_, ?_⟩
  · rw [div_div_eq_mul_div, div_one]
    have hle : C * power t beta ≤ C * (1 / (4 * C * (1 + C ^ 2))) :=
      mul_le_mul_of_nonneg_left hp2.le hCpos.le
    have heq : C * (1 / (4 * C * (1 + C ^ 2))) = 1 / (4 * (1 + C ^ 2)) := by
      field_simp
    have h4 : 1 / (4 * (1 + C ^ 2)) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  · have hle : 2 * (1 + C ^ 2) * power t beta ≤
        2 * (1 + C ^ 2) * (1 / (4 * C * (1 + C ^ 2))) :=
      mul_le_mul_of_nonneg_left hp2.le (by positivity)
    have heq : 2 * (1 + C ^ 2) * (1 / (4 * C * (1 + C ^ 2))) = 1 / (2 * C) := by
      field_simp; ring
    linarith
  · rw [hsqrt]
    have hlt : C * power t (1 / 2) < C * (1 / (36 * C ^ 2)) :=
      mul_lt_mul_of_pos_left hp3 hCpos
    have heq : C * (1 / (36 * C ^ 2)) = 1 / (36 * C) := by field_simp
    have h36 : 1 / (36 * C) ≤ 1 / (2 * C) :=
      div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith)
    linarith

/-- **Per-step positivity along a valid sequence** (generic port type). -/
theorem seq_step_positive {P : Type*} [Fintype P] [DecidableEq P] (q : Sequence P) (t : ℝ)
    (r : P → ℂ) (D0 : RMat P) (C : ℝ) (hC : 1 ≤ C) (hscale : PositiveScale C t)
    (hwf : q.wellFormed t r) (hlive0 : (q.state 0).live = Finset.univ)
    (hK0 : ‖((q.state 0).ambient r).K t‖ ≤ 1 / 2)
    (hbroad : ∀ p, ‖r p‖ ≤ C ∧ 1 / C ≤ (r p).im ∧ (r p).im ≤ C)
    (hsw : ∀ k ≤ q.length, ((q.state k).state r).g.IsSymm ∧ ((q.state k).state r).ward t)
    (hval : ∀ k ≤ q.length, q.valid t r D0 k) :
    ∀ k < q.length, ∀ y : (q.state k).live,
      1 - ((q.state k).state r).K t y y ≠ 0 ∧
      0 < ((q.state k).state r).q y -
        ((q.state k).state r).p y * ((q.state k).state r).F t y y := by
  obtain ⟨htpos, ht1, hp1, hp2, hp3, hp4⟩ := hscale
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hrpos : ∀ p : P, 0 < (r p).im := fun p =>
    lt_of_lt_of_le (by positivity) (hbroad p).2.1
  -- the statement at every prefix `s ≤ q.length`, by strong induction
  have main : ∀ s ≤ q.length, ∀ p : (q.state s).live,
      1 - ((q.state s).state r).K t p p ≠ 0 ∧
      0 < ((q.state s).state r).q p -
        ((q.state s).state r).p p * ((q.state s).state r).F t p p := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro hs
      let qs : Sequence P := { q with length := s }
      have hqs_wf : qs.wellFormed t r := seq_truncate_wellFormed hwf hs
      have hstep : ∀ k < qs.length,
          ((qs.state k).state r).g.IsSymm ∧ ((qs.state k).state r).ward t ∧
          ∀ p : (qs.state k).live, 1 - ((qs.state k).state r).K t p p ≠ 0 ∧
            0 < ((qs.state k).state r).q p -
              ((qs.state k).state r).p p * ((qs.state k).state r).F t p p := by
        intro k hk
        change k < s at hk
        have hk_le : k ≤ q.length := hk.le.trans hs
        exact ⟨(hsw k hk_le).1, (hsw k hk_le).2, ih k hk hk_le⟩
      obtain ⟨hpadK, -⟩ := AgentS45.cumulative_schur_proof qs t r htpos hrpos hqs_wf hlive0 hstep
      change pad (q.state s).live (1 - ((q.state s).state r).K t) =
        pad (q.state s).liveᶜᶜ (schur (1 - ((q.state 0).ambient r).K t -
          q.Jrecord t r (Finset.range s)) (q.state s).liveᶜ) at hpadK
      let sk := (q.state s).state r
      have hvs := hval s hs
      let B := ((q.state 0).ambient r).K t + q.Jrecord t r (Finset.range s)
      have hB : ‖B‖ ≤ 3 / 4 := by
        calc ‖B‖ ≤ ‖((q.state 0).ambient r).K t‖ + ‖q.Jrecord t r (Finset.range s)‖ :=
              norm_add_le _ _
          _ ≤ 1 / 2 + power t (delta / 10) := add_le_add hK0 hvs.1
          _ ≤ 3 / 4 := by linarith
      have hpadK' : pad (q.state s).live (1 - sk.K t) =
          pad (q.state s).liveᶜᶜ (schur (1 - B) (q.state s).liveᶜ) := by
        rw [hpadK, show 1 - ((q.state 0).ambient r).K t - q.Jrecord t r (Finset.range s) =
          1 - B by simp [B]; abel]
      have hKnorm : ‖sk.K t‖ ≤ 3 / 4 :=
        norm_K_le_of_pad_schur (q.state s).live (sk.K t) B (3 / 4) ⟨by norm_num, by norm_num⟩
          hB hpadK'
      have hunit : IsUnit (1 - sk.K t) :=
        (Units.oneSub (sk.K t) (by linarith : ‖sk.K t‖ < 1)).isUnit
      have hsk_p : ∀ p : (q.state s).live, 1 / C ≤ sk.p p := fun p => (hbroad p.1).2.1
      have hsk_r : ∀ p : (q.state s).live, ‖sk.r p‖ ≤ C := fun p => (hbroad p.1).1
      have hβ0 : 0 ≤ power t beta := (Real.rpow_pos_of_pos htpos _).le
      have hdiag := AgentS45.diag_from_lag sk t (power t beta) (1 / C) C
        (hsw s hs).2 hunit hvs.2.2.2 (by positivity) hsk_p hsk_r hβ0 hp2
      intro p
      have hraw : ‖sk.rawLag p‖ ≤ 2 * (1 + C ^ 2) * power t beta := by
        have hd := hdiag p
        have heq : 2 * power t beta * (1 + C / (1 / C)) =
            2 * (1 + C ^ 2) * power t beta := by field_simp
        linarith
      have hKpp : 1 - sk.K t p p ≠ 0 := by
        intro h0
        have h1 : sk.K t p p = 1 := by linear_combination -h0
        have h2 : ‖sk.K t p p‖ ≤ 3 / 4 :=
          (AndersonAC.AgentS78.entry_le_l2 (sk.K t) p p).trans hKnorm
        rw [h1, norm_one] at h2
        linarith
      have hqp : |sk.q p - sk.p p| ≤ 2 * (1 + C ^ 2) * power t beta := by
        have him : sk.q p - sk.p p = (sk.rawLag p).im := by
          simp [State.q, State.p, State.rawLag]
        rw [him]
        exact (Complex.abs_im_le_norm _).trans hraw
      have hq_lo : 1 / (2 * C) ≤ sk.q p := by
        have hp_lo : 1 / C ≤ sk.p p := hsk_p p
        have hqp_lo := (abs_le.mp hqp).1
        have hdiv2 : 1 / C - 1 / (2 * C) = 1 / (2 * C) := by ring
        linarith
      have hFpp : sk.F t p p ≤ Real.sqrt t :=
        F_diag_le_sqrt_of_row_cap htpos ht1 sk p (hvs.2.2.1 p)
      have hpF : sk.p p * sk.F t p p ≤ C * Real.sqrt t :=
        mul_le_mul (hbroad p.1).2.2 hFpp (by simp [State.F, entryAbsSquare]) hCpos.le
      exact ⟨hKpp, by linarith⟩
  exact fun k hk => main k hk.le

end AndersonAC.AgentS78send
