import AndersonAC.AgentS78.Construction.TileStartLift
import AndersonAC.AgentS78.Construction.TileStartPortFacts

/-!
# `D₀ ≍ W` on the live ports (04:118–121, 05:328)

 . The duplicated energy is
`D₀(f) = D^phys(f̄) + Σ_x p_i² k_x⁴ (f_x − f̄_i)²` (eq:sweep-duplicate-energy). Given the
physical comparison `c₁ W^phys ≤ D^phys ≤ c₂ W^phys` (S78 `spatialEnergy` over the active
set, `initial_comparison_of_stageBounds`), the live port energy is comparable with the
port spatial energy `W(f) = inf_{f = α + v∘site} ‖α‖² + Λ(v)/b`, because the port weights
satisfy `1/4 ≤ k⁴ ≤ 1` and `Σ_{x above i} k_x⁴ = 1`.
-/

noncomputable section
set_option autoImplicit false

open scoped BigOperators

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

theorem gradientEnergy_nonneg' {ι : Type} [Fintype ι] (G : SimpleGraph ι) (f : ι → ℝ) :
    0 ≤ gradientEnergy G f := by
  classical
  unfold gradientEnergy
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_)
  split_ifs <;> positivity

section Comparison
variable (θ : ℝ) (z : RunRecord d m)

/-- The port spatial energy on the live ports (cover energy `Λ`, scale `b`). -/
def liveW (b : ℝ) : S45.Form (liveStart z) :=
  S45.spatialEnergy (fun x : liveStart z => x.1.1) b (gradientEnergy (nnGraph d m))

/-- The physical spatial energy of the active set (S78 form). -/
def physW (b : ℝ) : (Torus d m → ℝ) → ℝ := spatialEnergy (nnGraph d m) z.endpoint.active b

theorem liveW_nonneg {b : ℝ} (hb : 0 < b) (f : liveStart z → ℝ) : 0 ≤ liveW z b f := by
  apply Real.sInf_nonneg
  rintro a ⟨α, v, -, rfl⟩
  have : 0 ≤ S45.l2sq α := Finset.sum_nonneg fun _ _ => by positivity
  have := gradientEnergy_nonneg' (nnGraph d m) v
  positivity

theorem physW_nonneg {b : ℝ} (hb : 0 < b) (F : Torus d m → ℝ) : 0 ≤ physW z b F := by
  apply Real.sInf_nonneg
  rintro a ⟨α, v, -, rfl⟩
  have : 0 ≤ ∑ i ∈ z.endpoint.active, α i ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have := gradientEnergy_nonneg' (nnGraph d m) v
  positivity

theorem liveW_le {b : ℝ} (hb : 0 < b) (f : liveStart z → ℝ) (α : liveStart z → ℝ)
    (v : Torus d m → ℝ) (h : ∀ x, f x = α x + v x.1.1) :
    liveW z b f ≤ S45.l2sq α + gradientEnergy (nnGraph d m) v / b := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro a ⟨α', v', -, rfl⟩
    have : 0 ≤ S45.l2sq α' := Finset.sum_nonneg fun _ _ => by positivity
    have := gradientEnergy_nonneg' (nnGraph d m) v'
    positivity
  · exact ⟨α, v, h, rfl⟩

theorem physW_le {b : ℝ} (hb : 0 < b) (F α v : Torus d m → ℝ)
    (h : ∀ i ∈ z.endpoint.active, F i = α i + v i) :
    physW z b F ≤ (∑ i ∈ z.endpoint.active, α i ^ 2) + b⁻¹ * gradientEnergy (nnGraph d m) v := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro a ⟨α', v', -, rfl⟩
    have : 0 ≤ ∑ i ∈ z.endpoint.active, α' i ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have := gradientEnergy_nonneg' (nnGraph d m) v'
    positivity
  · exact ⟨α, v, h, rfl⟩

variable {θ}

theorem live_weight4 (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (x : liveStart z) :
    (livePortMap θ z).weight x ^ 4 = if x.1.2 then θ else 1 - θ := by
  rw [livePortMap_weight]
  split_ifs
  · exact power_quarter_pow_four hθ0
  · exact power_quarter_pow_four (by linarith)

theorem live_weight4_bounds (hθ : 1 / 4 ≤ θ ∧ θ ≤ 3 / 4) (x : liveStart z) :
    1 / 4 ≤ (livePortMap θ z).weight x ^ 4 ∧ (livePortMap θ z).weight x ^ 4 ≤ 3 / 4 := by
  rw [live_weight4 z (by linarith) (by linarith)]
  split_ifs <;> constructor <;> linarith

/-- Averaging a site function returns it (mass one). -/
theorem average_site (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (G : Fin z.endpoint.active.card → ℝ)
    (k : Fin z.endpoint.active.card) :
    (livePortMap θ z).average (fun x => G ((livePortMap θ z).site x)) k = G k := by
  unfold S45.PortMap.average
  have : ∀ x : liveStart z, (if (livePortMap θ z).site x = k then
      (livePortMap θ z).weight x ^ 4 * G ((livePortMap θ z).site x) else 0) =
      (if (livePortMap θ z).site x = k then (livePortMap θ z).weight x ^ 4 else 0) * G k := by
    intro x; split_ifs with h
    · rw [h]
    · simp
  rw [Finset.sum_congr rfl fun x _ => this x, ← Finset.sum_mul]
  have hm := livePortMap_mass θ z hθ0 hθ1 k
  unfold S45.PortMap.mass at hm
  rw [hm, one_mul]

theorem average_add (f g : liveStart z → ℝ) (k : Fin z.endpoint.active.card) :
    (livePortMap θ z).average (f + g) k =
      (livePortMap θ z).average f k + (livePortMap θ z).average g k := by
  unfold S45.PortMap.average
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp [Pi.add_apply] <;> ring

/-- Jensen: `(Σ k⁴ α)² ≤ Σ k⁴ α²` over the ports above a site (mass one). -/
theorem average_sq_le (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (α : liveStart z → ℝ)
    (k : Fin z.endpoint.active.card) :
    (livePortMap θ z).average α k ^ 2 ≤
      (livePortMap θ z).average (fun x => α x ^ 2) k := by
  set v := livePortMap θ z
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => if v.site x = k then v.weight x ^ 2 else 0)
    (fun x => if v.site x = k then v.weight x ^ 2 * α x else 0)
  have h1 : ∑ x, (if v.site x = k then v.weight x ^ 2 else 0) *
      (if v.site x = k then v.weight x ^ 2 * α x else 0) = v.average α k := by
    unfold S45.PortMap.average
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
  have h2 : ∑ x, (if v.site x = k then v.weight x ^ 2 else 0) ^ 2 = 1 := by
    have hm := livePortMap_mass θ z hθ0 hθ1 k
    unfold S45.PortMap.mass at hm
    rw [← hm]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
  have h3 : ∑ x, (if v.site x = k then v.weight x ^ 2 * α x else 0) ^ 2 =
      v.average (fun x => α x ^ 2) k := by
    unfold S45.PortMap.average
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
  rw [h1, h2, h3, one_mul] at hcs
  exact hcs

/-- Sum over ports of a site function weighted by `k⁴` is the site sum. -/
theorem sum_weight4_site (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (G : Fin z.endpoint.active.card → ℝ) :
    ∑ x, (livePortMap θ z).weight x ^ 4 * G ((livePortMap θ z).site x) = ∑ k, G k := by
  rw [AgentS45.sum_weight_fourth_site]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [livePortMap_mass θ z hθ0 hθ1, one_mul]

/-- `Σ_x k_x⁴ α_x² = Σ_i avg(α²)_i`. -/
theorem sum_average (α : liveStart z → ℝ) :
    ∑ k, (livePortMap θ z).average α k = ∑ x, (livePortMap θ z).weight x ^ 4 * α x := by
  unfold S45.PortMap.average
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp

end Comparison

section Main
variable {θ : ℝ} (z : RunRecord d m) (s : S45.State (Fin z.endpoint.active.card)) (t : ℝ)

/-- **`D₀ ≍ W` on the live ports**, from the physical comparison. -/
theorem live_comparison (hθ : 1 / 4 ≤ θ ∧ θ ≤ 3 / 4) {b c₁ c₂ Cb : ℝ} (hb : 0 < b)
    (hc₁ : 0 < c₁) (hc₂ : 0 ≤ c₂) (hCb : 0 < Cb)
    (hfix : ∀ k, s.g k k = s.r k) (hp : ∀ k, 1 / Cb ≤ s.p k ∧ s.p k ≤ Cb)
    (hlow : ∀ g, c₁ * physW z b (extendFun (actEquiv z) g) ≤ S45.qform (s.D t) g)
    (hup : ∀ g, S45.qform (s.D t) g ≤ c₂ * physW z b (extendFun (actEquiv z) g)) :
    S45.formComparable (S45.qform (((livePortMap θ z).liftState s).D t)) (liveW z b)
      (max (c₂ + 4 * Cb ^ 2) (8 / c₁ + 8 * Cb ^ 2)) := by
  classical
  set v := livePortMap θ z with hv
  set e := actEquiv z
  have hθ0 : 0 ≤ θ := by linarith
  have hθ1 : θ ≤ 1 := by linarith
  have hmass := livePortMap_mass θ z hθ0 hθ1
  have hq := (AgentS45.duplication_algebraic v s t hmass hfix).2.2.2.2
  have hw4 := live_weight4_bounds z hθ
  have hp2 : ∀ k, s.p k ^ 2 ≤ Cb ^ 2 := fun k => by
    have := hp k; nlinarith [one_div_pos.mpr hCb]
  have hp2low : ∀ k, 1 / Cb ^ 2 ≤ s.p k ^ 2 := fun k => by
    have h1 := (hp k).1
    have h0 : 0 ≤ 1 / Cb := by positivity
    calc 1 / Cb ^ 2 = (1 / Cb) ^ 2 := by ring
      _ ≤ s.p k ^ 2 := pow_le_pow_left₀ h0 h1 2
  set K₁ := c₂ + 4 * Cb ^ 2
  set K₂ := 8 / c₁ + 8 * Cb ^ 2
  -- upper bound: D₀ ≤ K₁ W
  have hupper : ∀ f, S45.qform ((v.liftState s).D t) f ≤ K₁ * liveW z b f := by
    intro f
    have hK₁ : 0 < K₁ := by positivity
    rw [← div_le_iff₀' hK₁]
    apply le_csInf
    · exact ⟨_, f, 0, fun x => by simp, rfl⟩
    rintro a ⟨α, vv, hdec, rfl⟩
    rw [div_le_iff₀' hK₁, hq f]
    -- the average splits
    set α' := v.average α
    have hsite : ∀ x : liveStart z, vv x.1.1 = (fun k => vv (e k).val) (v.site x) := by
      intro x
      exact congrArg vv (livePortMap_site_val θ z x).symm
    have hf : f = α + fun x => (fun k => vv (e k).val) (v.site x) := by
      funext x; rw [hdec x, Pi.add_apply, hsite x]
    have havg : v.average f = fun k => α' k + vv (e k).val := by
      funext k
      rw [hf, average_add]
      have h := average_site z hθ0 hθ1 (fun k => vv (e k).val) k
      rw [← hv] at h
      rw [h]
    -- physical part
    have hphys : S45.qform (s.D t) (v.average f) ≤
        c₂ * ((∑ k, α' k ^ 2) + b⁻¹ * gradientEnergy (nnGraph d m) vv) := by
      refine (hup _).trans (mul_le_mul_of_nonneg_left ?_ hc₂)
      have := physW_le z hb (extendFun e (v.average f)) (extendFun e α') vv (fun i hi => by
        simp only [extendFun, hi, dite_true, havg]
        simp [e])
      refine this.trans (le_of_eq ?_)
      congr 1
      rw [← sum_active_equiv z.endpoint.active e]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [extendFun, (e k).property]
    -- Jensen
    have hα' : ∑ k, α' k ^ 2 ≤ S45.l2sq α := by
      calc ∑ k, α' k ^ 2 ≤ ∑ k, v.average (fun x => α x ^ 2) k :=
            Finset.sum_le_sum fun k _ => average_sq_le z hθ0 hθ1 α k
        _ = ∑ x, v.weight x ^ 4 * α x ^ 2 := sum_average z _
        _ ≤ ∑ x, α x ^ 2 := Finset.sum_le_sum fun x _ => by
            have := hw4 x; nlinarith [sq_nonneg (α x)]
        _ = S45.l2sq α := by
            unfold S45.l2sq; refine Finset.sum_congr rfl fun x _ => ?_
            rw [Real.norm_eq_abs, sq_abs]
    -- fluctuation part
    have hfl : ∑ x, s.p (v.site x) ^ 2 * v.weight x ^ 4 * (f x - v.average f (v.site x)) ^ 2 ≤
        4 * Cb ^ 2 * S45.l2sq α := by
      have hdiff : ∀ x, f x - v.average f (v.site x) = α x - α' (v.site x) := by
        intro x; rw [havg, hf]; simp only [Pi.add_apply]; ring
      have h1 : ∀ x, s.p (v.site x) ^ 2 * v.weight x ^ 4 * (f x - v.average f (v.site x)) ^ 2 ≤
          Cb ^ 2 * (2 * α x ^ 2 + 2 * (v.weight x ^ 4 * α' (v.site x) ^ 2)) := by
        intro x
        rw [hdiff]
        have hw := hw4 x
        have hpx := hp2 (v.site x)
        have hsq : (α x - α' (v.site x)) ^ 2 ≤ 2 * α x ^ 2 + 2 * α' (v.site x) ^ 2 := by
          nlinarith [sq_nonneg (α x + α' (v.site x))]
        have hA : 0 ≤ (α x - α' (v.site x)) ^ 2 := sq_nonneg _
        calc s.p (v.site x) ^ 2 * v.weight x ^ 4 * (α x - α' (v.site x)) ^ 2
            ≤ Cb ^ 2 * (v.weight x ^ 4 * (2 * α x ^ 2 + 2 * α' (v.site x) ^ 2)) := by
              have : 0 ≤ v.weight x ^ 4 := by positivity
              have h2 : v.weight x ^ 4 * (α x - α' (v.site x)) ^ 2 ≤
                  v.weight x ^ 4 * (2 * α x ^ 2 + 2 * α' (v.site x) ^ 2) :=
                mul_le_mul_of_nonneg_left hsq this
              have h3 : 0 ≤ v.weight x ^ 4 * (α x - α' (v.site x)) ^ 2 := by positivity
              nlinarith [mul_le_mul hpx h2 h3 (sq_nonneg Cb)]
          _ ≤ Cb ^ 2 * (2 * α x ^ 2 + 2 * (v.weight x ^ 4 * α' (v.site x) ^ 2)) := by
              apply mul_le_mul_of_nonneg_left _ (sq_nonneg Cb)
              have : v.weight x ^ 4 * (2 * α x ^ 2) ≤ 2 * α x ^ 2 := by
                nlinarith [sq_nonneg (α x), hw.2]
              nlinarith
      refine (Finset.sum_le_sum fun x _ => h1 x).trans ?_
      have hsw := sum_weight4_site z hθ0 hθ1 (fun k => α' k ^ 2)
      rw [← hv] at hsw
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsw]
      have hl : ∑ x, α x ^ 2 = S45.l2sq α := by
        unfold S45.l2sq; refine Finset.sum_congr rfl fun x _ => ?_
        rw [Real.norm_eq_abs, sq_abs]
      rw [hl]
      nlinarith [hα', sq_nonneg Cb]
    have hgr := gradientEnergy_nonneg' (nnGraph d m) vv
    have hl2 : 0 ≤ S45.l2sq α := Finset.sum_nonneg fun _ _ => by positivity
    have hdivb : gradientEnergy (nnGraph d m) vv / b = b⁻¹ * gradientEnergy (nnGraph d m) vv := by
      rw [div_eq_inv_mul]
    rw [hdivb]
    have : 0 ≤ b⁻¹ * gradientEnergy (nnGraph d m) vv := by positivity
    nlinarith
  -- lower bound: W ≤ K₂ D₀
  have hlower : ∀ f, liveW z b f ≤ K₂ * S45.qform ((v.liftState s).D t) f := by
    intro f
    set fl : liveStart z → ℝ := fun x => f x - v.average f (v.site x)
    set Favg := extendFun e (v.average f)
    have hSF : liveW z b f - 2 * ∑ x, fl x ^ 2 ≤ 8 * physW z b Favg := by
      rw [← div_le_iff₀' (by norm_num : (0:ℝ) < 8)]
      apply le_csInf
      · exact ⟨_, Favg, 0, fun i _ => by simp, rfl⟩
      rintro a ⟨α, vv, hdec, rfl⟩
      rw [div_le_iff₀' (by norm_num : (0:ℝ) < 8)]
      have hdecp : ∀ x : liveStart z, f x = (fl x + α x.1.1) + vv x.1.1 := by
        intro x
        have hx : x.1.1 ∈ z.endpoint.active := mem_liveStart_iff.mp x.2
        have h1 := hdec x.1.1 hx
        have h2 : Favg x.1.1 = v.average f (v.site x) := by
          simp only [Favg, extendFun, hx, dite_true]
          rfl
        simp only [fl]; linarith
      have hW := liveW_le z hb f _ vv hdecp
      have hsq : S45.l2sq (fun x : liveStart z => fl x + α x.1.1) ≤
          2 * ∑ x, fl x ^ 2 + 2 * ∑ x : liveStart z, α x.1.1 ^ 2 := by
        unfold S45.l2sq
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun x _ => ?_
        rw [Real.norm_eq_abs, sq_abs]
        nlinarith [sq_nonneg (fl x - α x.1.1)]
      have hports : ∑ x : liveStart z, α x.1.1 ^ 2 ≤ 4 * ∑ i ∈ z.endpoint.active, α i ^ 2 := by
        have h1 : ∀ x : liveStart z, α x.1.1 ^ 2 ≤
            4 * (v.weight x ^ 4 * (fun k => α (e k).val ^ 2) (v.site x)) := by
          intro x
          have := (hw4 x).1
          have hx := livePortMap_site_val θ z x
          rw [← hv] at hx
          show α x.1.1 ^ 2 ≤ 4 * (v.weight x ^ 4 * α ((actEquiv z (v.site x)) : Torus d m) ^ 2)
          rw [hx]
          nlinarith [sq_nonneg (α x.1.1)]
        refine (Finset.sum_le_sum fun x _ => h1 x).trans (le_of_eq ?_)
        have hsw := sum_weight4_site z hθ0 hθ1 (fun k => α (e k).val ^ 2)
        rw [← hv] at hsw
        rw [← Finset.mul_sum, hsw, sum_active_equiv z.endpoint.active e (fun i => α i ^ 2)]
      have hgr := gradientEnergy_nonneg' (nnGraph d m) vv
      have hdivb : gradientEnergy (nnGraph d m) vv / b = b⁻¹ * gradientEnergy (nnGraph d m) vv := by
        rw [div_eq_inv_mul]
      rw [hdivb] at hW
      have : 0 ≤ b⁻¹ * gradientEnergy (nnGraph d m) vv := by positivity
      nlinarith
    have hphys : physW z b Favg ≤ S45.qform (s.D t) (v.average f) / c₁ := by
      rw [le_div_iff₀' hc₁]
      have := hlow (v.average f)
      exact this
    have hfl : ∑ x, fl x ^ 2 ≤ 4 * Cb ^ 2 *
        ∑ x, s.p (v.site x) ^ 2 * v.weight x ^ 4 * (f x - v.average f (v.site x)) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      have hw := (hw4 x).1
      have hp' := hp2low (v.site x)
      have hc : 1 ≤ 4 * Cb ^ 2 * (s.p (v.site x) ^ 2 * v.weight x ^ 4) := by
        have h1 : 1 / (4 * Cb ^ 2) ≤ s.p (v.site x) ^ 2 * v.weight x ^ 4 := by
          calc 1 / (4 * Cb ^ 2) = 1 / Cb ^ 2 * (1 / 4) := by field_simp
            _ ≤ s.p (v.site x) ^ 2 * v.weight x ^ 4 :=
                mul_le_mul hp' hw (by norm_num) (by positivity)
        rw [div_le_iff₀ (by positivity)] at h1
        linarith
      have : 0 ≤ fl x ^ 2 := sq_nonneg _
      simp only [fl]
      nlinarith
    rw [hq f]
    have hD0 : 0 ≤ S45.qform (s.D t) (v.average f) := by
      have := hlow (v.average f); have := physW_nonneg z hb (extendFun e (v.average f))
      nlinarith
    have hS0 : 0 ≤ ∑ x, s.p (v.site x) ^ 2 * v.weight x ^ 4 *
        (f x - v.average f (v.site x)) ^ 2 := Finset.sum_nonneg fun x _ => by positivity
    have h8 : 8 * (S45.qform (s.D t) (v.average f) / c₁) =
        8 / c₁ * S45.qform (s.D t) (v.average f) := by ring
    have e1 : 0 ≤ 8 / c₁ * ∑ x, s.p (v.site x) ^ 2 * v.weight x ^ 4 *
        (f x - v.average f (v.site x)) ^ 2 := mul_nonneg (by positivity) hS0
    have e2 : 0 ≤ 8 * Cb ^ 2 * S45.qform (s.D t) (v.average f) := mul_nonneg (by positivity) hD0
    show _ ≤ (8 / c₁ + 8 * Cb ^ 2) * _
    linarith [hSF, hphys, hfl, h8, e1, e2]
  -- assemble
  intro f
  have hW0 := liveW_nonneg z hb f
  have hK₁ : K₁ ≤ max K₁ K₂ := le_max_left _ _
  have hK₂ : K₂ ≤ max K₁ K₂ := le_max_right _ _
  have hK₂pos : 0 < K₂ := by positivity
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ (hK₂pos.trans_le hK₂)]
    have := hlower f
    have hQ0 : 0 ≤ S45.qform ((v.liftState s).D t) f := by
      by_contra hneg
      push_neg at hneg
      nlinarith [mul_neg_of_pos_of_neg hK₂pos hneg]
    nlinarith
  · exact (hupper f).trans (mul_le_mul_of_nonneg_right hK₁ hW0)

end Main

end AndersonAC.AgentS78
