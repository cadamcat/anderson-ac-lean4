import AndersonAC.AgentS6Row.Pathwise

noncomputable section
open Matrix Finset ComplexConjugate MeasureTheory

namespace AndersonAC.AgentS6Row

open AndersonAC.S6 AndersonAC.L64

/-- The five predictable scalar contractions used in the row expansion. -/
structure RowData where
  v : ℂ
  m : ℝ
  s : ℂ
  j : ℂ
  vn : ℝ

def RowData.a0 (D : RowData) : ℝ := ‖D.s‖ ^ 2
def RowData.a2 (D : RowData) : ℝ := ‖D.v‖ ^ 2 * D.m - D.vn * ‖D.s‖ ^ 2
def RowData.kappa (D : RowData) : ℂ := D.v * D.s - D.s * D.j
def RowData.affine (D : RowData) (z : ℂ) : ℝ := D.a0 + D.a2 * ‖z‖ ^ 2 + 2 * (z * D.kappa).re

def remainderConstant (K c : ℝ) : ℝ :=
  2 * (4 * K) * (4 * (1 + 2 * (4 * K)) + 2) * (4 * Real.sqrt (KPhi K c)) +
    2 * (4 * Real.sqrt (KPhi K c)) ^ 2 * (4 * (1 + 2 * (4 * K))) ^ 2

lemma remainderConstant_nonneg {K c : ℝ} (hK : 0 ≤ K) : 0 ≤ remainderConstant K c := by
  unfold remainderConstant
  positivity

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)}
  {t : ℝ} {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
  {order : Fin n ≃ Fin (Fintype.card (Fin n))}

def runningV (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (ω : Ω) : Fin n → ℂ :=
  fun j => if k < q.stop ω then heatV q k ω j else 0

def trialRowData (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (ω : Ω) (i : Fin n) : RowData where
  v := runningV q k ω i
  m := trialWeights t (r ω) (q.state k ω) (q.ridge k ω) (q.pivot k ω)
  s := rowPair (trialCross t (r ω) (q.state k ω)) (q.ridge k ω) (q.pivot k ω) i
  j := rowBPair (trialCross t (r ω) (q.state k ω)) (q.ridge k ω)
    (coreᶜ.erase (q.pivot k ω)) (runningV q k ω) i
  vn := ∑ j ∈ coreᶜ.erase (q.pivot k ω), ‖runningV q k ω j‖ ^ 2

lemma trialRowData_predictable (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (i : Fin n) :
    StronglyMeasurable[q.history k] (fun ω => (trialRowData q k ω i).v) ∧
    StronglyMeasurable[q.history k] (fun ω => (trialRowData q k ω i).m) ∧
    StronglyMeasurable[q.history k] (fun ω => (trialRowData q k ω i).s) ∧
    StronglyMeasurable[q.history k] (fun ω => (trialRowData q k ω i).j) ∧
    StronglyMeasurable[q.history k] (fun ω => (trialRowData q k ω i).vn) := by
  let σ : Unit → MeasurableSpace Ω := fun _ => q.history k
  let C : Ω → Matrix (Fin n) core ℂ := fun ω => trialCross t (r ω) (q.state k ω)
  let τ : Ω → ℝ := q.ridge k
  let x : Ω → Fin n := q.pivot k
  let v : Ω → Fin n → ℂ := runningV q k
  have hC : Measurable[σ ()] C := by
    refine @Measurable.of_eval_matrix (Fin n) core ℂ _ Ω (σ ()) _ (fun a b => ?_)
    exact ((continuous_id.matrix_elem a b).comp_stronglyMeasurable (q.cross_adapted k)).measurable
  have hτ : Measurable[σ ()] τ := (q.ridge_predictable k).measurable
  have hx : Measurable[σ ()] x := q.pivot_predictable k
  have hvj : ∀ j, StronglyMeasurable[σ ()] (fun ω => v ω j) := fun j =>
    heatV_running_stronglyMeasurable q k j
  letI : MeasurableSpace Ω := σ ()
  have hv : Measurable v := Measurable.of_eval (fun j => (hvj j).measurable)
  change StronglyMeasurable (fun ω => v ω i) ∧
    StronglyMeasurable (fun ω => leverage (C ω) (τ ω) (x ω)) ∧
    StronglyMeasurable (fun ω => rowPair (C ω) (τ ω) (x ω) i) ∧
    StronglyMeasurable (fun ω => rowBPair (C ω) (τ ω) (coreᶜ.erase (x ω)) (v ω) i) ∧
    StronglyMeasurable (fun ω => ∑ j ∈ coreᶜ.erase (x ω), ‖v ω j‖ ^ 2)
  refine ⟨hvj i, ?_, ?_, ?_, ?_⟩
  · exact stronglyMeasurable_fin_select x hx
      (fun x ω => leverage (C ω) (τ ω) x)
      (fun x => ((AndersonAC.AgentS6.measurable_leverage x).comp (hC.prodMk hτ)).stronglyMeasurable)
  · exact stronglyMeasurable_fin_select x hx
      (fun x ω => rowPair (C ω) (τ ω) x i)
      (fun x => ((measurable_rowPair x i).comp (hC.prodMk hτ)).stronglyMeasurable)
  · exact stronglyMeasurable_fin_select x hx
      (fun x ω => rowBPair (C ω) (τ ω) (coreᶜ.erase x) (v ω) i)
      (fun x => (measurable_rowBPair C τ v hC hτ hv (coreᶜ.erase x) i).stronglyMeasurable)
  · exact stronglyMeasurable_fin_select x hx
      (fun x ω => ∑ j ∈ coreᶜ.erase x, ‖v ω j‖ ^ 2)
      (fun x => Finset.stronglyMeasurable_fun_sum (coreᶜ.erase x) fun j _ => (hvj j).norm.pow 2)

set_option maxHeartbeats 1000000 in
lemma trialRowData_bounds (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (d : ℕ) (K c : ℝ) (hK : 0 ≤ K) (hc : 0 < c) (hs : Small t K)
    (hvnsmall : K / c * (t ^ betaW + 2 * coreCap d t * Real.sqrt (fourthCap t)) ≤ 1)
    (hfrosmall : 16 * KPhi K c * (leverageScale t) ^ 2 / t ≤ 1 / 4)
    (hcard : (core.card : ℝ) ≤ coreCap d t) (k : ℕ) (ω : Ω) (i : Fin n)
    (hE : ω ∈ survivorEvent q k i) (hr : BroadBounds c K (r ω))
    (hpre : HeatPrestate t K (fun j : (q.state k ω).active => r ω j)
      (trialInverse t (r ω) (q.state k ω)))
    (hξ : |q.residual k ω| ≤ K * Real.sqrt t) :
    let D := trialRowData q k ω i
    let z := heatCoefficient t (r ω (q.pivot k ω)) ((q.state k ω).hatG (q.pivot k ω) (q.pivot k ω)) (q.residual k ω)
    0 ≤ D.m ∧ D.m ≤ 4 * leverageScale t ∧ ‖D.v‖ ≤ 2 ∧ ‖D.s‖ ≤ 4 * leverageScale t ∧
      ‖D.j‖ ≤ 4 * leverageScale t / (Real.sqrt t * c) ∧ 0 ≤ D.vn ∧ D.vn ≤ 2 ∧
      |D.vn - 1| ≤ (2 * K / c) * epsilonScale d t ∧
      |recordedLeverageIncrement q k ω i - D.affine z| ≤
        remainderConstant K c * ((leverageScale t) ^ 2 * ‖D.v‖ / Real.sqrt t + (leverageScale t) ^ 3 / t) := by
  classical
  obtain ⟨hk, hi, hix, hic⟩ := hE
  have ht := hs.pos
  have hl : 0 < leverageScale t := Real.rpow_pos_of_pos ht _
  have hp : ∀ j, 0 < (r ω j).im := fun j => hc.trans_le (hr.2 j).2.1
  have hup := q.heat k ω hk
  have hcopy := hup
  obtain ⟨hx, hxc, hact, _, _, _⟩ := hcopy
  have hi' : i ∈ (q.state (k + 1) ω).active := by rw [hact]; exact Finset.mem_erase.mpr ⟨hix, hi⟩
  have hiS : i ∈ coreᶜ.erase (q.pivot k ω) := Finset.mem_erase.mpr ⟨hix, Finset.mem_compl.mpr hic⟩
  have hτ := q.running_ridge k ω hk
  obtain ⟨L, hL⟩ := exists_normalizer (ambientScattering t (r ω) (q.state k ω))
    core (q.ridge k ω) coreᶜ hτ
  let H := nheat (ambientScattering t (r ω) (q.state k ω)) L (q.pivot k ω)
    (ambientV t (r ω) (q.state k ω) (q.pivot k ω) hx)
  have hV : runningV q k ω = ambientV t (r ω) (q.state k ω) (q.pivot k ω) hx := by
    funext j
    unfold runningV
    rw [if_pos hk]
    by_cases hj : j ∈ (q.state k ω).active <;> simp [heatV, ambientV, hj, hx]
  have hHm : H.m = (trialRowData q k ω i).m := by
    rw [nheat_m _ hτ hL, ambientLeverage_eq t (r ω) (q.state k ω) (q.ridge k ω) _ hxc]
    rfl
  have hHs : rowS H i = (trialRowData q k ω i).s :=
    (ambient_rowScalars_eq t (r ω) (q.state k ω) (q.pivot k ω) i hxc hic (q.ridge k ω) L
      (ambientV t (r ω) (q.state k ω) (q.pivot k ω) hx) hL).1
  have hHj : H.u i ⬝ᵥ H.b = (trialRowData q k ω i).j := by
    have hh := (ambient_rowScalars_eq t (r ω) (q.state k ω) (q.pivot k ω) i hxc hic (q.ridge k ω) L
      (ambientV t (r ω) (q.state k ω) (q.pivot k ω) hx) hL).2
    simpa only [trialRowData, hV] using hh
  have hHvn : H.vn = (trialRowData q k ω i).vn := by simp only [H, nheat, NHeat.vn, trialRowData, hV]
  have hHv : H.v i = (trialRowData q k ω i).v := by simp only [H, nheat, trialRowData, hV]
  have hm : H.m ≤ 4 * leverageScale t := by
    rw [nheat_m _ hτ hL, ambientLeverage_eq t (r ω) (q.state k ω) (q.ridge k ω) _ hxc,
      q.pivot_max k ω hk]
    exact (q.running_cap k ω hk).2
  have hmi : H.lev i ≤ H.m := by
    rw [nheat_lev _ hτ hL, nheat_m _ hτ hL,
      ambientLeverage_eq t (r ω) (q.state k ω) (q.ridge k ω) i hic,
      ambientLeverage_eq t (r ω) (q.state k ω) (q.ridge k ω) _ hxc, q.pivot_max k ω hk]
    exact AndersonAC.AgentS6.le_maxWeight _ _
  have hvn : H.vn ≤ 2 := ambientHeat_vn_le_two ht hs.le_one hK hc (r ω)
    (fun j => (hr.2 j).2) (q.state k ω) (q.pivot k ω) hx hxc L hpre hcard hvnsmall
  have hb : nsq H.b ≤ H.m / (t * c ^ 2) := ambientHeat_b_bound ht hc (r ω)
    (fun j => (hr.2 j).2.1) (q.state k ω) (q.pivot k ω) hx hxc (q.ridge k ω) hτ L hL
  have hv2 : ‖H.v i‖ ≤ 2 := by
    have hh := (H.norm_sq_v_le_vn hiS).trans hvn
    nlinarith [norm_nonneg (H.v i)]
  have hsrow : ‖rowS H i‖ ≤ 4 * leverageScale t := (norm_rowS_le_m H i hmi).trans hm
  have hjrow : ‖H.u i ⬝ᵥ H.b‖ ≤ 4 * leverageScale t / (Real.sqrt t * c) :=
    (norm_rowB_le H ht hc i hmi hb).trans (div_le_div_of_nonneg_right hm (by positivity))
  have hdev : |H.vn - 1| ≤ K * t ^ betaW / c + (core.card + 1) * (K / c * Real.sqrt (fourthCap t)) :=
    ambientHeat_vn_bound ht hc (r ω) (fun j => (hr.2 j).2)
      (q.state k ω) (q.pivot k ω) hx hxc L hpre
  have hcount : (core.card : ℝ) + 1 ≤ 2 * coreCap d t := by
    have hh := coreCap_ge_one d t ht hs.le_one
    linarith
  have hdev' : |H.vn - 1| ≤ (2 * K / c) * epsilonScale d t := by
    have h1 := mul_le_mul_of_nonneg_right hcount
      (show 0 ≤ K / c * Real.sqrt (fourthCap t) by positivity)
    have h2 : 0 ≤ K / c * t ^ betaW := by positivity
    have h3 : 0 ≤ (2 * K / c) * Real.sqrt t := by positivity
    calc
      _ ≤ _ := hdev
      _ ≤ K * t ^ betaW / c + 2 * coreCap d t * (K / c * Real.sqrt (fourthCap t)) := by
        linarith only [h1]
      _ = (2 * K / c) * epsilonScale d t -
          (K / c * t ^ betaW + (2 * K / c) * Real.sqrt t) := by
        unfold epsilonScale
        ring
      _ ≤ _ := sub_le_self _ (add_nonneg h2 h3)
  let z := heatCoefficient t (r ω (q.pivot k ω))
    (trialInverse t (r ω) (q.state k ω) ⟨_, hx⟩ ⟨_, hx⟩) (q.residual k ω)
  have hγ : ‖trialInverse t (r ω) (q.state k ω) ⟨_, hx⟩ ⟨_, hx⟩‖ ≤ K :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans (hpre.1 ⟨_, hx⟩)
  have hz : ‖z‖ ≤ 4 * K := norm_hc_le hs (hr.2 _).1 hγ hξ
  have hF : fro (H.D z) ≤ 1 / 4 :=
    (fro_D_scale H ht hs.le_one hc hl.le hK hm hvn hb z hz).trans hfrosmall
  have hD : Real.sqrt (fro (H.D z)) ≤ (4 * Real.sqrt (KPhi K c)) * leverageScale t / Real.sqrt t :=
    sqrt_fro_D_scale H ht hs.le_one hc hl.le hK hm hvn hb z hz
  have hmi4 : H.lev i ≤ 4 * leverageScale t := hmi.trans hm
  have hrem := rowRem_scale H ht hl (by positivity : 0 ≤ 4 * K)
    (by positivity : 0 ≤ 4 * Real.sqrt (KPhi K c)) i hmi4 hm hv2 z hz hF hD
  have hchange : recordedLeverageIncrement q k ω i = rowAff H i z + rowRem H i z := by
    rw [recordedLeverageIncrement, if_pos ⟨hk, hi', hic⟩]
    rw [← normalized_trial_row_update ht (r ω) hp hup hx (q.ridge k ω) hτ L hL i hiS]
    exact row_change_eq_affine_add_rem H z hF i
  have haff : (trialRowData q k ω i).affine z = rowAff H i z := by
    unfold RowData.affine RowData.a0 RowData.a2 RowData.kappa rowAff
    rw [← hHs, ← hHj, ← hHm, ← hHv, ← hHvn]
    ring
  dsimp only
  rw [AndersonAC.AgentS6.hatG_eq_trialInverse q k ω hk.le ⟨_, hx⟩ ⟨_, hx⟩]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hHm]; exact H.m_nn
  · rw [← hHm]; exact hm
  · rw [← hHv]; exact hv2
  · rw [← hHs]; exact hsrow
  · rw [← hHj]; exact hjrow
  · rw [← hHvn]; exact H.vn_nonneg
  · rw [← hHvn]; exact hvn
  · rw [← hHvn]; exact hdev'
  · rw [show heatCoefficient t (r ω (q.pivot k ω))
        (trialInverse t (r ω) (q.state k ω) ⟨_, hx⟩ ⟨_, hx⟩) (q.residual k ω) = z from rfl,
      hchange, haff, add_sub_cancel_left, ← hHv]
    exact hrem

end AndersonAC.AgentS6Row
