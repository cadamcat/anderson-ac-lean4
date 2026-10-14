import AndersonAC.AgentS78Geo.TerminalMetric
import AndersonAC.AgentS78Geo.Damped

/-!
# Terminal Schur structure along a stopped trial

Generic over the index type `ι` of the trial, embedded by `emb` into a graph `G` (the torus).
`J0` is the direct hopping on `G`; at trial start every entry of the trial matrix that differs
from `J0` joins sites at zero collapsed distance for the old terminal set `T0`
(06-clearing.tex:50–54, 207–216). Each heat Schur-eliminates its pivot, which becomes a
provisional terminal, so the invariant persists with `T_k = T0 ∪ {pivots before k}`
(`trial_schur_invariant`). Consequences: the exterior geometry of Lemma 6.2
(`trial_exteriorGeometry`, 06-clearing.tex:196–216) and the Combes–Thomas decay of the
running inverse (`trial_resolvent_decay`, 06-clearing.tex:214–238).
-/

noncomputable section
open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator
set_option autoImplicit false

namespace AndersonAC.AgentS78Geo

open AndersonAC.S78 AndersonAC.S6

variable {Ω : Type} [MeasurableSpace Ω] {ι : Type} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] {V : Type} [DecidableEq V]
  {core : Finset ι} {t : ℝ} {r : Ω → ι → ℂ} {g0 : Ω → Matrix ι ι ℂ}
  {order : ι ≃ Fin (Fintype.card ι)}

/-- Old terminals and the pivots of the first `k` heats. -/
def trialTerminals (q : StoppedTrial (Ω := Ω) core t r g0 order) (emb : ι → V) (T0 : Finset V)
    (k : ℕ) (ω : Ω) : Finset V :=
  T0 ∪ (Finset.range k).image (fun l => emb (q.pivot l ω))

/-- The collapsed distance at step `k`. -/
def trialCollapsed (q : StoppedTrial (Ω := Ω) core t r g0 order) (G : SimpleGraph V)
    (emb : ι → V) (T0 : Finset V) (k : ℕ) (ω : Ω) (a b : ι) : ℝ :=
  terminalDistance G (trialTerminals q emb T0 k ω) (emb a) (emb b)

theorem trialTerminals_mono (q : StoppedTrial (Ω := Ω) core t r g0 order) (emb : ι → V)
    (T0 : Finset V) (k : ℕ) (ω : Ω) :
    trialTerminals q emb T0 k ω ⊆ trialTerminals q emb T0 (k + 1) ω := by
  unfold trialTerminals
  apply Finset.union_subset_union le_rfl
  apply Finset.image_subset_image
  exact Finset.range_mono (Nat.le_succ k)

theorem pivot_mem_trialTerminals (q : StoppedTrial (Ω := Ω) core t r g0 order) (emb : ι → V)
    (T0 : Finset V) (k : ℕ) (ω : Ω) :
    emb (q.pivot k ω) ∈ trialTerminals q emb T0 (k + 1) ω := by
  unfold trialTerminals
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨k, by simp, rfl⟩

/-- **Schur invariant** along the trial. -/
theorem trial_schur_invariant (q : StoppedTrial (Ω := Ω) core t r g0 order)
    {G : SimpleGraph V} (hG : G.Connected) (emb : ι → V) (T0 : Finset V)
    (J0 : V → V → ℝ) (hJadj : ∀ u v, J0 u v ≠ 0 → G.Adj u v)
    (h0 : ∀ ω (i j : {i // i ∈ (q.state 0 ω).active}),
      (q.state 0 ω).M i j ≠ J0 (emb i) (emb j) → terminalDistance G T0 (emb i) (emb j) = 0) :
    ∀ k ω, k ≤ q.stop ω → ∀ (i j : {i // i ∈ (q.state k ω).active}),
      (q.state k ω).M i j ≠ J0 (emb i) (emb j) → trialCollapsed q G emb T0 k ω i j = 0 := by
  intro k
  induction k with
  | zero =>
    intro ω _ i j hij
    have := h0 ω i j hij
    simpa [trialCollapsed, trialTerminals] using this
  | succ k ih =>
    intro ω hk i j hij
    have hks : k < q.stop ω := by omega
    obtain ⟨hx, _, hact, _, hM, _⟩ := q.heat k ω hks
    set s := q.state k ω
    set x := q.pivot k ω
    have hss : (q.state (k + 1) ω).active ⊆ s.active := by
      rw [hact]; exact Finset.erase_subset _ _
    have hsub : ∀ (a : {i // i ∈ (q.state (k + 1) ω).active}), (a : ι) ∈ s.active :=
      fun a => hss a.2
    have hmono : ∀ a b, trialCollapsed q G emb T0 (k + 1) ω a b ≤
        trialCollapsed q G emb T0 k ω a b := fun a b =>
      terminalDistance_antitone hG (trialTerminals_mono q emb T0 k ω) _ _
    have hnn : ∀ a b, 0 ≤ trialCollapsed q G emb T0 (k + 1) ω a b := fun a b =>
      terminalDistance_nonneg _ _ _ _
    -- an entry of the old matrix that is nonzero joins at zero new distance to the pivot
    have hzero_of_ne : ∀ (a : ι) (ha : a ∈ s.active), s.M ⟨a, ha⟩ ⟨x, hx⟩ ≠ 0 →
        trialCollapsed q G emb T0 (k + 1) ω a x = 0 := by
      intro a ha hne
      by_cases hJ : s.M ⟨a, ha⟩ ⟨x, hx⟩ = J0 (emb a) (emb x)
      · have hadj : G.Adj (emb a) (emb x) := hJadj _ _ (hJ ▸ hne)
        exact terminalDistance_adj_terminal G _ hadj
          (Or.inr (pivot_mem_trialTerminals q emb T0 k ω))
      · exact le_antisymm ((hmono a x).trans
          (ih ω hks.le ⟨a, ha⟩ ⟨x, hx⟩ hJ).le) (hnn a x)
    rw [hM i j (hsub i) (hsub j)] at hij
    by_cases hold : s.M ⟨i, hsub i⟩ ⟨j, hsub j⟩ = J0 (emb i) (emb j)
    · rw [hold] at hij
      have hprod : s.M ⟨i, hsub i⟩ ⟨x, hx⟩ * s.M ⟨x, hx⟩ ⟨j, hsub j⟩ ≠ 0 := by
        intro h0'
        apply hij
        rw [h0', zero_div, sub_zero]
      have h1 := hzero_of_ne i (hsub i) (left_ne_zero_of_mul hprod)
      have hsymm : s.M ⟨x, hx⟩ ⟨j, hsub j⟩ = s.M ⟨j, hsub j⟩ ⟨x, hx⟩ :=
        (s.symmetric.apply _ _).symm
      have h2 := hzero_of_ne j (hsub j) (hsymm ▸ right_ne_zero_of_mul hprod)
      have htri := terminalDistance_triangle hG (trialTerminals q emb T0 (k + 1) ω)
        (emb i) (emb x) (emb j)
      have h2' : terminalDistance G (trialTerminals q emb T0 (k + 1) ω) (emb x) (emb j) = 0 := by
        rw [terminalDistance_symm hG]; exact h2
      apply le_antisymm _ (hnn _ _)
      unfold trialCollapsed at h1 ⊢
      linarith
    · exact le_antisymm ((hmono i j).trans (ih ω hks.le ⟨i, hsub i⟩ ⟨j, hsub j⟩ hold).le)
        (hnn i j)


section Decay

variable [Fintype V]

theorem card_filter_le_of_adj {G : SimpleGraph V} (d : ℕ)
    (hdegG : ∀ u (S : Finset V), (∀ v ∈ S, G.Adj u v) → S.card ≤ 2 * d)
    {R : Type} [Fintype R] (f : R → V) (hf : Function.Injective f) (P : Matrix R R ℝ)
    (hP : ∀ a b, P a b ≠ 0 → G.Adj (f a) (f b)) (a : R) :
    ((Finset.univ.filter (fun b => P a b ≠ 0)).card : ℝ) ≤ 2 * d := by
  have h1 : ((Finset.univ.filter (fun b => P a b ≠ 0)).image f).card ≤ 2 * d := by
    apply hdegG (f a)
    intro v hv
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    exact hP a b (Finset.mem_filter.mp hb).2
  rw [Finset.card_image_of_injective _ hf] at h1
  exact_mod_cast h1

theorem collapsed_facts (q : StoppedTrial (Ω := Ω) core t r g0 order) {G : SimpleGraph V}
    (hG : G.Connected) (emb : ι → V) (T0 : Finset V) (k : ℕ) (ω : Ω) :
    let coll := trialCollapsed q G emb T0 k ω
    (∀ a b, 0 ≤ coll a b) ∧ (∀ a b, coll a b = coll b a) ∧
      (∀ a b c, coll a c ≤ coll a b + coll b c) ∧ (∀ a, coll a a = 0) := by
  refine ⟨fun a b => terminalDistance_nonneg _ _ _ _, fun a b => terminalDistance_symm hG _ _ _,
    fun a b c => terminalDistance_triangle hG _ _ _ _, fun a => terminalDistance_self _ _ _⟩

/-- **Combes–Thomas decay** of the running inverse in the collapsed metric. -/
theorem trial_resolvent_decay (q : StoppedTrial (Ω := Ω) core t r g0 order)
    {G : SimpleGraph V} (hG : G.Connected) (emb : ι → V) (hemb : Function.Injective emb)
    (T0 : Finset V) (J0 : V → V → ℝ) (hJs : ∀ u v, J0 u v = J0 v u)
    (hJ1 : ∀ u v, |J0 u v| ≤ 1) (hJadj : ∀ u v, J0 u v ≠ 0 → G.Adj u v) (d : ℕ)
    (hdegG : ∀ u (S : Finset V), (∀ v ∈ S, G.Adj u v) → S.card ≤ 2 * d)
    (h0 : ∀ ω (i j : {i // i ∈ (q.state 0 ω).active}),
      (q.state 0 ω).M i j ≠ J0 (emb i) (emb j) → terminalDistance G T0 (emb i) (emb j) = 0)
    (c : ℝ) (hc : 0 < c) (hr : ∀ ω i, c ≤ (r ω i).im) (ht : 0 < t) (ht1 : t ≤ 1) :
    ∀ k ω, k ≤ q.stop ω → ∀ i j : {i // i ∈ (q.state k ω).active},
      ‖scaledInverse t (trialInverse t (r ω) (q.state k ω)) i j‖ ≤
        (4 / (3 * c)) / Real.sqrt t * Real.exp (-(AndersonAC.SolS6.localizationRate d c) * t *
          trialCollapsed q G emb T0 k ω i j) := by
  intro k ω hk
  set s := q.state k ω
  intro i j
  set coll := trialCollapsed q G emb T0 k ω
  obtain ⟨hnn, hsymm, htri, hself⟩ := collapsed_facts q hG emb T0 k ω
  have hinv := trial_schur_invariant q hG emb T0 J0 hJadj h0 k ω hk
  let J : Matrix {i // i ∈ s.active} {i // i ∈ s.active} ℝ :=
    Matrix.of fun a b => J0 (emb a) (emb b)
  let K : Matrix {i // i ∈ s.active} {i // i ∈ s.active} ℝ := s.M - J
  have hMJK : s.M = J + K := by ext a b; simp [K]
  have hJs' : J.IsSymm := Matrix.IsSymm.ext fun a b => by simp only [J, Matrix.of_apply]; exact hJs _ _
  have hKs : K.IsSymm := Matrix.IsSymm.ext fun a b => by
    simp only [K, Matrix.sub_apply, J, Matrix.of_apply]
    rw [s.symmetric.apply a b, hJs]
  have hdeg : ∀ a, ((Finset.univ.filter (fun b => J a b ≠ 0)).card : ℝ) ≤ 2 * d :=
    card_filter_le_of_adj d hdegG (fun a : {i // i ∈ s.active} => emb a)
      (hemb.comp Subtype.val_injective) J (fun a b h => hJadj _ _ (by simpa [J] using h))
  have hJρ : ∀ a b, J a b ≠ 0 → |coll a j - coll b j| ≤ 1 := by
    intro a b hab
    have h1 : coll a b ≤ 1 := terminalDistance_adj_le_one G _ (hJadj _ _ (by simpa [J] using hab))
    rw [abs_sub_le_iff]
    constructor
    · linarith [htri a b j]
    · linarith [htri b a j, hsymm a b]
  have hKρ : ∀ a b, K a b ≠ 0 → coll a j = coll b j := by
    intro a b hab
    have hne : s.M a b ≠ J0 (emb a) (emb b) := by
      intro h; apply hab; simp [K, J, h]
    have h0' := hinv a b hne
    apply le_antisymm
    · linarith [htri a b j]
    · linarith [htri b a j, hsymm a b]
  have hct := combes_thomas_entry d J K hJs' hKs (fun a b => hJ1 _ _) hdeg t c ht ht1 hc
    (fun a : {i // i ∈ s.active} => r ω a) (fun a => hr ω a) (fun l => coll l j) hJρ hKρ i j
  have hjj : coll j j = 0 := hself _
  rw [hjj, sub_zero] at hct
  have hg : trialInverse t (r ω) s = (dampedMatrix (J + K) t (fun a => r ω a))⁻¹ := by
    rw [← hMJK]; rfl
  rw [scaledInverse, Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), hg]
  have hsq : Real.sqrt t * (4 / (3 * (t * c))) = (4 / (3 * c)) / Real.sqrt t := by
    have hs := Real.sqrt_pos.mpr ht
    have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
    calc Real.sqrt t * (4 / (3 * (t * c))) =
          Real.sqrt t * ((4 / (3 * c)) / (Real.sqrt t * Real.sqrt t)) := by rw [hss]; ring
      _ = (4 / (3 * c)) / Real.sqrt t := by field_simp
  calc Real.sqrt t * ‖(dampedMatrix (J + K) t (fun a => r ω a))⁻¹ i j‖
      ≤ Real.sqrt t * (4 / (3 * (t * c)) *
          Real.exp (-(AndersonAC.SolS6.localizationRate d c * t * coll i j))) :=
        mul_le_mul_of_nonneg_left hct (Real.sqrt_nonneg _)
    _ = _ := by rw [← mul_assoc, hsq, neg_mul, neg_mul]

end Decay

section Exterior

variable [Fintype V]

/-- The trial matrix extended by zero to the whole index type. -/
def extendM {core : Finset ι} (s : TrialState core) : Matrix ι ι ℝ := fun i j =>
  if h : i ∈ s.active ∧ j ∈ s.active then s.M ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-- The direct hops between active sites of the trial state. -/
def extendJ {core : Finset ι} (s : TrialState core) (emb : ι → V) (J0 : V → V → ℝ) :
    Matrix ι ι ℝ := fun i j => if i ∈ s.active ∧ j ∈ s.active then J0 (emb i) (emb j) else 0

theorem distanceToCore_abs_sub_le {α : Type} (dist : α → α → ℝ)
    (hnn : ∀ a b, 0 ≤ dist a b) (hsymm : ∀ a b, dist a b = dist b a)
    (htri : ∀ a b c, dist a c ≤ dist a b + dist b c) (core : Finset α) (i j : α) :
    |distanceToCore dist core i - distanceToCore dist core j| ≤ dist i j := by
  have h1 := distanceToCore_lipschitz dist hnn htri core i j
  have h2 := distanceToCore_lipschitz dist hnn htri core j i
  rw [hsymm j i] at h2
  rw [abs_sub_le_iff]; constructor <;> linarith

theorem far_of_radius_pos {α : Type} (dist : α → α → ℝ) (core : Finset α) (i : α)
    (h : 0 < max (distanceToCore dist core i - 1) 0) : ∀ c ∈ core, 1 < dist i c := by
  intro c hc
  have hne : core.Nonempty := ⟨c, hc⟩
  have hpos : 1 < distanceToCore dist core i := by
    by_contra hle
    push_neg at hle
    have : max (distanceToCore dist core i - 1) 0 = 0 := max_eq_right (by linarith)
    linarith
  unfold distanceToCore at hpos
  rw [dif_pos hne] at hpos
  exact hpos.trans_le (Finset.inf'_le _ hc)

theorem sqrtDamping_inv (p : ι → ℝ) (hp : ∀ i, 0 < p i) :
    (sqrtDamping p)⁻¹ = Matrix.diagonal (fun i => ((Real.sqrt (p i) : ℂ))⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [sqrtDamping, Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one with i
  have : (Real.sqrt (p i) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hp i)).ne'
  field_simp

/-- The row of `H D⁻¹ C` at a site at collapsed distance `> 1` from the core vanishes. -/
theorem exterior_row_zero (q : StoppedTrial (Ω := Ω) core t r g0 order)
    {G : SimpleGraph V} (hG : G.Connected) (emb : ι → V)
    (T0 : Finset V) (J0 : V → V → ℝ) (hJadj : ∀ u v, J0 u v ≠ 0 → G.Adj u v)
    (h0 : ∀ ω (i j : {i // i ∈ (q.state 0 ω).active}),
      (q.state 0 ω).M i j ≠ J0 (emb i) (emb j) → terminalDistance G T0 (emb i) (emb j) = 0)
    (c : ℝ) (hc : 0 < c) (hr : ∀ ω i, c ≤ (r ω i).im) (ht : 0 < t)
    (k : ℕ) (ω : Ω) (hk : k ≤ q.stop ω) (i : ι)
    (hfar : ∀ b ∈ core, 1 < trialCollapsed q G emb T0 k ω i b) (hicore : i ∉ core)
    (v : EuclideanSpace ℂ {b // b ∈ core}) :
    (Matrix.toEuclideanLin (dampedMatrix (extendJ (q.state k ω) emb J0 +
        (extendM (q.state k ω) - extendJ (q.state k ω) emb J0)) t (r ω) *
        (sqrtDamping (imagDamping (r ω)))⁻¹)
      (Matrix.toEuclideanLin (trialCross t (r ω) (q.state k ω)) v)) i = 0 := by
  have hunit : IsUnit (dampedMatrix (q.state k ω).M t (fun a => r ω a)).det :=
    damped_isUnit (q.state k ω).M (q.state k ω).symmetric t c ht hc _ (fun a => hr ω a)
  have hMg : dampedMatrix (q.state k ω).M t (fun a => r ω a) *
      trialInverse t (r ω) (q.state k ω) = 1 := Matrix.mul_nonsing_inv _ hunit
  have hp : ∀ j, 0 < imagDamping (r ω) j := fun j => hc.trans_le (hr ω j)
  have hinv := trial_schur_invariant q hG emb T0 J0 hJadj h0 k ω hk
  have hH : dampedMatrix (extendJ (q.state k ω) emb J0 +
      (extendM (q.state k ω) - extendJ (q.state k ω) emb J0)) t (r ω) =
      dampedMatrix (extendM (q.state k ω)) t (r ω) := by simp
  rw [hH]
  -- the core column entries of the trial matrix vanish on the row `i`
  have hMzero : ∀ (hi : i ∈ (q.state k ω).active) (j : {a // a ∈ (q.state k ω).active}),
      (j : ι) ∈ core → (q.state k ω).M ⟨i, hi⟩ j = 0 := by
    intro hi j hj
    by_contra hne
    by_cases hJ : (q.state k ω).M ⟨i, hi⟩ j = J0 (emb i) (emb j)
    · have hadj : G.Adj (emb i) (emb j) := hJadj _ _ (hJ ▸ hne)
      have h1 : trialCollapsed q G emb T0 k ω i j ≤ 1 := terminalDistance_adj_le_one G _ hadj
      linarith [hfar j hj]
    · have h1 := hinv ⟨i, hi⟩ j hJ
      change trialCollapsed q G emb T0 k ω i j = 0 at h1
      linarith [hfar j hj]
  -- the whole row of `H D⁻¹ C`
  have hrow : ∀ b : {b // b ∈ core},
      (dampedMatrix (extendM (q.state k ω)) t (r ω) * (sqrtDamping (imagDamping (r ω)))⁻¹ *
        trialCross t (r ω) (q.state k ω)) i b = 0 := by
    intro b
    rw [sqrtDamping_inv _ hp, Matrix.mul_apply]
    have hterm : ∀ j, (dampedMatrix (extendM (q.state k ω)) t (r ω) *
        Matrix.diagonal (fun i => ((Real.sqrt (imagDamping (r ω) i) : ℂ))⁻¹))
        i j * trialCross t (r ω) (q.state k ω) j b =
        if hj : j ∈ (q.state k ω).active then
          (if j ∈ core then 0 else dampedMatrix (extendM (q.state k ω)) t (r ω) i j *
            trialInverse t (r ω) (q.state k ω) ⟨j, hj⟩ ⟨b, (q.state k ω).core_active b.2⟩) *
            (2 * Complex.I * (t : ℂ) * (Real.sqrt (imagDamping (r ω) b) : ℂ))
        else 0 := by
      intro j
      rw [Matrix.mul_diagonal]
      simp only [trialCross]
      by_cases hj : j ∈ (q.state k ω).active
      · rw [dif_pos hj, dif_pos hj]
        by_cases hjc : j ∈ core
        · rw [if_pos hjc, if_pos hjc]; simp
        · rw [if_neg hjc, if_neg hjc]
          have hjb : (⟨j, hj⟩ : {a // a ∈ (q.state k ω).active}) ≠
              ⟨b, (q.state k ω).core_active b.2⟩ := by
            intro h
            apply hjc
            have := congrArg Subtype.val h
            simp only at this
            rw [this]; exact b.2
          simp only [scattering, scatteringOfDamping, Matrix.add_apply,
            Matrix.one_apply_ne hjb, zero_add, Matrix.smul_apply, smul_eq_mul, sqrtDamping,
            Matrix.diagonal_mul, Matrix.mul_diagonal, imagDamping]
          have hpj : (Real.sqrt (r ω j).im : ℂ) ≠ 0 :=
            Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hp j)).ne'
          field_simp
      · rw [dif_neg hj, dif_neg hj, mul_zero]
    simp_rw [hterm]
    rw [← Finset.sum_subset (Finset.subset_univ (q.state k ω).active)
      (fun j _ hj => by rw [dif_neg hj])]
    rw [← Finset.sum_coe_sort (q.state k ω).active]
    simp only [Subtype.coe_eta, Finset.coe_mem, dif_pos]
    rw [← Finset.sum_mul]
    apply mul_eq_zero_of_left
    by_cases hi : i ∈ (q.state k ω).active
    · have hHrow : ∀ j : {a // a ∈ (q.state k ω).active},
          dampedMatrix (extendM (q.state k ω)) t (r ω) i j =
            dampedMatrix (q.state k ω).M t (fun a => r ω a) ⟨i, hi⟩ j := by
        intro j
        obtain ⟨jv, hjv⟩ := j
        have hM : extendM (q.state k ω) i jv = (q.state k ω).M ⟨i, hi⟩ ⟨jv, hjv⟩ := by
          simp only [extendM]; rw [dif_pos ⟨hi, hjv⟩]
        have hD : Matrix.diagonal (r ω) i jv =
            Matrix.diagonal (fun a : {a // a ∈ (q.state k ω).active} => r ω a) ⟨i, hi⟩
              ⟨jv, hjv⟩ := by
          by_cases hij : i = jv
          · subst hij; simp
          · have hne : (⟨i, hi⟩ : {a // a ∈ (q.state k ω).active}) ≠ ⟨jv, hjv⟩ :=
              fun h => hij (congrArg Subtype.val h)
            rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hne]
        simp only [dampedMatrix, Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, hM, hD]
      have hsplit : ∀ j : {a // a ∈ (q.state k ω).active},
          (if (j : ι) ∈ core then 0 else dampedMatrix (extendM (q.state k ω)) t (r ω) i j *
            trialInverse t (r ω) (q.state k ω) j ⟨b, (q.state k ω).core_active b.2⟩) =
          dampedMatrix (q.state k ω).M t (fun a => r ω a) ⟨i, hi⟩ j *
            trialInverse t (r ω) (q.state k ω) j ⟨b, (q.state k ω).core_active b.2⟩ -
          (if (j : ι) ∈ core then dampedMatrix (q.state k ω).M t (fun a => r ω a) ⟨i, hi⟩ j *
            trialInverse t (r ω) (q.state k ω) j ⟨b, (q.state k ω).core_active b.2⟩ else 0) := by
        intro j
        rw [hHrow j]
        split_ifs <;> ring
      simp_rw [hsplit]
      rw [Finset.sum_sub_distrib]
      have h1 : ∑ j : {a // a ∈ (q.state k ω).active},
          dampedMatrix (q.state k ω).M t (fun a => r ω a) ⟨i, hi⟩ j *
            trialInverse t (r ω) (q.state k ω) j ⟨b, (q.state k ω).core_active b.2⟩ = 0 := by
        have := congrFun (congrFun hMg ⟨i, hi⟩) ⟨b, (q.state k ω).core_active b.2⟩
        rw [Matrix.mul_apply] at this
        rw [this, Matrix.one_apply_ne]
        intro h
        apply hicore
        have := congrArg Subtype.val h
        simp only at this
        rw [this]; exact b.2
      have h2 : ∑ j : {a // a ∈ (q.state k ω).active},
          (if (j : ι) ∈ core then dampedMatrix (q.state k ω).M t (fun a => r ω a) ⟨i, hi⟩ j *
            trialInverse t (r ω) (q.state k ω) j ⟨b, (q.state k ω).core_active b.2⟩ else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        split_ifs with hj
        · have hne : (⟨i, hi⟩ : {a // a ∈ (q.state k ω).active}) ≠ j := by
            intro h; apply hicore; rw [← h] at hj; exact hj
          have : dampedMatrix (q.state k ω).M t (fun a => r ω a) ⟨i, hi⟩ j = 0 := by
            simp only [dampedMatrix, Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply,
              Matrix.diagonal_apply_ne _ hne, hMzero hi j hj]
            simp
          rw [this, zero_mul]
        · rfl
      rw [h1, h2, sub_zero]
    · apply Finset.sum_eq_zero
      intro j _
      have hij : i ≠ (j : ι) := fun h => hi (h ▸ j.2)
      have : dampedMatrix (extendM (q.state k ω)) t (r ω) i j = 0 := by
        simp only [dampedMatrix, Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply,
          Matrix.diagonal_apply_ne _ hij, extendM,
          dif_neg (fun h : i ∈ (q.state k ω).active ∧ (j : ι) ∈ (q.state k ω).active => hi h.1)]
        simp
      split_ifs <;> simp [this]
  have hlin : Matrix.toEuclideanLin (dampedMatrix (extendM (q.state k ω)) t (r ω) *
      (sqrtDamping (imagDamping (r ω)))⁻¹)
      (Matrix.toEuclideanLin (trialCross t (r ω) (q.state k ω)) v) =
      Matrix.toEuclideanLin (dampedMatrix (extendM (q.state k ω)) t (r ω) *
        (sqrtDamping (imagDamping (r ω)))⁻¹ * trialCross t (r ω) (q.state k ω)) v := by
    ext l
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
      Matrix.mulVec_mulVec]
  rw [hlin]
  change (Matrix.toEuclideanLin _ v).ofLp i = 0
  rw [toEuclideanLin_apply']
  exact Finset.sum_eq_zero fun b _ => by rw [hrow b, zero_mul]

/-- **Exterior geometry** of the trial state (Lemma 6.2 input, 06-clearing.tex:196–216). -/
theorem trial_exteriorGeometry (q : StoppedTrial (Ω := Ω) core t r g0 order)
    {G : SimpleGraph V} (hG : G.Connected) (emb : ι → V) (hemb : Function.Injective emb)
    (T0 : Finset V) (J0 : V → V → ℝ) (hJs : ∀ u v, J0 u v = J0 v u)
    (hJ1 : ∀ u v, |J0 u v| ≤ 1) (hJadj : ∀ u v, J0 u v ≠ 0 → G.Adj u v) (d : ℕ)
    (hdegG : ∀ u (S : Finset V), (∀ v ∈ S, G.Adj u v) → S.card ≤ 2 * d)
    (h0 : ∀ ω (i j : {i // i ∈ (q.state 0 ω).active}),
      (q.state 0 ω).M i j ≠ J0 (emb i) (emb j) → terminalDistance G T0 (emb i) (emb j) = 0)
    (c : ℝ) (hc : 0 < c) (hr : ∀ ω i, c ≤ (r ω i).im) (ht : 0 < t) :
    ∀ k ω, k ≤ q.stop ω →
      ExteriorGeometry d (fun i => max (distanceToCore (trialCollapsed q G emb T0 k ω) core i - 1) 0)
        (dampedMatrix (extendJ (q.state k ω) emb J0 +
          (extendM (q.state k ω) - extendJ (q.state k ω) emb J0)) t (r ω))
        (trialCross t (r ω) (q.state k ω)) t (r ω) := by
  intro k ω hk
  set s := q.state k ω
  set coll := trialCollapsed q G emb T0 k ω
  set ρ : ι → ℝ := fun i => max (distanceToCore coll core i - 1) 0
  obtain ⟨hnn, hsymm, htri, hself⟩ := collapsed_facts q hG emb T0 k ω
  have hinv := trial_schur_invariant q hG emb T0 J0 hJadj h0 k ω hk
  have hρlip : ∀ i j, |ρ i - ρ j| ≤ coll i j := by
    intro i j
    have h := distanceToCore_abs_sub_le coll hnn hsymm htri core i j
    exact (abs_max_sub_max_le_abs _ _ _).trans (by simpa using h)
  set Jk := extendJ s emb J0
  set Mk := extendM s
  refine ⟨fun i => le_max_right _ _, ⟨Jk, Mk - Jk, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact Matrix.IsSymm.ext fun i j => by
      simp only [Jk, extendJ]
      by_cases h : i ∈ s.active ∧ j ∈ s.active
      · rw [if_pos h, if_pos ⟨h.2, h.1⟩, hJs]
      · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩)]
  · exact Matrix.IsSymm.ext fun i j => by
      simp only [Matrix.sub_apply, Jk, Mk, extendJ, extendM]
      by_cases h : i ∈ s.active ∧ j ∈ s.active
      · rw [dif_pos h, dif_pos ⟨h.2, h.1⟩, if_pos h, if_pos ⟨h.2, h.1⟩, hJs,
          s.symmetric.apply]
      · rw [dif_neg h, dif_neg (fun h' => h ⟨h'.2, h'.1⟩), if_neg h,
          if_neg (fun h' => h ⟨h'.2, h'.1⟩)]
  · intro i j
    simp only [Jk, extendJ]
    split_ifs
    · exact hJ1 _ _
    · simp
  · intro i
    exact card_filter_le_of_adj d hdegG emb hemb Jk (fun a b h => by
      simp only [Jk, extendJ] at h
      split_ifs at h
      · exact hJadj _ _ h
      · exact absurd rfl h) i
  · intro i j hij
    have hadj : G.Adj (emb i) (emb j) := by
      simp only [Jk, extendJ] at hij
      split_ifs at hij
      · exact hJadj _ _ hij
      · exact absurd rfl hij
    exact (hρlip i j).trans (terminalDistance_adj_le_one G _ hadj)
  · intro i j hij
    simp only [Matrix.sub_apply, Jk, Mk, extendJ, extendM] at hij
    by_cases h : i ∈ s.active ∧ j ∈ s.active
    · rw [dif_pos h, if_pos h] at hij
      have hne : s.M ⟨i, h.1⟩ ⟨j, h.2⟩ ≠ J0 (emb i) (emb j) := sub_ne_zero.mp hij
      have h0' := hinv ⟨i, h.1⟩ ⟨j, h.2⟩ hne
      have := hρlip i j
      change coll i j = 0 at h0'
      rw [h0'] at this
      exact sub_eq_zero.mp (abs_nonpos_iff.mp this)
    · rw [dif_neg h, if_neg h, sub_zero] at hij
      exact absurd rfl hij
  · -- exterior source
    intro w hw i hi
    obtain ⟨v, rfl⟩ := hw
    have hfar := far_of_radius_pos coll core i hi
    have hicore : i ∉ core := fun h => by
      have := hfar i h
      have h2 : coll i i = 0 := hself i
      linarith
    exact exterior_row_zero q hG emb T0 J0 hJadj h0 c hc hr ht k ω hk i hfar hicore v

end Exterior

end AndersonAC.AgentS78Geo
