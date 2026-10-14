import AndersonAC.S45.MatrixConcentrationProof
import AndersonAC.S45.SmallFactsProof
import AndersonAC.S45.HelperStatements2
import AndersonAC.S45.SchurProof

/-! `AndersonAC.S45.ordinary_sweep_endpoint` (Proposition 5.8, deterministic
endpoint of a valid ordinary sweep). -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators ComplexOrder

namespace AndersonAC.AgentS45

open AndersonAC.S45

/-! ### The reserve frame -/

section Frame

variable {n : ℕ}

theorem mem_reserves_true (i : Fin n) : ((i, true) : initialPorts (Fin n)) ∈ (reserves : Finset _) :=
  Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩

/-- Reserve ports indexed by sites. -/
def reserveEquiv (L : Finset (initialPorts (Fin n))) (hL : L = reserves) : Fin n ≃ L where
  toFun i := ⟨(i, true), hL ▸ mem_reserves_true i⟩
  invFun x := x.1.1
  left_inv i := rfl
  right_inv x := by
    obtain ⟨⟨i, b⟩, hx⟩ := x
    have : b = true := by
      rw [hL] at hx; exact (Finset.mem_filter.1 hx).2
    subst this; rfl

@[simp] theorem reserveEquiv_apply (L : Finset (initialPorts (Fin n))) (hL : L = reserves)
    (i : Fin n) : ((reserveEquiv L hL i : L) : initialPorts (Fin n)) = (i, true) := rfl

/-- Reindexing a state along an equivalence. -/
def State.reindex {ι κ : Type*} (e : κ ≃ ι) (s : State ι) : State κ :=
  ⟨fun i j => s.g (e i) (e j), fun i => s.r (e i)⟩

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem State.reindex_h (e : κ ≃ ι) (s : State ι) (t : ℝ) :
    (State.reindex e s).h t = (s.h t).submatrix e e := by
  ext i j; rfl

theorem State.reindex_K (e : κ ≃ ι) (s : State ι) (t : ℝ) :
    (State.reindex e s).K t = (s.K t).submatrix e e := by
  simp only [State.K, State.reindex_h]; rfl

theorem norm_submatrix_equiv (e : κ ≃ ι) (A : Matrix ι ι ℂ) : ‖A.submatrix e e‖ = ‖A‖ := by
  have := norm_reindex e.symm A
  simpa [reindex_apply] using this

theorem State.reindex_fourthRow (e : κ ≃ ι) (s : State ι) (t : ℝ) (i : κ) :
    (State.reindex e s).fourthRow t Finset.univ i = s.fourthRow t Finset.univ (e i) := by
  simp only [State.fourthRow, State.reindex_h, submatrix_apply]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

end Frame

/-! ### Helper statements taken as hypotheses (exact `Statements.lean` types at universe 0;
`ProofCheck.lean` checks each against the phase statement). -/

def CumulativeSchurStmt : Prop :=
  ∀ (P : Type) [Fintype P] [DecidableEq P]
    (q : Sequence P) (t : ℝ) (r : P → ℂ) (_ht : 0 < t)
    (_hp : ∀ i, 0 < (r i).im)
    (_hseq : q.wellFormed t r) (_hstart : (q.state 0).live = Finset.univ)
    (_hstep : ∀ k < q.length, ((q.state k).state r).g.IsSymm ∧ ((q.state k).state r).ward t ∧
      ∀ x : (q.state k).live, 1 - ((q.state k).state r).K t x x ≠ 0 ∧
        0 < ((q.state k).state r).q x -
          ((q.state k).state r).p x * ((q.state k).state r).F t x x),
    let E := (q.state q.length).liveᶜ
    let s0 := (q.state 0).ambient r
    pad (q.state q.length).live (1 - ((q.state q.length).state r).K t) =
      pad Eᶜ (schur (1 - s0.K t - q.Jrecord t r (Finset.range q.length)) E) ∧
    pad (q.state q.length).live (((q.state q.length).state r).D t) =
      pad Eᶜ (schur (s0.D t + q.Lrecord t r (Finset.range q.length)) E)

def SchurContractionStmt : Prop :=
  ∀ (P : Type) [Fintype P] [DecidableEq P]
    (B : CMat P) (E : Finset P) (ρ : ℝ) (_hρ : 0 ≤ ρ ∧ ρ < 1) (_hB : ‖B‖ ≤ ρ),
    IsUnit (restrict (1 - B) E) ∧ ‖1 - schur (1 - B) E‖ ≤ ρ

def SchurDualTransportStmt : Prop :=
  ∀ (P : Type) [Fintype P] [DecidableEq P]
    (D L : RMat P) (E : Finset P) (ε : ℝ) (_hε : 0 ≤ ε ∧ ε < 1)
    (_hD : constantKernel D) (_hL : L.IsSymm)
    (_hLzero : L *ᵥ (fun _ => 1) = 0) (_hcap : formAbsLe (qform L) (qform D) ε)
    (_hproper : E ≠ Finset.univ),
    constantKernel (schur (D + L) E) ∧
    ∀ y : (↑(Eᶜ) : Type _) → ℝ, neutral y →
      dualForm (qform D) (fun i => if hi : i ∈ Eᶜ then y ⟨i, hi⟩ else 0) / (1 + ε) ≤
        dualForm (qform (schur (D + L) E)) y ∧
      dualForm (qform (schur (D + L) E)) y ≤
        dualForm (qform D) (fun i => if hi : i ∈ Eᶜ then y ⟨i, hi⟩ else 0) / (1 - ε)

def DuplicationStmt : Prop :=
  ∀ (P I : Type) [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]
    (v : PortMap P I) (s : State I) (t : ℝ)
    (_hmass : ∀ i, v.mass i = 1) (_hk : ∀ x, 0 < v.weight x)
    (_hfix : ∀ i, s.g i i = s.r i) (_hkernel : constantKernel (s.D t))
    (_hp : ∀ i, 0 < s.p i),
    let s0 := v.liftState s
    v.Qᴴ * v.Q = 1 ∧ s0.K t = v.Q * s.K t * v.Qᵀ ∧ ‖s0.K t‖ = ‖s.K t‖ ∧
    (∀ x, s0.fourthRow t Finset.univ x = v.weight x ^ 4 * s.fourthRow t Finset.univ (v.site x)) ∧
    (∀ f, qform (s0.D t) f = qform (s.D t) (v.average f) +
      ∑ x, s.p (v.site x)^2 * v.weight x^4 * (f x - v.average f (v.site x))^2) ∧
    (∀ y, neutral y → s0.X t y = s.X t (v.sumCharge y) +
      (∑ x, y x^2 / (v.weight x^4 * s.p (v.site x)^2)) -
      ∑ i, (v.sumCharge y i)^2 / s.p i^2)

def ReserveTargetStmt : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I]
    (s : State I) (t θ : ℝ) (_hθ : 0 < θ ∧ θ < 1)
    (_hfix : ∀ i, s.g i i = s.r i) (_hp : ∀ i, 0 < s.p i)
    (_hkernel : constantKernel (s.D t)) (y : I → ℝ) (_hy : neutral y),
    θ * ((splitPorts I θ).liftState s).X t (reserveCharge y) =
      θ * s.X t y + (1 - θ) * (∑ i, y i^2 / s.p i^2)

def ReserveScalingStmt : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I]
    (s : State I) (t θ : ℝ) (_hθ : 0 < θ),
    let v : PortMap I I := ⟨id, fun _ => power θ (1 / 4)⟩
    (v.liftState s).h t = s.h (θ * t) ∧
    (v.liftState s).D t = θ • s.D (θ * t) ∧
    (∀ y, θ * (v.liftState s).X t y = s.X (θ * t) y)

/-! ### Scalar facts about the split weights -/

theorem power_rpow (t e : ℝ) : power t e = t ^ e := rfl

theorem quarter_pow_four {a : ℝ} (ha : 0 ≤ a) : (power a (1 / 4)) ^ 4 = a := by
  rw [power_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ha]; norm_num

theorem quarter_mul_self {a : ℝ} (ha : 0 ≤ a) : power a (1 / 4) * power a (1 / 4) = Real.sqrt a := by
  rw [power_rpow, ← Real.rpow_add' ha (by norm_num), Real.sqrt_eq_rpow]; norm_num

theorem quarter_sq {a : ℝ} (ha : 0 ≤ a) : (power a (1 / 4)) ^ 2 = Real.sqrt a := by
  rw [pow_two, quarter_mul_self ha]

theorem quarter_pos {a : ℝ} (ha : 0 < a) : 0 < power a (1 / 4) := Real.rpow_pos_of_pos ha _

theorem splitPorts_mass {n : ℕ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (i : Fin n) :
    (splitPorts (Fin n) θ).mass i = 1 := by
  unfold PortMap.mass
  change (∑ x : Fin n × Bool, _) = 1
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
  · simp only [splitPorts, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
    rw [quarter_pow_four h0, quarter_pow_four (by linarith)]
    ring
  · intro b _ hb
    simp [splitPorts, hb]
  · simp

theorem mask_univ {ι α : Type*} [Fintype ι] [DecidableEq ι] [Zero α] (A : Matrix ι ι α) :
    mask Finset.univ A = A := by
  ext i j; simp [mask, pad, restrict]

/-- Generic smallness of a positive power. -/
theorem power_small {e a : ℝ} (he : 0 < e) (ha : 0 < a) :
    ∃ t0 > 0, ∀ t, 0 < t → t < t0 → power t e < a := by
  refine ⟨a ^ (1 / e), Real.rpow_pos_of_pos ha _, fun t ht htt => ?_⟩
  have h := Real.rpow_lt_rpow ht.le htt he
  rw [power_rpow]
  rwa [← Real.rpow_mul ha.le, one_div_mul_cancel (ne_of_gt he), Real.rpow_one] at h

/-- The reserve-scaling port map. -/
def reserveMap (n : ℕ) (θ : ℝ) : PortMap (Fin n) (Fin n) := ⟨id, fun _ => power θ (1 / 4)⟩

theorem cur_reindex {n : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) (old new : State (Fin n))
    (hr : ∀ i, new.r i = old.r i) (a : LiveState (initialPorts (Fin n)))
    (hL : a.live = reserves) (hg : ∀ i j, a.g (i, true) (j, true) = Real.sqrt θ * new.g i j) :
    State.reindex (reserveEquiv a.live hL) (a.state ((splitPorts (Fin n) θ).liftState old).r) =
      (reserveMap n θ).liftState new := by
  have hw : ((power θ (1 / 4) : ℝ) : ℂ) * ((power θ (1 / 4) : ℝ) : ℂ) = ((Real.sqrt θ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, quarter_mul_self hθ]
  simp only [State.reindex, LiveState.state, PortMap.liftState, reserveMap, restrict,
    submatrix_apply, reserveEquiv]
  congr 1
  · funext i j
    simp only [Equiv.coe_fn_mk, id]
    rw [hg, ← hw]
  · funext i
    simp only [Equiv.coe_fn_mk, splitPorts, if_true, id, hr]

theorem pad_apply_mem {P α : Type*} [Fintype P] [DecidableEq P] [Zero α] (S : Finset P) (A : Matrix S S α) {a b : P}
    (ha : a ∈ S) (hb : b ∈ S) : pad S A a b = A ⟨a, ha⟩ ⟨b, hb⟩ := by
  simp [pad, ha, hb]

theorem submatrix_of_pad_eq {n : ℕ} {α : Type*} [Zero α] (L M : Finset (initialPorts (Fin n)))
    (hL : L = reserves) (hM : M = reserves) (A : Matrix L L α) (B : Matrix M M α)
    (h : pad L A = pad M B) :
    A.submatrix (reserveEquiv L hL) (reserveEquiv L hL) =
      B.submatrix (reserveEquiv M hM) (reserveEquiv M hM) := by
  ext i j
  have h1 := congrFun (congrFun h (i, true)) (j, true)
  have hiL : ((i, true) : initialPorts (Fin n)) ∈ L := hL ▸ mem_reserves_true i
  have hjL : ((j, true) : initialPorts (Fin n)) ∈ L := hL ▸ mem_reserves_true j
  have hiM : ((i, true) : initialPorts (Fin n)) ∈ M := hM ▸ mem_reserves_true i
  have hjM : ((j, true) : initialPorts (Fin n)) ∈ M := hM ▸ mem_reserves_true j
  rw [pad_apply_mem L A hiL hjL, pad_apply_mem M B hiM hjM] at h1
  exact h1

/-- The `K` estimate at the endpoint, from the cumulative Schur identity and contraction. -/
theorem K_from_schur {n : ℕ} (L : Finset (initialPorts (Fin n))) (hL : L = reserves)
    (K : Matrix L L ℂ) (B : CMat (initialPorts (Fin n))) (ρ : ℝ)
    (hpad : pad L (1 - K) = pad Lᶜᶜ (schur (1 - B) Lᶜ))
    (hcon : ‖1 - schur (1 - B) Lᶜ‖ ≤ ρ) :
    ‖K.submatrix (reserveEquiv L hL) (reserveEquiv L hL)‖ ≤ ρ := by
  have hM : Lᶜᶜ = reserves := by rw [compl_compl, hL]
  have h := submatrix_of_pad_eq L Lᶜᶜ hL hM _ _ hpad
  have e : K.submatrix (reserveEquiv L hL) (reserveEquiv L hL) =
      (1 - schur (1 - B) Lᶜ).submatrix (reserveEquiv Lᶜᶜ hM) (reserveEquiv Lᶜᶜ hM) := by
    ext i j
    have hij := congrFun (congrFun h i) j
    simp only [submatrix_apply, Matrix.sub_apply, Matrix.one_apply,
      EmbeddingLike.apply_eq_iff_eq] at hij ⊢
    rw [← hij]; ring
  rw [e, norm_submatrix_equiv]
  exact hcon

/-! ### The diagonal error from the lag cap -/

theorem ward_row {κ : Type*} [Fintype κ] [DecidableEq κ] {s : State κ} {t : ℝ}
    (hw : s.ward t) (i : κ) :
    (∑ j, s.p j * ‖s.h t i j‖ ^ 2) = (s.g i i).im := by
  have hw' : s.h t * diagonal (fun i => (s.p i : ℂ)) * (s.h t)ᴴ = matrixIm s.g := hw
  have h := congrFun (congrFun hw' i) i
  rw [Matrix.mul_apply] at h
  simp only [Matrix.mul_diagonal, conjTranspose_apply, matrixIm] at h
  have h2 := congrArg Complex.re h
  rw [Complex.re_sum, Complex.ofReal_re] at h2
  rw [← h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm (s.h t i j), mul_assoc, Complex.re_ofReal_mul]
  congr 1
  rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

theorem diag_from_lag {κ : Type*} [Fintype κ] [DecidableEq κ] (s : State κ) (t a cp cr : ℝ)
    (hw : s.ward t) (hK : IsUnit (1 - s.K t)) (hlag : ∀ i, ‖s.lag t i‖ ≤ a)
    (hcp : 0 < cp) (hp : ∀ i, cp ≤ s.p i) (hr : ∀ i, ‖s.r i‖ ≤ cr) (ha : 0 ≤ a)
    (hsmall : a / cp ≤ 1 / 2) (i : κ) :
    ‖s.rawLag i‖ ≤ 2 * a * (1 + cr / cp) := by
  have hdet : IsUnit (1 - s.K t).det := (Matrix.isUnit_iff_isUnit_det _).1 hK
  have hraw : s.rawLag = (1 - s.K t) *ᵥ s.lag t := by
    simp only [State.lag, State.P, mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, one_mulVec]
  have hrow : ∀ i, ‖s.rawLag i‖ ≤ a + a * ∑ j, ‖s.h t i j‖ ^ 2 := by
    intro i
    rw [hraw, Matrix.sub_mulVec, one_mulVec, Pi.sub_apply, Matrix.mulVec, dotProduct]
    calc ‖s.lag t i - ∑ j, s.K t i j * s.lag t j‖
        ≤ ‖s.lag t i‖ + ‖∑ j, s.K t i j * s.lag t j‖ := norm_sub_le _ _
      _ ≤ a + ∑ j, ‖s.h t i j‖ ^ 2 * a := by
          refine add_le_add (hlag i) ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_))
          rw [norm_mul]
          have : ‖s.K t i j‖ = ‖s.h t i j‖ ^ 2 := by
            simp [State.K, AndersonAC.Blueprint.entrywiseSquare, norm_pow]
          rw [this]
          exact mul_le_mul_of_nonneg_left (hlag j) (by positivity)
      _ = a + a * ∑ j, ‖s.h t i j‖ ^ 2 := by rw [Finset.mul_sum]; congr 1;
                                              exact Finset.sum_congr rfl fun j _ => by ring
  have hsum : ∑ j, ‖s.h t i j‖ ^ 2 ≤ (cr + ‖s.rawLag i‖) / cp := by
    rw [le_div_iff₀ hcp]
    calc (∑ j, ‖s.h t i j‖ ^ 2) * cp = ∑ j, cp * ‖s.h t i j‖ ^ 2 := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ ∑ j, s.p j * ‖s.h t i j‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hp j) (by positivity)
      _ = (s.g i i).im := ward_row hw i
      _ ≤ ‖s.g i i‖ := Complex.im_le_norm _
      _ ≤ ‖s.r i‖ + ‖s.rawLag i‖ := by
          have : s.g i i = s.r i + s.rawLag i := by simp [State.rawLag]
          rw [this]; exact norm_add_le _ _
      _ ≤ cr + ‖s.rawLag i‖ := by linarith [hr i]
  have h1 := hrow i
  have h2 : a * ∑ j, ‖s.h t i j‖ ^ 2 ≤ a * ((cr + ‖s.rawLag i‖) / cp) :=
    mul_le_mul_of_nonneg_left hsum ha
  have h3 : a * ((cr + ‖s.rawLag i‖) / cp) = a / cp * cr + a / cp * ‖s.rawLag i‖ := by ring
  have h4 : a / cp * ‖s.rawLag i‖ ≤ 1 / 2 * ‖s.rawLag i‖ :=
    mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
  have h5 : a / cp * cr = a * (cr / cp) := by ring
  nlinarith

/-! ### Forms under reindexing -/

section FormReindex

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem qform_submatrix (e : κ ≃ ι) (A : RMat ι) (f : κ → ℝ) :
    qform (A.submatrix e e) f = qform A (f ∘ e.symm) := by
  unfold qform
  rw [← Fintype.sum_equiv e (fun i => f i * (A.submatrix e e *ᵥ f) i)
    (fun i => (f ∘ e.symm) i * (A *ᵥ (f ∘ e.symm)) i) (fun i => ?_)]
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  congr 1
  simp only [Matrix.mulVec, dotProduct, submatrix_apply]
  exact Fintype.sum_equiv e _ _ (fun j => by simp)

theorem dualForm_submatrix (e : κ ≃ ι) (A : RMat ι) (y : κ → ℝ) :
    dualForm (qform (A.submatrix e e)) y = dualForm (qform A) (y ∘ e.symm) := by
  unfold dualForm
  congr 1
  ext a
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨f ∘ e.symm, ?_⟩
    rw [qform_submatrix]
    congr 2
    exact (Fintype.sum_equiv e.symm _ _ (fun i => by simp)).symm
  · rintro ⟨f, rfl⟩
    refine ⟨f ∘ e, ?_⟩
    rw [qform_submatrix]
    have : (f ∘ e) ∘ e.symm = f := by funext i; simp
    rw [this]
    congr 2
    exact Fintype.sum_equiv e.symm _ _ (fun i => by simp)

theorem State.reindex_D (e : κ ≃ ι) (s : State ι) (t : ℝ) :
    (State.reindex e s).D t = (s.D t).submatrix e e := by
  ext i j
  simp only [State.D, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    submatrix_apply, diagonal_apply, EmbeddingLike.apply_eq_iff_eq, State.F, entryAbsSquare,
    State.reindex_h]
  rfl

theorem dualForm_qform_nonneg (A : RMat ι) (y : ι → ℝ) : 0 ≤ dualForm (qform A) y := by
  unfold dualForm
  by_cases hb : BddAbove {a : ℝ | ∃ f : ι → ℝ, a = 2 * (∑ i, y i * f i) - qform A f}
  · exact le_csSup hb ⟨0, by simp [qform]⟩
  · rw [Real.sSup_of_not_bddAbove hb]

end FormReindex

/-! ### The lifted Laplacian keeps the constant kernel -/

theorem State.D_symm {ι : Type*} [Fintype ι] [DecidableEq ι] (s : State ι) (t : ℝ)
    (hsym : s.g.IsSymm) : (s.D t).IsSymm := by
  have hh : ∀ x y, s.h t y x = s.h t x y := fun x y => by
    simp only [State.h, Matrix.smul_apply]; rw [hsym.apply x y]
  ext x y
  simp only [Matrix.transpose_apply, State.D, Matrix.sub_apply, Matrix.diagonal_mul,
    Matrix.mul_diagonal, diagonal_apply, State.F, entryAbsSquare]
  rw [hh x y]
  by_cases hxy : y = x
  · subst hxy; rfl
  · rw [if_neg hxy, if_neg (Ne.symm hxy)]; ring

theorem lifted_g_symm {P I : Type*} [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]
    (v : PortMap P I) (s : State I) (hsym : s.g.IsSymm) : (v.liftState s).g.IsSymm := by
  ext x y
  show (v.weight y : ℂ) * v.weight x * s.g (v.site y) (v.site x) =
    (v.weight x : ℂ) * v.weight y * s.g (v.site x) (v.site y)
  rw [hsym.apply (v.site x) (v.site y)]; ring

theorem lifted_kernel {P I : Type*} [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]
    (v : PortMap P I) (s : State I) (t : ℝ) (hmass : ∀ i, v.mass i = 1)
    (hk : ∀ x, 0 < v.weight x) (hp : ∀ i, 0 < s.p i) (hker : constantKernel (s.D t))
    (hsym : ((v.liftState s).D t).IsSymm)
    (hid : ∀ f, qform ((v.liftState s).D t) f = qform (s.D t) (v.average f) +
      ∑ x, s.p (v.site x)^2 * v.weight x^4 * (f x - v.average f (v.site x))^2) :
    constantKernel ((v.liftState s).D t) := by
  have hterm : ∀ f x, 0 ≤ s.p (v.site x)^2 * v.weight x^4 * (f x - v.average f (v.site x))^2 :=
    fun f x => by positivity
  have hsumnn : ∀ f, 0 ≤ ∑ x, s.p (v.site x)^2 * v.weight x^4 *
      (f x - v.average f (v.site x))^2 := fun f => Finset.sum_nonneg fun x _ => hterm f x
  refine ⟨hsym, fun f => ?_, fun f => ?_⟩
  · rw [hid]; exact add_nonneg (hker.2.1 _) (hsumnn f)
  · rw [hid]
    constructor
    · intro h0
      have h1 : qform (s.D t) (v.average f) = 0 :=
        le_antisymm (by linarith [hsumnn f]) (hker.2.1 _)
      have h2 : ∑ x, s.p (v.site x)^2 * v.weight x^4 * (f x - v.average f (v.site x))^2 = 0 := by
        linarith [hker.2.1 (v.average f)]
      obtain ⟨a, ha⟩ := (hker.2.2 _).1 h1
      refine ⟨a, fun x => ?_⟩
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => hterm f x).1 h2 x (Finset.mem_univ x)
      have hc : 0 < s.p (v.site x)^2 * v.weight x^4 := by
        have := hp (v.site x); have := hk x; positivity
      have h4 : (f x - v.average f (v.site x))^2 = 0 := by
        rcases mul_eq_zero.1 h3 with h | h
        · exact absurd h (ne_of_gt hc)
        · exact h
      have h5 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h4
      rw [← ha (v.site x)]; linarith
    · rintro ⟨a, ha⟩
      have havg : ∀ i, v.average f i = a := by
        intro i
        have hm := hmass i
        unfold PortMap.mass at hm
        unfold PortMap.average
        calc (∑ x, if v.site x = i then v.weight x ^ 4 * f x else 0)
            = (∑ x, if v.site x = i then v.weight x ^ 4 else 0) * a := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun x _ => ?_
              split_ifs <;> simp [ha x]
          _ = a := by rw [hm, one_mul]
      have h1 : qform (s.D t) (v.average f) = 0 := (hker.2.2 _).2 ⟨a, havg⟩
      rw [h1, zero_add]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [ha x, havg]; ring

theorem dualForm_qform_fin0 (A : RMat (Fin 0)) (y : Fin 0 → ℝ) : dualForm (qform A) y = 0 := by
  unfold dualForm
  have : {a : ℝ | ∃ f : Fin 0 → ℝ, a = 2 * (∑ i, y i * f i) - qform A f} = {0} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨f, rfl⟩; simp [qform]
    · rintro rfl; exact ⟨0, by simp [qform]⟩
  rw [this, csSup_singleton]

/-! ### Proposition 5.8 -/

theorem ordinary_sweep_endpoint_of (hcum : CumulativeSchurStmt) (hcon : SchurContractionStmt)
    (hdual : SchurDualTransportStmt) (hdup : DuplicationStmt) (hres : ReserveTargetStmt)
    (hsc : ReserveScalingStmt) (hstepL : StepLLaplacian) :
    ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
    ∀ (n : ℕ) (t θ : ℝ) (old new : State (Fin n))
    (q : Sequence (initialPorts (Fin n))),
    0 < t → t < t0 → 1 / 4 ≤ θ → θ ≤ 5 / 8 →
    (∀ i, new.r i = old.r i ∧ ‖old.r i‖ ≤ C ∧ 1 / C ≤ old.p i ∧ old.p i ≤ C) →
    (∀ i, old.g i i = old.r i) → old.g.IsSymm → old.ward t →
    constantKernel (old.D t) → ‖old.K t‖ ≤ 1 / 3 →
    let r := ((splitPorts (Fin n) θ).liftState old).r
    q.wellFormed t r → (q.state 0).live = Finset.univ →
    (q.state 0).g = ((splitPorts (Fin n) θ).liftState old).g →
    (q.state q.length).live = reserves →
    (∀ i j, (q.state q.length).g (i, true) (j, true) = Real.sqrt θ * new.g i j) →
    (∀ k ≤ q.length, ((q.state k).state r).g.IsSymm ∧ ((q.state k).state r).ward t) →
    (∀ k < q.length, ∀ x : (q.state k).live,
      1 - ((q.state k).state r).K t x x ≠ 0 ∧
      0 < ((q.state k).state r).q x -
        ((q.state k).state r).p x * ((q.state k).state r).F t x x) →
    q.valid t r (((splitPorts (Fin n) θ).liftState old).D t) q.length →
    (∀ i, ((q.state q.length).ambient r).fourthRow t reserves (i, true) ≤
      (θ^2 + C * power t (delta / 2000)) * rowCap t) →
    (∀ y, neutral y →
      (1 - C' * power t (delta / 10)) *
        (θ * old.X t y + (1 - θ) * (∑ i, y i^2 / old.p i^2)) ≤ new.X (θ * t) y ∧
      new.X (θ * t) y ≤ (1 + C' * power t (delta / 10)) *
        (θ * old.X t y + (1 - θ) * (∑ i, y i^2 / old.p i^2))) ∧
    ‖new.K (θ * t)‖ ≤ ‖old.K t‖ + power t (delta / 10) ∧
    (∀ i, ‖new.g i i - old.r i‖ ≤ C' * power t S45.beta) ∧
    (∀ i, new.fourthRow (θ * t) Finset.univ i ≤
      (θ^2 + C' * power t (delta / 2000)) * rowCap t ∧
      new.fourthRow (θ * t) Finset.univ i < (7 / 10 : ℝ) * rowCap (θ * t)) := by
  intro C hC
  have hC0 : 0 < C := by linarith
  obtain ⟨t1, ht1, hmarg⟩ := endpoint_margin_proof C hC0
  obtain ⟨t2, ht2, hεs⟩ := power_small (e := delta / 10) (by norm_num [delta])
    (a := 1 / 2) (by norm_num)
  obtain ⟨t3, ht3, hβs⟩ := power_small (e := S45.beta) (by norm_num [S45.beta, delta])
    (a := 1 / (4 * C)) (by positivity)
  set C' : ℝ := 4 * (1 + 2 * C ^ 2) + C + 2 with hC'def
  have hC'pos : 0 < C' := by positivity
  refine ⟨C', hC'pos, min t1 (min t2 t3), lt_min ht1 (lt_min ht2 ht3), ?_⟩
  intro n t θ old new q ht htt0 hθ1 hθ2 hold hfix hsym hward hker hK0 r hwf hlive0 hg0 hlive
    hgnew hsw hpiv hvalid hrow
  have htt1 : t < t1 := lt_of_lt_of_le htt0 (min_le_left _ _)
  have htt2 : t < t2 := lt_of_lt_of_le htt0 ((min_le_right _ _).trans (min_le_left _ _))
  have htt3 : t < t3 := lt_of_lt_of_le htt0 ((min_le_right _ _).trans (min_le_right _ _))
  have hθpos : 0 < θ := by linarith
  have hθlt : θ < 1 := by linarith
  have hsqrtθ : 1 / 2 ≤ Real.sqrt θ := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hθ1
  have hsqrtθ1 : Real.sqrt θ ≤ 1 := Real.sqrt_le_one.mpr hθlt.le
  have hp_old : ∀ i, 0 < old.p i := fun i =>
    lt_of_lt_of_le (by positivity) (hold i).2.2.1
  set v0 := splitPorts (Fin n) θ with hv0
  set s0 := v0.liftState old with hs0
  have hmass : ∀ i, v0.mass i = 1 := splitPorts_mass hθpos.le hθlt.le
  have hkw : ∀ x, 0 < v0.weight x := by
    intro x
    simp only [hv0, splitPorts]
    split_ifs
    · exact quarter_pos hθpos
    · exact quarter_pos (by linarith)
  obtain ⟨-, -, hKeq, -, hqid, -⟩ := hdup (initialPorts (Fin n)) (Fin n) v0 old t hmass hkw hfix
    hker hp_old
  set ε := power t (delta / 10) with hεdef
  have hε0 : 0 ≤ ε := (Real.rpow_pos_of_pos ht _).le
  have hεlt : ε < 1 / 2 := hεs t ht htt2
  set L := (q.state q.length).live with hLdef
  set cur := (q.state q.length).state r with hcurdef
  set e := reserveEquiv L hlive with hedef
  have hcur : State.reindex e cur = (reserveMap n θ).liftState new :=
    cur_reindex hθpos.le old new (fun i => (hold i).1) (q.state q.length) hlive hgnew
  obtain ⟨hh, hDsc, hXsc⟩ := hsc (Fin n) new t θ hθpos
  have hnewK : new.K (θ * t) = (cur.K t).submatrix e e := by
    rw [← State.reindex_K, hcur]
    show entrywiseSquare (new.h (θ * t)) = entrywiseSquare (((reserveMap n θ).liftState new).h t)
    rw [← hh]; rfl
  -- r has positive imaginary part
  have hrim : ∀ x, (r x).im = power (if x.2 then θ else 1 - θ) (1 / 4) ^ 2 * old.p x.1 := by
    intro x
    simp only [r, hs0, hv0, PortMap.liftState, splitPorts, State.p]
    rw [← Complex.ofReal_pow, Complex.im_ofReal_mul]
  have hrpos : ∀ x, 0 < (r x).im := by
    intro x; rw [hrim]
    have := hkw x
    simp only [hv0, splitPorts] at this
    have := hp_old x.1
    positivity
  -- the initial ambient state is the lifted old state
  have hamb0 : (q.state 0).ambient r = s0 := by
    simp only [LiveState.ambient, hlive0, mask_univ, hg0]
    rfl
  have hstep : ∀ k < q.length, ((q.state k).state r).g.IsSymm ∧ ((q.state k).state r).ward t ∧
      ∀ x : (q.state k).live, 1 - ((q.state k).state r).K t x x ≠ 0 ∧
        0 < ((q.state k).state r).q x -
          ((q.state k).state r).p x * ((q.state k).state r).F t x x := fun k hk =>
    ⟨(hsw k hk.le).1, (hsw k hk.le).2, hpiv k hk⟩
  obtain ⟨hpadK, hpadD⟩ := hcum _ q t r ht hrpos hwf hlive0 hstep
  rw [hamb0] at hpadK hpadD
  -- K
  set B := s0.K t + q.Jrecord t r (Finset.range q.length) with hBdef
  set ρ := ‖old.K t‖ + ε with hρdef
  have hB : ‖B‖ ≤ ρ := by
    refine (norm_add_le _ _).trans ?_
    rw [hKeq]; exact add_le_add le_rfl hvalid.1
  have hρ : 0 ≤ ρ ∧ ρ < 1 := ⟨by positivity, by linarith⟩
  have hcon' := (hcon _ B Lᶜ ρ hρ hB).2
  have hpadK' : pad L (1 - cur.K t) = pad Lᶜᶜ (schur (1 - B) Lᶜ) := by
    rw [hpadK, hBdef, sub_add_eq_sub_sub]
  have hKcur := K_from_schur L hlive (cur.K t) B ρ hpadK' hcon'
  have hKnew : ‖new.K (θ * t)‖ ≤ ‖old.K t‖ + ε := by rw [hnewK]; exact hKcur
  -- diagonal
  have hcurK : ‖cur.K t‖ < 1 := by
    have := hKcur; rw [norm_submatrix_equiv] at this; linarith
  have hunit : IsUnit (1 - cur.K t) := (Units.oneSub (cur.K t) hcurK).isUnit
  have hLres : ∀ x : L, (x : initialPorts (Fin n)).2 = true := fun x => by
    have hx : (x : initialPorts (Fin n)) ∈ (reserves : Finset (initialPorts (Fin n))) :=
      hlive ▸ x.2
    exact (Finset.mem_filter.1 hx).2
  have hcurp : ∀ x : L, 1 / (2 * C) ≤ cur.p x := by
    intro x
    show 1 / (2 * C) ≤ (r x).im
    rw [hrim, if_pos (hLres x), quarter_sq hθpos.le]
    have h1 := (hold (x : initialPorts (Fin n)).1).2.2.1
    calc 1 / (2 * C) = 1 / 2 * (1 / C) := by field_simp
      _ ≤ Real.sqrt θ * old.p (x : initialPorts (Fin n)).1 :=
          mul_le_mul hsqrtθ h1 (by positivity) (by positivity)
  have hcurr : ∀ x : L, ‖cur.r x‖ ≤ C := by
    intro x
    show ‖r x‖ ≤ C
    simp only [r, hs0, hv0, PortMap.liftState, splitPorts, if_pos (hLres x)]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (quarter_pos hθpos), quarter_sq hθpos.le]
    calc Real.sqrt θ * ‖old.r (x : initialPorts (Fin n)).1‖ ≤ 1 * C :=
          mul_le_mul hsqrtθ1 (hold _).2.1 (norm_nonneg _) zero_le_one
      _ = C := one_mul C
  have hβ0 : 0 ≤ power t S45.beta := (Real.rpow_pos_of_pos ht _).le
  have hsmall : power t S45.beta / (1 / (2 * C)) ≤ 1 / 2 := by
    have := hβs t ht htt3
    rw [div_div_eq_mul_div, div_one]
    have h4 : power t S45.beta * (2 * C) ≤ 1 / (4 * C) * (2 * C) :=
      mul_le_mul_of_nonneg_right this.le (by positivity)
    calc power t S45.beta * (2 * C) ≤ 1 / (4 * C) * (2 * C) := h4
      _ = 1 / 2 := by field_simp; ring
  have hdiag := diag_from_lag cur t (power t S45.beta) (1 / (2 * C)) C (hsw _ le_rfl).2 hunit
    hvalid.2.2.2 (by positivity) hcurp hcurr hβ0 hsmall
  have hgii : ∀ i, cur.rawLag (e i) = (Real.sqrt θ : ℂ) * (new.g i i - old.r i) := by
    intro i
    have hg := congrArg (fun s : State (Fin n) => s.g i i) hcur
    have hr := congrArg (fun s : State (Fin n) => s.r i) hcur
    simp only [State.reindex, reserveMap, PortMap.liftState, id] at hg hr
    simp only [State.rawLag]
    rw [hg, hr, (hold i).1, ← Complex.ofReal_mul, ← Complex.ofReal_pow, quarter_mul_self hθpos.le,
      quarter_sq hθpos.le]
    ring
  -- fourth rows
  have hfour : ∀ i, new.fourthRow (θ * t) Finset.univ i =
      ((q.state q.length).ambient r).fourthRow t reserves (i, true) := by
    intro i
    have h1 : new.fourthRow (θ * t) Finset.univ i = cur.fourthRow t Finset.univ (e i) := by
      rw [← State.reindex_fourthRow, hcur]
      simp only [State.fourthRow, ← hh]
      rfl
    rw [h1]
    simp only [State.fourthRow]
    rw [← hlive, ← Finset.sum_coe_sort L]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hi : ((i, true) : initialPorts (Fin n)) ∈ L := hlive ▸ mem_reserves_true i
    have hent : ((q.state q.length).ambient r).h t (i, true) j = cur.h t (e i) j := by
      show (Real.sqrt t : ℂ) * mask L (q.state q.length).g (i, true) j =
        (Real.sqrt t : ℂ) * restrict (q.state q.length).g L (e i) j
      rw [mask, pad_apply_mem L _ hi j.2]
      rfl
    rw [hent]
  refine ⟨fun y hy => ?_, hKnew, fun i => ?_, fun i => ?_⟩
  · -- X sandwich
    have hT := hres (Fin n) old t θ ⟨hθpos, hθlt⟩ hfix hp_old hker y hy
    set X0 := s0.X t (reserveCharge y) with hX0def
    have hX0 : 0 ≤ X0 := dualForm_qform_nonneg _ _
    rw [← hT]
    have hC'1 : 2 ≤ C' := by rw [hC'def]; nlinarith
    by_cases hn : n = 0
    · subst hn
      have h1 : new.X (θ * t) y = 0 := dualForm_qform_fin0 _ _
      have h2 : old.X t y = 0 := dualForm_qform_fin0 _ _
      have h4 : θ * X0 = 0 := by rw [hT, h2]; simp
      rw [h1, h4]; simp
    have hM : Lᶜᶜ = reserves := by rw [compl_compl, hlive]
    have hE : Lᶜ ≠ Finset.univ := by
      intro hc
      have h0 : ((⟨0, Nat.pos_of_ne_zero hn⟩, true) : initialPorts (Fin n)) ∈ L :=
        hlive ▸ mem_reserves_true _
      have : ((⟨0, Nat.pos_of_ne_zero hn⟩, true) : initialPorts (Fin n)) ∈ Lᶜ := by
        rw [hc]; exact Finset.mem_univ _
      exact (Finset.mem_compl.1 this) h0
    set e' := reserveEquiv Lᶜᶜ hM with he'def
    set Lrec := q.Lrecord t r (Finset.range q.length) with hLrecdef
    have hD := submatrix_of_pad_eq L Lᶜᶜ hlive hM _ _ hpadD
    have hXnew : new.X (θ * t) y =
        θ * dualForm (qform (schur (s0.D t + Lrec) Lᶜ)) (y ∘ e'.symm) := by
      rw [← hXsc y]
      change θ * ((reserveMap n θ).liftState new).X t y = _
      rw [← hcur]
      congr 1
      show dualForm (qform ((State.reindex e cur).D t)) y = _
      rw [State.reindex_D, hD, dualForm_submatrix]
    have hkerD0 : constantKernel (s0.D t) :=
      lifted_kernel v0 old t hmass hkw hp_old hker (State.D_symm s0 t (lifted_g_symm v0 old hsym))
        hqid
    have hsteps := hstepL _ q t r hwf (fun k hk => (hsw k hk).1)
    have hLsym : Lrec.IsSymm := by
      show (∑ k ∈ Finset.range q.length, q.stepL t r k)ᵀ = ∑ k ∈ Finset.range q.length, q.stepL t r k
      rw [Matrix.transpose_sum]
      exact Finset.sum_congr rfl fun k hk => (hsteps k (Finset.mem_range.1 hk)).1
    have hLzero : Lrec *ᵥ (fun _ => 1) = 0 := by
      show (∑ k ∈ Finset.range q.length, q.stepL t r k) *ᵥ (fun _ => 1) = 0
      rw [Matrix.sum_mulVec]
      exact Finset.sum_eq_zero fun k hk => (hsteps k (Finset.mem_range.1 hk)).2
    have hd := hdual _ (s0.D t) Lrec Lᶜ ε ⟨hε0, by linarith⟩ hkerD0 hLsym hLzero hvalid.2.1 hE
    have hy' : neutral (y ∘ e'.symm) := by
      unfold neutral at hy ⊢
      rw [← hy]
      exact Fintype.sum_equiv e'.symm _ _ (fun _ => rfl)
    obtain ⟨hlo, hhi⟩ := hd.2 (y ∘ e'.symm) hy'
    have hpadY : (fun i => if hi : i ∈ Lᶜᶜ then (y ∘ e'.symm) ⟨i, hi⟩ else 0) =
        reserveCharge y := by
      funext x
      by_cases hx : x ∈ Lᶜᶜ
      · rw [dif_pos hx]
        have hx2 : x.2 = true := by rw [hM] at hx; exact (Finset.mem_filter.1 hx).2
        simp [reserveCharge, hx2, he'def, reserveEquiv]
      · rw [dif_neg hx]
        have hx2 : x.2 = false := by
          by_contra hc
          apply hx; rw [hM]
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa using hc⟩
        simp [reserveCharge, hx2]
    rw [hpadY] at hlo hhi
    change X0 / (1 + ε) ≤ _ at hlo
    change _ ≤ X0 / (1 - ε) at hhi
    rw [hXnew]
    set Z := dualForm (qform (schur (s0.D t + Lrec) Lᶜ)) (y ∘ e'.symm)
    have h1 : X0 * (1 - ε) ≤ Z := by
      refine le_trans ?_ hlo
      rw [le_div_iff₀ (by linarith)]
      have e1 : X0 * (1 - ε) * (1 + ε) = X0 - X0 * ε ^ 2 := by ring
      rw [e1]; linarith [mul_nonneg hX0 (sq_nonneg ε)]
    have h2 : Z ≤ X0 * (1 + 2 * ε) := by
      refine hhi.trans ?_
      rw [div_le_iff₀ (by linarith)]
      have e1 : X0 * (1 + 2 * ε) * (1 - ε) = X0 + X0 * ε * (1 - 2 * ε) := by ring
      rw [e1]
      have : 0 ≤ X0 * ε * (1 - 2 * ε) :=
        mul_nonneg (mul_nonneg hX0 hε0) (by linarith)
      linarith
    have hw : 0 ≤ θ * X0 := mul_nonneg hθpos.le hX0
    have hCε : 2 * ε ≤ C' * ε := mul_le_mul_of_nonneg_right hC'1 hε0
    constructor
    · calc (1 - C' * ε) * (θ * X0) ≤ (1 - ε) * (θ * X0) :=
            mul_le_mul_of_nonneg_right (by linarith) hw
        _ = θ * (X0 * (1 - ε)) := by ring
        _ ≤ θ * Z := mul_le_mul_of_nonneg_left h1 hθpos.le
    · calc θ * Z ≤ θ * (X0 * (1 + 2 * ε)) := mul_le_mul_of_nonneg_left h2 hθpos.le
        _ = (1 + 2 * ε) * (θ * X0) := by ring
        _ ≤ (1 + C' * ε) * (θ * X0) := mul_le_mul_of_nonneg_right (by linarith) hw
  · have h := hdiag (e i)
    rw [hgii, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] at h
    have h2 : ‖new.g i i - old.r i‖ ≤ 2 * (Real.sqrt θ * ‖new.g i i - old.r i‖) := by
      nlinarith [norm_nonneg (new.g i i - old.r i)]
    have h3 : 2 * (2 * power t S45.beta * (1 + C / (1 / (2 * C)))) = 4 * (1 + 2 * C ^ 2) * power t S45.beta := by
      field_simp; ring
    calc ‖new.g i i - old.r i‖ ≤ 2 * (2 * power t S45.beta * (1 + C / (1 / (2 * C)))) := by linarith
      _ = 4 * (1 + 2 * C ^ 2) * power t S45.beta := h3
      _ ≤ C' * power t S45.beta := mul_le_mul_of_nonneg_right (by rw [hC'def]; linarith) hβ0
  · rw [hfour]
    have hrc : 0 ≤ rowCap t := (Real.rpow_pos_of_pos ht _).le
    have hpw : 0 ≤ power t (delta / 2000) := (Real.rpow_pos_of_pos ht _).le
    refine ⟨(hrow i).trans (mul_le_mul_of_nonneg_right ?_ hrc), ?_⟩
    · have : C ≤ C' := by rw [hC'def]; nlinarith
      nlinarith
    · exact lt_of_le_of_lt (hrow i) (hmarg t θ ht htt1 hθ1 hθ2).1

/-- `schur_contraction` is proved. -/
theorem schurContraction_holds : SchurContractionStmt :=
  fun P _ _ => @schur_contraction_proof P _ _

end AndersonAC.AgentS45
