import AndersonAC.AgentS78.Construction.TilePhase
import AndersonAC.AgentS78.Construction.TileStartAlgebraic
import AndersonAC.AgentS78.Construction.TileStartDecay
import AndersonAC.S45.RestrictLiveActive
import AndersonAC.S45.SweepEndpointProof

/-! Bridge the live-subtype and active-site forms of the duplicated stage start. -/

noncomputable section
set_option autoImplicit false

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

private def activeStartEquiv (θ : ℝ) (z : RunRecord d m) :
    S45.initialPorts {i // i ∈ z.endpoint.active} ≃
      {p : Port d m // p ∈ (sweepStartLiveState θ z).live} where
  toFun p := ⟨(p.1.1, p.2), by
    change ((p.1.1, p.2) : Port d m) ∈
      Finset.univ.filter (fun q : Port d m => q.1 ∈ z.endpoint.active)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.1.2⟩⟩
  invFun p := ((⟨p.1.1, by
    have hp : p.1.1 ∈ z.endpoint.active := by
      simpa [sweepStartLiveState] using p.2
    exact hp⟩, p.1.2))
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl
  right_inv p := by
    apply Subtype.ext
    exact Prod.eta p.1

private theorem activeStartEquiv_port (θ : ℝ) (z : RunRecord d m)
    (p : S45.initialPorts {i // i ∈ z.endpoint.active}) :
    (activeStartEquiv θ z p).1 = ((p.1.1, p.2) : Port d m) := rfl

private theorem activeStartEquiv_bit (θ : ℝ) (z : RunRecord d m)
    (p : S45.initialPorts {i // i ∈ z.endpoint.active}) :
    ((activeStartEquiv θ z p).1).2 = p.2 := rfl

private theorem activeStartEquiv_symm_bit (θ : ℝ) (z : RunRecord d m)
    (p : {p : Port d m // p ∈ (sweepStartLiveState θ z).live}) :
    ((activeStartEquiv θ z).symm p).2 = p.1.2 := by
  have h := congrArg
    (fun q : {p : Port d m // p ∈ (sweepStartLiveState θ z).live} => q.1.2)
    (Equiv.apply_symm_apply (activeStartEquiv θ z) p)
  simpa only [activeStartEquiv_bit] using h

private theorem state_eq_of_fields {I : Type*} (s t : S45.State I)
    (hg : s.g = t.g) (hr : s.r = t.r) : s = t := by
  cases s with
  | mk sg sr =>
    cases t with
    | mk tg tr =>
      dsimp at hg hr
      subst tg
      subst tr
      rfl

private theorem startV3_eq_reindex (P : TilePlan d m) (j : ℕ) (z : RunRecord d m) :
    startV3 P j z.endpoint z.r =
      AgentS45.State.reindex (activeStartEquiv (sweepTheta P.u m j) z)
        (liveStartState P j (sweepStartLiveState (sweepTheta P.u m j) z) z.r) := by
  apply state_eq_of_fields
  · funext p q
    have hp := activeStartEquiv_port (sweepTheta P.u m j) z p
    have hq := activeStartEquiv_port (sweepTheta P.u m j) z q
    change
      ((S45.splitPorts {i // i ∈ z.endpoint.active} (sweepTheta P.u m j)).liftState
          ⟨fun i k => z.endpoint.g i.1 k.1, fun i => z.r i.1⟩).g p q =
        (((S45.splitPorts (Torus d m) (sweepTheta P.u m j)).liftState
          ⟨z.endpoint.g, z.r⟩).g (activeStartEquiv (sweepTheta P.u m j) z p).1
            (activeStartEquiv (sweepTheta P.u m j) z q).1)
    simp [S45.PortMap.liftState, S45.splitPorts, hp, hq]
  · funext p
    have hp := activeStartEquiv_port (sweepTheta P.u m j) z p
    change
      ((S45.splitPorts {i // i ∈ z.endpoint.active} (sweepTheta P.u m j)).liftState
          ⟨fun i k => z.endpoint.g i.1 k.1, fun i => z.r i.1⟩).r p =
        portR (sweepTheta P.u m j) z.r
          (activeStartEquiv (sweepTheta P.u m j) z p).1
    simp [S45.PortMap.liftState, S45.splitPorts, portR, hp]

private def reindexForm {κ ι : Type*} (e : κ ≃ ι) (Q : S45.Form ι) : S45.Form κ :=
  fun f => Q (f ∘ e.symm)

private theorem l1_reindex {κ ι : Type*} [Fintype κ] [Fintype ι]
    (e : κ ≃ ι) (f : κ → ℝ) : S45.l1 (f ∘ e.symm) = S45.l1 f := by
  unfold S45.l1
  exact (Fintype.sum_equiv e _ _ (fun i => by simp)).symm

private theorem l2sq_reindex {κ ι : Type*} [Fintype κ] [Fintype ι]
    (e : κ ≃ ι) (f : κ → ℝ) : S45.l2sq (f ∘ e.symm) = S45.l2sq f := by
  unfold S45.l2sq
  exact (Fintype.sum_equiv e _ _ (fun i => by simp)).symm

private theorem sum_reindex_symm {κ ι α : Type*} [Fintype κ] [Fintype ι]
    [AddCommMonoid α] (e : κ ≃ ι) (f : κ → α) :
    (∑ i : ι, f (e.symm i)) = ∑ i : κ, f i := by
  exact (Fintype.sum_equiv e _ _ (fun i => by simp)).symm

private theorem spatialEnergy_reindex {κ ι I : Type*} [Fintype κ] [Fintype ι]
    [Fintype I] (e : κ ≃ ι) (site : ι → I) (site' : κ → I) (b : ℝ)
    (Λ : S45.Form I) (hsite : ∀ x, site' x = site (e x)) (f : κ → ℝ) :
    S45.spatialEnergy site' b Λ f =
      S45.spatialEnergy site b Λ (f ∘ e.symm) := by
  classical
  unfold S45.spatialEnergy
  congr 1
  ext a
  constructor
  · rintro ⟨α, v, hf, rfl⟩
    refine ⟨α ∘ e.symm, v, ?_, ?_⟩
    · intro i
      have hi := hf (e.symm i)
      simpa [Function.comp_apply, hsite] using hi
    · rw [l2sq_reindex]
  · rintro ⟨α, v, hf, rfl⟩
    refine ⟨α ∘ e, v, ?_, ?_⟩
    · intro i
      have hi := hf (e i)
      simpa [Function.comp_apply, hsite] using hi
    · have hsq := l2sq_reindex e (α ∘ e)
      have hcomp : (α ∘ e) ∘ e.symm = α := by
        funext i
        simp
      rw [hcomp] at hsq
      rw [hsq]

private theorem state_reindex_fourthRow_set {κ ι : Type*} [Fintype κ]
    [DecidableEq κ] [Fintype ι] [DecidableEq ι] (e : κ ≃ ι)
    (s : S45.State ι) (t : ℝ) (C : Finset κ) (i : κ) :
    (AgentS45.State.reindex e s).fourthRow t C i =
      s.fourthRow t (C.map e.toEmbedding) (e i) := by
  simp only [S45.State.fourthRow, Finset.sum_map]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [AgentS45.State.reindex_h]
  rfl

private theorem one_submatrix_equiv {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (e : κ ≃ ι) :
    (1 : Matrix ι ι ℂ).submatrix e e = 1 := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    simp
  · have hne : e i ≠ e j := fun h => hij (e.injective h)
    simp [hij, hne]

private theorem isUnit_submatrix_equiv {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (e : κ ≃ ι) (M : Matrix ι ι ℂ)
    (hM : IsUnit M) : IsUnit (M.submatrix e e) := by
  classical
  obtain ⟨u, rfl⟩ := hM
  refine ⟨⟨((↑u : Matrix ι ι ℂ).submatrix e e),
    ((↑(u⁻¹) : Matrix ι ι ℂ).submatrix e e), ?_, ?_⟩, rfl⟩
  · rw [Matrix.submatrix_mul_equiv _ _ e e e, Units.mul_inv,
      one_submatrix_equiv]
  · rw [Matrix.submatrix_mul_equiv _ _ e e e, Units.inv_mul,
      one_submatrix_equiv]

private theorem inv_submatrix_equiv {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (e : κ ≃ ι) (M : Matrix ι ι ℂ)
    (hM : IsUnit M) :
    ((M.submatrix e e)⁻¹) = (M⁻¹).submatrix e e := by
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).mp hM
  have hU := isUnit_submatrix_equiv e M hM
  have hdetS : IsUnit (M.submatrix e e).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hU
  have h1 : M.submatrix e e * (M⁻¹).submatrix e e = 1 := by
    rw [Matrix.submatrix_mul_equiv _ _ e e e,
      Matrix.mul_nonsing_inv _ hdet, one_submatrix_equiv]
  have h2 : (M⁻¹).submatrix e e * M.submatrix e e = 1 := by
    rw [Matrix.submatrix_mul_equiv _ _ e e e,
      Matrix.nonsing_inv_mul _ hdet, one_submatrix_equiv]
  have hcalc : (M⁻¹).submatrix e e = (M.submatrix e e)⁻¹ := by
    calc
      (M⁻¹).submatrix e e = (M⁻¹).submatrix e e * 1 := (mul_one _).symm
      _ = (M⁻¹).submatrix e e *
          (M.submatrix e e * (M.submatrix e e)⁻¹) := by
            rw [Matrix.mul_nonsing_inv _ hdetS]
      _ = ((M⁻¹).submatrix e e * M.submatrix e e) *
          (M.submatrix e e)⁻¹ := by rw [mul_assoc]
      _ = 1 * (M.submatrix e e)⁻¹ := by rw [h2]
      _ = (M.submatrix e e)⁻¹ := one_mul _
  exact hcalc.symm

private theorem state_reindex_lag {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (e : κ ≃ ι) (s : S45.State ι) (t : ℝ)
    (hU : IsUnit (1 - s.K t)) :
    (AgentS45.State.reindex e s).lag t = s.lag t ∘ e := by
  classical
  let s' := AgentS45.State.reindex e s
  have hM : 1 - s'.K t = (1 - s.K t).submatrix e e := by
    rw [show s'.K t = (s.K t).submatrix e e from AgentS45.State.reindex_K e s t]
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.one_apply, Matrix.sub_apply]
    by_cases hij : i = j
    · subst j
      simp
    · have he : e i ≠ e j := fun h => hij (e.injective h)
      simp [hij, he]
  have hU' : IsUnit (1 - s'.K t) := by
    rw [hM]
    exact isUnit_submatrix_equiv e (1 - s.K t) hU
  have hraw : s'.rawLag = s.rawLag ∘ e := by
    funext i
    rfl
  have hmulOld : (1 - s.K t) *ᵥ s.lag t = s.rawLag := by
    have hdet : IsUnit (1 - s.K t).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp hU
    calc
      (1 - s.K t) *ᵥ s.lag t =
          (1 - s.K t) *ᵥ ((1 - s.K t)⁻¹ *ᵥ s.rawLag) := rfl
      _ = ((1 - s.K t) * (1 - s.K t)⁻¹) *ᵥ s.rawLag := by
        rw [Matrix.mulVec_mulVec]
      _ = s.rawLag := by
        rw [Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hmulCandidate : (1 - s'.K t) *ᵥ (s.lag t ∘ e) = s'.rawLag := by
    rw [hM, hraw, Matrix.submatrix_mulVec_equiv]
    have hcomp : (s.lag t ∘ e) ∘ e.symm = s.lag t := by
      funext i
      simp
    rw [hcomp]
    exact congrArg (fun f => f ∘ e) hmulOld
  have hdet' : IsUnit (1 - s'.K t).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hU'
  have hinv : (1 - s'.K t)⁻¹ *ᵥ s'.rawLag = s'.lag t := rfl
  have hcandidate : (1 - s'.K t)⁻¹ *ᵥ s'.rawLag = s.lag t ∘ e := by
    calc
      (1 - s'.K t)⁻¹ *ᵥ s'.rawLag =
          (1 - s'.K t)⁻¹ *ᵥ ((1 - s'.K t) *ᵥ (s.lag t ∘ e)) := by
            rw [hmulCandidate]
      _ = ((1 - s'.K t)⁻¹ * (1 - s'.K t)) *ᵥ (s.lag t ∘ e) := by
            rw [Matrix.mulVec_mulVec]
      _ = s.lag t ∘ e := by
            rw [Matrix.nonsing_inv_mul _ hdet', Matrix.one_mulVec]
  exact hinv.symm.trans hcandidate

private theorem state_reindex_X {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (e : κ ≃ ι) (s : S45.State ι) (t : ℝ)
    (y : κ → ℝ) :
    (AgentS45.State.reindex e s).X t y = s.X t (y ∘ e.symm) := by
  simp only [S45.State.X, AgentS45.State.reindex_D, AgentS45.dualForm_submatrix]

private theorem constantKernel_reindex {κ ι : Type*} [Fintype κ]
    [DecidableEq κ] [Fintype ι] [DecidableEq ι] (e : κ ≃ ι)
    (D : S45.RMat ι) (hD : S45.constantKernel D) :
    S45.constantKernel (D.submatrix e e) := by
  refine ⟨?_, ?_, ?_⟩
  · apply Matrix.IsSymm.ext
    intro i j
    exact hD.1.apply (e i) (e j)
  · intro f
    rw [AgentS45.qform_submatrix]
    exact hD.2.1 (f ∘ e.symm)
  · intro f
    rw [AgentS45.qform_submatrix]
    constructor
    · intro hzero
      obtain ⟨a, ha⟩ := (hD.2.2 (f ∘ e.symm)).mp hzero
      refine ⟨a, ?_⟩
      intro i
      simpa using ha (e i)
    · rintro ⟨a, ha⟩
      apply (hD.2.2 (f ∘ e.symm)).mpr
      refine ⟨a, ?_⟩
      intro i
      simpa using ha (e.symm i)

private theorem state_reindex_ward {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (e : κ ≃ ι) (s : S45.State ι) (t : ℝ)
    (hward : s.ward t) : (AgentS45.State.reindex e s).ward t := by
  let s' := AgentS45.State.reindex e s
  have hp : Matrix.diagonal (fun i : κ => (s'.p i : ℂ)) =
      (Matrix.diagonal (fun i : ι => (s.p i : ℂ))).submatrix e e := by
    ext i j
    simp only [s', AgentS45.State.reindex, S45.State.p,
      Matrix.submatrix_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst j
      simp
    · have he : e i ≠ e j := fun h => hij (e.injective h)
      simp [hij, he]
  have hstar : ((s.h t).submatrix e e)ᴴ = (s.h t)ᴴ.submatrix e e := by
    ext i j
    simp [Matrix.submatrix_apply]
  have him : S45.matrixIm s'.g = (S45.matrixIm s.g).submatrix e e := by
    ext i j
    rfl
  change s'.h t * Matrix.diagonal (fun i : κ => (s'.p i : ℂ)) * (s'.h t)ᴴ =
    S45.matrixIm s'.g
  rw [AgentS45.State.reindex_h, hp, hstar, him,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  exact congrArg (fun M : S45.CMat ι => M.submatrix e e) hward

private theorem prestate_reindex {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (e : κ ≃ ι) (s : S45.State ι)
    (t C : ℝ) (Λ W : S45.Form ι)
    (h : S45.Prestate t C Λ W s) :
    S45.Prestate t C (reindexForm e Λ) (reindexForm e W)
      (AgentS45.State.reindex e s) := by
  classical
  let s' := AgentS45.State.reindex e s
  refine ⟨h.scale,
    ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro i
    simpa [s', AgentS45.State.reindex, S45.State.p] using h.broad (e i)
  · apply Matrix.IsSymm.ext
    intro i j
    exact h.symmetric.apply (e i) (e j)
  · exact state_reindex_ward e s t h.ward
  · simpa [s', AgentS45.State.reindex_K] using
      (show ‖(s.K t).submatrix e e‖ ≤ 1 / 2 from by
        rw [AgentS45.norm_submatrix_equiv]
        exact h.K_cap)
  · have hM : 1 - s'.K t = (1 - s.K t).submatrix e e := by
      rw [show s'.K t = (s.K t).submatrix e e from AgentS45.State.reindex_K e s t]
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.one_apply, Matrix.sub_apply]
      by_cases hij : i = j
      · subst j
        simp
      · have he : e i ≠ e j := fun h => hij (e.injective h)
        simp [hij, he]
    rw [hM]
    exact isUnit_submatrix_equiv e (1 - s.K t) h.invertible
  · rw [AgentS45.State.reindex_D]
    exact constantKernel_reindex e (s.D t) h.kernel
  · intro i
    rw [AgentS45.State.reindex_fourthRow]
    simpa using h.row_cap (e i)
  · intro i
    simpa [state_reindex_lag e s t h.invertible] using h.lag_cap (e i)
  · intro y hy
    have hy' : S45.neutral (y ∘ e.symm) := by
      unfold S45.neutral at hy ⊢
      change (∑ i : ι, y (e.symm i)) = 0
      rw [sum_reindex_symm e y]
      exact hy
    have hsum :
        (∑ i : κ, y i ^ 2 / (s'.p i) ^ 2) =
          ∑ i : ι, (y ∘ e.symm) i ^ 2 / (s.p i) ^ 2 := by
      simpa [s', AgentS45.State.reindex, S45.State.p, Function.comp_apply] using
        (sum_reindex_symm e (fun i : κ => y i ^ 2 / (s.p (e i)) ^ 2)).symm
    have hX : s'.X t y = s.X t (y ∘ e.symm) := by
      simpa [s'] using state_reindex_X e s t y
    rw [hX, hsum]
    exact h.sharp (y ∘ e.symm) hy'
  · intro y hy
    have hy' : S45.neutral (y ∘ e.symm) := by
      unfold S45.neutral at hy ⊢
      change (∑ i : ι, y (e.symm i)) = 0
      rw [sum_reindex_symm e y]
      exact hy
    simpa [reindexForm, l1_reindex, l2sq_reindex] using
      h.fourier (y ∘ e.symm) hy'
  · intro y hy
    have hy' : S45.neutral (y ∘ e.symm) := by
      unfold S45.neutral at hy ⊢
      change (∑ i : ι, y (e.symm i)) = 0
      rw [sum_reindex_symm e y]
      exact hy
    simpa [reindexForm, l1_reindex, l2sq_reindex] using
      h.dual_fourier (y ∘ e.symm) hy'
  · rw [Fintype.card_congr e]
    exact h.volume

/-- Convert the live-subtype stage-start clauses to the active-site-port form
used by TilePhase.StartClauses. -/
theorem startClauses_of_live (C : ℝ) (P : TilePlan d m) (j : ℕ)
    (z : RunRecord d m)
    (h1 : StartAlgebraicLive C P j
      (sweepStartLiveState (sweepTheta P.u m j) z) z.r)
    (h2 : StartDecayLive C P j
      (sweepStartLiveState (sweepTheta P.u m j) z) z.r) :
    StartClauses C P j z.endpoint z.r
      (sweepStartLiveState (sweepTheta P.u m j) z) := by
  classical
  let θ := sweepTheta P.u m j
  let a := sweepStartLiveState θ z
  let e := activeStartEquiv θ z
  let s := liveStartState P j a z.r
  have hstate : startV3 P j z.endpoint z.r = AgentS45.State.reindex e s := by
    exact startV3_eq_reindex P j z
  rcases h1.start_prestate with ⟨Λ, W, hPre, hKcap, hΛnonneg, hSharp⟩
  let Λ' : S45.Form (S45.initialPorts {i // i ∈ z.endpoint.active}) :=
    reindexForm e Λ
  let W' : S45.Form (S45.initialPorts {i // i ∈ z.endpoint.active}) :=
    reindexForm e W
  have hPre' : S45.Prestate (sweepScale P.u m j) C Λ' W'
      (startV3 P j z.endpoint z.r) := by
    rw [hstate]
    exact prestate_reindex e s (sweepScale P.u m j) C Λ W hPre
  have hKcap' : ‖(startV3 P j z.endpoint z.r).K (sweepScale P.u m j)‖ ≤ 1 / 3 := by
    rw [hstate, AgentS45.State.reindex_K, AgentS45.norm_submatrix_equiv]
    exact hKcap
  have hΛnonneg' : ∀ y, S45.neutral y → 0 ≤ Λ' y := by
    intro y hy
    have hy' : S45.neutral (y ∘ e.symm) := by
      unfold S45.neutral at hy ⊢
      change (∑ i : a.live, y (e.symm i)) = 0
      rw [sum_reindex_symm e y]
      exact hy
    exact hΛnonneg (y ∘ e.symm) hy'
  have hSharp' : ∀ y, S45.neutral y →
      (startV3 P j z.endpoint z.r).X (sweepScale P.u m j) y ≤
        (1 + S45.power (sweepScale P.u m j) S45.kappa) *
          (∑ i, y i ^ 2 / (startV3 P j z.endpoint z.r).p i ^ 2) +
          C * sweepScale P.u m j * Λ' y := by
    intro y hy
    have hy' : S45.neutral (y ∘ e.symm) := by
      unfold S45.neutral at hy ⊢
      change (∑ i : a.live, y (e.symm i)) = 0
      rw [sum_reindex_symm e y]
      exact hy
    have hsum :
        (∑ i : S45.initialPorts {i // i ∈ z.endpoint.active},
          y i ^ 2 / ((AgentS45.State.reindex e s).p i) ^ 2) =
        ∑ i : a.live, (y ∘ e.symm) i ^ 2 / (s.p i) ^ 2 := by
      simpa [AgentS45.State.reindex, S45.State.p, Function.comp_apply] using
        (sum_reindex_symm e
          (fun i : S45.initialPorts {i // i ∈ z.endpoint.active} =>
            y i ^ 2 / (s.p (e i)) ^ 2)).symm
    rw [hstate, state_reindex_X, hsum]
    simpa [Λ', reindexForm] using hSharp (y ∘ e.symm) hy'
  have hcomparison : S45.formComparable
      (S45.qform ((startV3 P j z.endpoint z.r).D (sweepScale P.u m j)))
      (S45.spatialEnergy
        (fun p : S45.initialPorts {i // i ∈ z.endpoint.active} =>
          (P.cover j).cover.site ((p.1.1, p.2) : Port d m))
        (P.cover j).b (P.cover j).cover.energy) C := by
    let siteOld : a.live → Torus d m := fun x => (P.cover j).cover.site x.1
    let siteNew : S45.initialPorts {i // i ∈ z.endpoint.active} → Torus d m :=
      fun p => (P.cover j).cover.site ((p.1.1, p.2) : Port d m)
    have hsite : ∀ p, siteNew p = siteOld (e p) := by
      intro p
      dsimp [siteNew, siteOld, e]
      exact congrArg (P.cover j).cover.site
        (activeStartEquiv_port θ z p).symm
    intro f
    have hq : S45.qform
        ((startV3 P j z.endpoint z.r).D (sweepScale P.u m j)) f =
        S45.qform (s.D (sweepScale P.u m j)) (f ∘ e.symm) := by
      rw [hstate, AgentS45.State.reindex_D, AgentS45.qform_submatrix]
    have hR := spatialEnergy_reindex e siteOld siteNew (P.cover j).b
      (P.cover j).cover.energy hsite f
    rw [hq, hR]
    exact h1.start_comparison (f ∘ e.symm)
  have hreserve :
      (S45.reserves : Finset (S45.initialPorts {i // i ∈ z.endpoint.active})).map
        e.toEmbedding =
      Finset.univ.filter (fun x : a.live => x.1.2 = true) := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_map.mp hx with ⟨p, hp, rfl⟩
      have hpbit : p.2 = true := (Finset.mem_filter.mp hp).2
      have hbit : (e p).1.2 = true := by
        change ((activeStartEquiv θ z p).1).2 = true
        rw [activeStartEquiv_bit]
        exact hpbit
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbit⟩
    · intro hx
      have hxbit : x.1.2 = true := (Finset.mem_filter.mp hx).2
      refine Finset.mem_map.mpr ⟨e.symm x, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_univ _
        · have hbit := activeStartEquiv_symm_bit θ z x
          simpa [e] using hbit.trans hxbit
      · exact Equiv.apply_symm_apply e x
  refine ⟨?_, ?_, hcomparison, ?_, ?_, ?_, ?_, h2.prefix_decay⟩
  · exact ⟨Λ', W', hPre', hKcap', hΛnonneg', hSharp'⟩
  · intro i
    have hLagAmbient := h1.start_lag (e i).1
    have hLagOld : s.lag (sweepScale P.u m j) (e i) = 0 := by
      change (if hp : (e i).1 ∈ a.live then
        (a.state (portR θ z.r)).lag (sweepScale P.u m j) ⟨(e i).1, hp⟩ else 0) = 0 at hLagAmbient
      rw [dif_pos (e i).2] at hLagAmbient
      simpa [s, liveStartState] using hLagAmbient
    rw [hstate, state_reindex_lag e s (sweepScale P.u m j) hPre.invertible]
    exact hLagOld
  · intro i
    rw [hstate, AgentS45.State.reindex_fourthRow]
    simpa using h1.start_rows (e i)
  · intro i hi
    have hrow := state_reindex_fourthRow_set e s (sweepScale P.u m j)
      S45.reserves i
    rw [hstate]
    rw [hreserve] at hrow
    have hbit : (e i).1.2 = true := by
      change ((activeStartEquiv θ z i).1).2 = true
      rw [activeStartEquiv_bit]
      exact (Finset.mem_filter.mp hi).2
    rw [hrow]
    exact h1.start_reserve_rows (e i) hbit
  · intro p q
    rw [hstate, AgentS45.State.reindex_h]
    have hp : (e p).1 = ((p.1.1, p.2) : Port d m) :=
      activeStartEquiv_port θ z p
    have hq : (e q).1 = ((q.1.1, q.2) : Port d m) :=
      activeStartEquiv_port θ z q
    simpa [hp, hq] using h2.start_decay (e p) (e q)
  · intro p q hdist
    rw [hstate, AgentS45.State.reindex_h]
    apply h2.start_far_decay (e p) (e q)
    have hp : (e p).1 = ((p.1.1, p.2) : Port d m) :=
      activeStartEquiv_port θ z p
    have hq : (e q).1 = ((q.1.1, q.2) : Port d m) :=
      activeStartEquiv_port θ z q
    simpa [hp, hq] using hdist

end AndersonAC.AgentS78

end
