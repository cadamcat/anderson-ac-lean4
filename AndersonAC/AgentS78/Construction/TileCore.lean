import AndersonAC.AgentS78.Construction.TileTrial

/-!
# the first tile trial as an ordered monitored process. Split of `TileCrossingStatement` (TileTrial.lean) into four
pieces (05-local-sweeps.tex:766–870, Lemma `local-trial`):

* **slot recursion** `TileSlotDescriptionStatement` — the first trial of `tileBlock` from a non-aborted
  record is the slot recursion `slotSeq` driven by the first order `π_{j,T,0}` and a fixed
  site-value function of the signs: `localFirstFail = {slotSeq … N = none}`.
* **tile slot law** `TileSlotLawStatement` — `S45.UniformSlotLaw` for (run, remaining, slot, ξ) with the
  history filtration `tileFiltration` under `sourcesLaw`, for every predictable `run`.
* **monitor bounds** `TileMonitorBoundsStatement` — the four monitored records (`tileEval`, padded to one
  common space) satisfy the measurability / Hermitian / mean / stack / jump hypotheses of
  `S45.ordered_raw_bounds` at running slots.
* **budget crossing** `TileFailCrossingStatement` — a failed slot recursion crosses a monitored budget
  (S45.local_transfer, Lemma `local-prospective`).

The assembly `TileCrossingStatement` from slot recursion–budget crossing, `S45.ordered_raw_bounds` and
`S45.ordered_trial_inputs` is `tileCrossing_of_pieces` (TileCoreAssembly.lean).

Indexing. Sites are encoded in `Fin (siteCount d m)` by `siteRank` (the site type of
`S45.ordered_raw_bounds`). `N = |T|` slots; slot `k < N` exposes the site at position
`π_{j,T,0}(k)` of the tile in the fixed site order (as `exposedSite`).

Site values (05:345–359). The physical increment `ζ_i` of a site is a fixed function of the
signs: at an active coupled site the true digit `√(3 s_{j−1}/4) ε_{i,h}` (`h = prefixLength i`),
or at the final sweep the whole true suffix from `h`; at an active pending site the designated
auxiliary sign of family 0; at an inactive site (never used: its slot is skipped) the dummy
`√(w t) ε^{aux}_{j,T,0,i}`, so that every slot value has the moment law `(0, t)` after the
normalization `ξ = ζ/√w` (normalized scalar of `S45.StepRel`, 04:198–228).
-/

open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer sourcesLaw signValue binarySuffix)

section Core
variable {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)

/-- Number of slots `N = |T|`. -/
abbrev slotCount : ℕ := (tileSites (P.cover j) T).card

/-- The site exposed at slot `k` of the first trial (`π_{j,T,0}(k)`-th site of the tile). -/
def tileSlot (k : ℕ) (ω : RandomSources (Torus d m) M) : Torus d m :=
  if h : k < M (tileOrderIndex j T 0) then
    (siteAt (tileSites (P.cover j) T) (ω.2 (tileOrderIndex j T 0) ⟨k, h⟩).val).getD (site₀ d m)
  else site₀ d m

open Classical in
/-- The physical increment `ζ_i` of site `i` in the first trial (see the header). -/
def tileZeta (x : RunRecord d m) (i : Torus d m) (ω : RandomSources (Torus d m) M) : ℝ :=
  if activeIn P j T x i then
    (if i ∉ x.pending then
      (if IsFinalSweep m j then
        binarySuffix (couplingOf P.u P.n₀) (x.prefixLength i) (fun k => ω.1 (Sum.inl (i, k)))
      else digitAmp P.u (j - 1) * signValue (ω.1 (Sum.inl (i, x.prefixLength i))))
    else digitAmp P.u (j - 1) * signValue (ω.1 (Sum.inr (tileAuxIndex j T 0 i))))
  else Real.sqrt (sweepW P.u m j * sweepScale P.u m j) *
    signValue (ω.1 (Sum.inr (tileAuxIndex j T 0 i)))

/-- The normalized scalar `ξ = ζ/√w` of slot `k`. -/
def tileXi (x : RunRecord d m) (k : ℕ) (ω : RandomSources (Torus d m) M) : ℝ :=
  tileZeta P j T M x (tileSlot P j T M k ω) ω / Real.sqrt (sweepW P.u m j)

/-- The candidate update of the included prefix `q` at site `i` with normalized scalar `ξ`. -/
def candidate (x : RunRecord d m) (q : S45.Sequence (Port d m)) (i : Torus d m) (ξ : ℝ) :
    S45.Sequence (Port d m) :=
  extendSeq q (stepLive (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r)
    (q.state q.length) (i, false) ξ) (i, false) ξ

open Classical in
/-- One slot of the first trial on the included prefix `q` (05:338–344, 466–504): skip an
inactive or already deleted site; otherwise delete its bit port and test (`trialOk`).
`none` = the trial fails at this slot. -/
def slotStep (x : RunRecord d m) (q : S45.Sequence (Port d m)) (i : Torus d m) (ξ : ℝ) :
    Option (S45.Sequence (Port d m)) :=
  if activeIn P j T x i ∧ ((i, false) : Port d m) ∈ (q.state q.length).live then
    (if trialOk P j T x (candidate P j x q i ξ)
        (stepDen (sweepScale P.u m j) (portR (sweepTheta P.u m j) x.r) (q.state q.length)
          (i, false) ξ)
      then some (candidate P j x q i ξ) else none)
  else some q

/-- The included prefix after slots `0, …, k−1` (`none` once the trial has failed). -/
def slotSeq (x : RunRecord d m) : ℕ → RandomSources (Torus d m) M →
    Option (S45.Sequence (Port d m))
  | 0 => fun _ => some x.sweep
  | k + 1 => fun ω =>
    if k < slotCount P j T then
      (slotSeq x k ω).bind fun q => slotStep P j T x q (tileSlot P j T M k ω) (tileXi P j T M x k ω)
    else slotSeq x k ω

/-- The trial is still running before slot `k` (predictable stopping multiplier `s_k`). -/
def tileRun (x : RunRecord d m) (k : ℕ) (ω : RandomSources (Torus d m) M) : Bool :=
  (slotSeq P j T M x k ω).isSome

/-- Encoded slot site. -/
def tileSlotF (k : ℕ) (ω : RandomSources (Torus d m) M) : Fin (siteCount d m) :=
  siteRank d m (tileSlot P j T M k ω)

open Classical in
/-- Unexposed sites of the tile before slot `k`, encoded. -/
def tileRemaining (k : ℕ) (ω : RandomSources (Torus d m) M) : Finset (Fin (siteCount d m)) :=
  ((tileSites (P.cover j) T).image (siteRank d m)) \
    ((Finset.range k).image fun l => tileSlotF P j T M l ω)

/-- The revealed history before slot `k`: the exposed sites and their normalized scalars. -/
def tileHist (x : RunRecord d m) (k : ℕ) (ω : RandomSources (Torus d m) M) :
    Fin k → ℕ × ℝ :=
  fun l => ((tileSlotF P j T M l ω : ℕ), tileXi P j T M x l ω)

theorem tileHist_comap_mono (x : RunRecord d m) {k k' : ℕ} (h : k ≤ k') :
    MeasurableSpace.comap (tileHist P j T M x k) inferInstance ≤
      MeasurableSpace.comap (tileHist P j T M x k') inferInstance := by
  have hfac : tileHist P j T M x k =
      (fun f : Fin k' → ℕ × ℝ => fun l : Fin k => f (Fin.castLE h l)) ∘ tileHist P j T M x k' := by
    funext ω l; rfl
  rw [hfac, ← MeasurableSpace.comap_comp]
  have hm : Measurable (fun f : Fin k' → ℕ × ℝ => fun l : Fin k => f (Fin.castLE h l)) := by
    fun_prop
  exact MeasurableSpace.comap_mono hm.comap_le

/-- The history filtration of the first trial: `ℱ k` = σ(slots `< k` and their scalars). -/
def tileFiltration (x : RunRecord d m) :
    Filtration ℕ (inferInstance : MeasurableSpace (RandomSources (Torus d m) M)) where
  seq k := MeasurableSpace.comap (tileHist P j T M x k) inferInstance ⊓ inferInstance
  mono' _ _ h := inf_le_inf_right _ (tileHist_comap_mono P j T M x h)
  le' _ := inf_le_right

/-! ### The monitored records (05:399–419, 452–462, 795–842) -/

/-- Inner ports of the tile cube `P₀ ∩ Q_T`. -/
abbrev innerPorts : Finset (Port d m) := (P.cover j).cover.inner T

/-- Dimension of the local coordinates `H_T`. -/
abbrev localDim : ℕ := (P.cover j).cover.dim T

/-- Number of monitors: lag, full row and reserve row at each inner port, then `J` and `L`. -/
def monitorCount : ℕ := 3 * (innerPorts P j T).card + 2

/-- Common padded dimension `D = 2|P₀ ∩ Q_T| + 2 dim H_T + 2`. -/
def monitorDim : ℕ := 2 * (innerPorts P j T).card + 2 * localDim P j T + 2

/-- Kind of a monitor. -/
def monitorKind (i : Fin (monitorCount P j T)) : S45.MonitorKind :=
  if i.val < (innerPorts P j T).card then .lag
  else if i.val < 3 * (innerPorts P j T).card then .row else .matrix

/-- Pad a matrix on a finite index type into the common space along an embedding. -/
def padInto {α : Type} [Fintype α] [DecidableEq α] (D : ℕ) (e : α → Fin D) (A : S45.CMat α) :
    S45.CMat (Fin D) :=
  fun a b => ∑ x, ∑ y, if e x = a ∧ e y = b then A x y else 0

/-- Embedding of the `J` dilation space `P₀∩Q_T ⊕ P₀∩Q_T` into `Fin D` (first block). -/
def embJ (z : (innerPorts P j T) ⊕ (innerPorts P j T)) : Fin (monitorDim P j T) :=
  match z with
  | Sum.inl p => ⟨((innerPorts P j T).equivFin p : ℕ), by
      have := ((innerPorts P j T).equivFin p).isLt; unfold monitorDim; omega⟩
  | Sum.inr p => ⟨(innerPorts P j T).card + ((innerPorts P j T).equivFin p : ℕ), by
      have := ((innerPorts P j T).equivFin p).isLt; unfold monitorDim; omega⟩

/-- Embedding of the `L` dilation space `H_T ⊕ H_T` into `Fin D` (second block). -/
def embL (z : Fin (localDim P j T) ⊕ Fin (localDim P j T)) : Fin (monitorDim P j T) :=
  match z with
  | Sum.inl a => ⟨2 * (innerPorts P j T).card + a, by have := a.isLt; unfold monitorDim; omega⟩
  | Sum.inr a => ⟨2 * (innerPorts P j T).card + localDim P j T + a, by
      have := a.isLt; unfold monitorDim; omega⟩

/-- Embedding of a scalar monitor's `Fin 2` into `Fin D` (last two coordinates). -/
def embS (a : Fin 2) : Fin (monitorDim P j T) :=
  ⟨2 * (innerPorts P j T).card + 2 * localDim P j T + a, by
    have := a.isLt; unfold monitorDim; omega⟩

/-- Scalar dilation `[[0, u], [ū, 0]]` (lag coordinates). -/
def scalarDilation (u : ℂ) : S45.CMat (Fin 2) := !![0, u; star u, 0]

/-- Real scalar as a `1 × 1` block in `Fin 2` (row proxies). -/
def scalarBlock (a : ℝ) : S45.CMat (Fin 2) := !![(a : ℂ), 0; 0, 0]

open Classical in
/-- **The monitored increment** of monitor `i` at slot `k` when the exposed site is `y` with
normalized scalar `z`, evaluated at the current included prefix (`tileRun` ensures it is the
valid prestate): the step increments of `S45.Sequence` at the candidate step, i.e. the lag
increment at an inner port, the normalized full-row / reserve-row proxy increments at an inner
port, the `J` increment compressed to `P₀ ∩ Q_T` (dilation), and the pulled-back `L` increment
`B_Tᵀ L B_T` (dilation, the local coordinates are orthonormal so the Riesz map is the
identity). Zero at a skipped slot. All padded into `Fin D`. -/
def tileEval (x : RunRecord d m) (i : Fin (monitorCount P j T)) (k : ℕ)
    (ω : RandomSources (Torus d m) M) (y : Fin (siteCount d m)) (z : ℝ) :
    S45.CMat (Fin (monitorDim P j T)) :=
  let q := (slotSeq P j T M x k ω).getD x.sweep
  let site := (siteRank d m).symm y
  let t := sweepScale P.u m j
  let r := portR (sweepTheta P.u m j) x.r
  let c := candidate P j x q site z
  let n := (innerPorts P j T).card
  if activeIn P j T x site ∧ ((site, false) : Port d m) ∈ (q.state q.length).live then
    if h1 : i.val < n then
      padInto _ (embS P j T) (scalarDilation (c.stepLag t r q.length
        ((innerPorts P j T).equivFin.symm ⟨i.val, h1⟩)))
    else if h2 : i.val < 2 * n then
      padInto _ (embS P j T) (scalarBlock (c.stepRow t r Finset.univ q.length
        ((innerPorts P j T).equivFin.symm ⟨i.val - n, by omega⟩)))
    else if h3 : i.val < 3 * n then
      padInto _ (embS P j T) (scalarBlock (c.stepRow t r S45.reserves q.length
        ((innerPorts P j T).equivFin.symm ⟨i.val - 2 * n, by omega⟩)))
    else if i.val = 3 * n then
      padInto _ (embJ P j T) (S45.dilation (S45.restrict (c.stepJ t r q.length) (innerPorts P j T)))
    else
      padInto _ (embL P j T) (S45.dilation ((S45.pullback ((P.cover j).cover.coords T).B
        (c.stepL t r q.length)).map (fun a => (a : ℂ))))
  else 0

end Core

/-! ## The four pieces -/

/-- **slot recursion (slot-level description, deterministic).** The first trial of the tile block from a
non-aborted record fails exactly when the slot recursion fails; the first `k ≤ N` slots are
distinct sites of the tile (`π_{j,T,0}` is a permutation of `|T|` entries). -/
def TileSlotDescriptionStatement : Prop :=
  ∀ (d m : ℕ) (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count) (M : ℕ → ℕ)
    (x : RunRecord d m), TileOrderSizes P j T M → x.aborted = false →
    localFirstFail M (tileBlock P j T) x =
      {ω | slotSeq P j T M x (slotCount P j T) ω = none} ∧
    ∀ k ≤ slotCount P j T, ∀ ω, (tileRemaining P j T M k ω).card = slotCount P j T - k

/-- **tile slot law (uniform slot law, probabilistic).** Under `sourcesLaw`, for every predictable
continuation flag, the exposed slot is conditionally uniform among the unexposed sites and its
normalized scalar has conditional mean `0`, variance `t`, and `|ξ| ≤ 2√t`
(05:776–785; Lemma `conditional-freshness` on the raw product space). -/
def TileSlotLawStatement : Prop :=
  ∀ (d m : ℕ) (C : ℝ) (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (M : ℕ → ℕ) (x : RunRecord d m),
    P.u ∈ Set.Ioc (1 / 4 : ℝ) 1 → P.n₀ < j → j ≤ m + 1 → TileOrderSizes P j T M →
    x.aborted = false → TileGoodCore C P j T x →
    ∀ run : ℕ → RandomSources (Torus d m) M → Bool,
      (∀ k < slotCount P j T, @Measurable _ Bool (tileFiltration P j T M x k) ⊤ (run k)) →
      S45.UniformSlotLaw (sourcesLaw (Torus d m) M) (tileFiltration P j T M x)
        (slotCount P j T) (sweepScale P.u m j) 2 run (tileRemaining P j T M)
        (tileSlotF P j T M) (tileXi P j T M x)

/-- **monitor bounds (monitored increment bounds, deterministic).** For each `C ≥ 1` there are `C' ≥ 2`
and `t0 > 0` such that the monitored increments of a good record satisfy the measurability,
Hermitian, mean, stack and jump hypotheses of `S45.ordered_raw_bounds` with constant `C'`,
at every running slot, and the continuation flag `tileRun` is predictable (05:795–842; Proposition `sweep-increments`, Lemma `local-pullback`). -/
def TileMonitorBoundsStatement (d : ℕ) (C : ℝ) : Prop :=
  ∃ C' ≥ 2, ∃ t0 > 0, ∀ (m : ℕ) (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (M : ℕ → ℕ) (x : RunRecord d m),
    P.u ∈ Set.Ioc (1 / 4 : ℝ) 1 → P.n₀ < j → j ≤ m + 1 → TileOrderSizes P j T M →
    x.aborted = false → TileGoodCore C P j T x → sweepScale P.u m j < t0 →
    let t := sweepScale P.u m j
    let N := slotCount P j T
    let ℱ := tileFiltration P j T M x
    let run := tileRun P j T M x
    let remaining := tileRemaining P j T M
    let eval := tileEval P j T M x
    let kind := monitorKind P j T
    (∀ k < N, @Measurable _ Bool (ℱ k) ⊤ (run k)) ∧
    (∀ i k y, @StronglyMeasurable (RandomSources (Torus d m) M × ℝ)
      (S45.CMat (Fin (monitorDim P j T))) _ ((ℱ k).prod (borel ℝ))
      (fun a => eval i k a.1 y a.2)) ∧
    (∀ i k ω y z, (eval i k ω y z).IsHermitian) ∧
    (∀ i k, k < N → ∀ ω, run k ω = true →
      ∀ (ρ : Fin (siteCount d m) → Measure ℝ), (∀ y, IsProbabilityMeasure (ρ y)) →
      (∀ y ∈ remaining k ω, S45.MomentLaw (ρ y) t C' id) →
      ‖∑ y ∈ remaining k ω, ∫ z, eval i k ω y z ∂(ρ y)‖ ≤
        C' * S45.monitorBias t (kind i) / S45.logFactor t) ∧
    (∀ i k, k < N → ∀ ω, run k ω = true → ∀ z : Fin (siteCount d m) → ℝ,
      (∀ y ∈ remaining k ω, |z y| ≤ C' * Real.sqrt t) →
      (∑ y ∈ remaining k ω, (eval i k ω y (z y))^2) ≤
        (C' * S45.monitorVariance t (kind i) / S45.logFactor t) •
          (1 : S45.CMat (Fin (monitorDim P j T)))) ∧
    (∀ i k, k < N → ∀ ω, run k ω = true → ∀ y ∈ remaining k ω,
      ∀ z, |z| ≤ C' * Real.sqrt t → ‖eval i k ω y z‖ ≤ C' * S45.monitorJump t (kind i))

/-- The stopped monitored records (the raw increments built by `S45.ordered_raw_bounds`). -/
def tileRaw {d m : ℕ} (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (M : ℕ → ℕ) (x : RunRecord d m) (i : Fin (monitorCount P j T)) :
    ℕ → RandomSources (Torus d m) M → S45.CMat (Fin (monitorDim P j T))
  | 0 => fun _ => 0
  | k + 1 => fun ω => if k < slotCount P j T ∧ tileRun P j T M x k ω = true then
      tileEval P j T M x i k ω (tileSlotF P j T M k ω) (tileXi P j T M x k ω) else 0

/-- **budget crossing (failure crosses a budget, deterministic).** For each `C ≥ 1`, for small `t`, if the
slot recursion of a good record fails then some stopped monitored record exceeds its local
budget (05:844–860: a failure without a budget crossing contradicts Lemma `local-transfer`,
whose tails come from Lemma `local-prospective`). -/
def TileFailCrossingStatement (d : ℕ) (C : ℝ) : Prop :=
  ∃ t0 > 0, ∀ (m : ℕ) (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (M : ℕ → ℕ) (x : RunRecord d m),
    P.u ∈ Set.Ioc (1 / 4 : ℝ) 1 → P.n₀ < j → j ≤ m + 1 → TileOrderSizes P j T M →
    x.aborted = false → TileGoodCore C P j T x → sweepScale P.u m j < t0 →
    ∀ ω, slotSeq P j T M x (slotCount P j T) ω = none →
      ∃ i n, S45.monitorBudget (sweepScale P.u m j) (monitorKind P j T i) <
        ‖S45.partialSum (tileRaw P j T M x i) n ω‖

end AndersonAC.AgentS78
