import AndersonAC.AgentS78.Construction.BoxAssembly
import AndersonAC.AgentS78.Construction.TileTrialFirst
import AndersonAC.AgentS78.Construction.TileTrialHalt
import AndersonAC.AgentS78.Construction.TileTrialRetry

/-!
# Run invariant split by block kind

`BoxInvariantK` assumes the invariant along the schedule off `exceptionalSet`, jointly
with the true installed values `TrueValues`, plus the final good and all-terminal
records. The two trial estimates require good entering records: tile records satisfy
`TileGood`, and clearing records satisfy the clearing first-failure bound through the
S6 bridge. `boxInvariant_of_K` derives the full
`BoxInvariant`: first-failure bounds per kind (query-free blocks never fail), and the halting
bounds (tile: the given ε; clearing: deterministic halting by `clearingHaltBound`; query-free:
immediate), and the pathwise final record off `exceptionalSet` by the joint induction with
`TrueValues` (`blockPrestate_mem_joint`, `installed_eq_true`).
-/

open MeasureTheory Filter Topology

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (Query RandomSources sourcesLaw)

variable {d m : ℕ}

theorem slotScaleOf_opIndex (j k : ℕ) (y : Torus d m) (hk : k < 4) :
    slotScaleOf d m (opIndex d m j k y) = j :=
  (decode_opIndex j k y hk).1

/-- **The run invariant package of one box, split by block kind.** -/
structure BoxInvariantK (d m n₀ : ℕ) (u E Cr cp cg c C : ℝ) (P : TilePlan d m) where
  ts₀ : TileScratch d m
  cl₀ : ClearScratch d m
  rec₀ : RunRecord d m
  hpend₀ : rec₀.pending = ∅
  hrec₀ : rec₀.aborted = false
  Inv : ℕ → Set (RunRecord d m)
  hInv0 : rec₀ ∈ Inv 0
  /-- The initial record carries the true installed values (nothing installed). -/
  hTV0 : ∀ ω : RandomSources (Torus d m) (tileOrderSize P), rec₀ ∈ TrueValues n₀ u ω
  /-- **Route R2**: the invariant is kept only off the null `exceptionalSet` (02-state.tex:222–229),
  on records carrying the true installed values of `ω`. -/
  hInv : ∀ n x k (ω : RandomSources (Torus d m) (tileOrderSize P)),
    ω ∉ exceptionalSet (d := d) (m := m) n₀ u E (tileOrderSize P) → x ∈ TrueValues n₀ u ω →
    x ∈ Inv n →
    (∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).halted
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k' ω) = false) →
    (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).halted
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k ω) = true →
    (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).exit
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k ω) ∈ Inv (n + 1)
  /-- The true installed values are kept by every block (same hypotheses as `hInv`). -/
  hTV : ∀ n x k (ω : RandomSources (Torus d m) (tileOrderSize P)),
    ω ∉ exceptionalSet (d := d) (m := m) n₀ u E (tileOrderSize P) → x ∈ TrueValues n₀ u ω →
    x ∈ Inv n →
    (∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).halted
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k' ω) = false) →
    (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).halted
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k ω) = true →
    (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n).exit
      (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u)) n) x k ω) ∈
        TrueValues n₀ u ω
  /-- **The final record** (record level): an invariant, non-aborted record entering stage `m + 2`
  whose installed values are `λ V(ω)` gives the certificate data at `ω ∉ exceptionalSet`. -/
  hfinal : ∀ x ∈ Inv (stageStartIdx d m (m + 2)), x.aborted = false →
    ∀ ω : RandomSources (Torus d m) (tileOrderSize P),
    ω ∉ exceptionalSet (d := d) (m := m) n₀ u E (tileOrderSize P) →
    (∀ i, x.installed i = OAI.Anderson.scaleCoupling n₀ u * (trueConfig ω i : ℝ)) →
    ∃ (s : Endpoint (Torus d m)) (r : Torus d m → ℂ), IsDampedEndpoint s r (OAI.Anderson.scaleHeight m P.u) ∧ TrueSchurIdentity P.n₀ P.u E (trueConfig ω) s ∧ Fintype.card (Torus d m) ≤ 2 * s.active.card ∧ (∀ i ∈ s.active, ‖r i‖ ≤ Cr ∧ cp ≤ (r i).im) ∧ (∀ i ∈ s.active, ‖s.g i i - r i‖ ≤ cp - cg)
  /-- Every site is terminal at the non-aborted record entering stage `m + 2` (pathwise). -/
  hAT : ∀ ω : RandomSources (Torus d m) (tileOrderSize P),
    blockStart (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u))) rec₀
      (stageStartIdx d m (m + 2)) ω ≠ ⊤ →
    (blockPrestate (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u))) rec₀
      (stageStartIdx d m (m + 2)) ω).aborted = false →
    ∀ i, i ∈ (blockPrestate (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ (clrOf n₀ u))) rec₀
      (stageStartIdx d m (m + 2)) ω).terminal
  /-- Records entering the tile block of `(j, T)` are `TileGood` (tile trial's hypothesis). -/
  hgoodT : ∀ j (y : Torus d m) (T : Fin (P.cover j).cover.count), P.n₀ < j → j ≤ m + 1 →
    tileAt P j y = some T → ∀ x ∈ Inv (opIndex d m j 0 y), x ∈ TileGood C P j T
  /-- The clearing first-failure bound on records entering a clearing block (clearing trial bound). -/
  hboundC : ∀ j (y : Torus d m), P.n₀ < j → j ≤ m / 2 → ∀ x ∈ Inv (opIndex d m j 2 y),
    sourcesLaw (Torus d m) (tileOrderSize P)
      (localFirstFail (tileOrderSize P) (clearingBlock (d := d) (m := m) n₀ j u y) x) ≤
        ENNReal.ofReal (birthBound c j)

/-- The halting event of a tile operation is that of its tile block. -/
theorem runOp_tile_notHalted {ClSc : Type} (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClSc)
    (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc))
    (j : ℕ) (y : Torus d m) (T : Fin (P.cover j).cover.count) (h1 : P.n₀ < j) (h2 : j ≤ m + 1)
    (hT : tileAt P j y = some T) (x : RunRecord d m) (k : ℕ) :
    notHalted (tileOrderSize P) (runOp P ts₀ cl₀ clr j 0 y) x k =
      notHalted (tileOrderSize P) (tileBlock P j T) x k := by
  unfold runOp
  rw [if_pos ⟨h1, h2⟩, if_pos rfl]
  simp only [hT]
  exact notHalted_embed (tileOrderSize P) (tileBlock P j T) (tileEmbed cl₀) tileProj
    (fun _ => rfl) x k

/-- The halting rate of block `n`: the tile rate on tile blocks, otherwise `1` before the
deterministic clearing bound and `0` after. -/
def boxEps (P : TilePlan d m) (u : ℝ)
    (εT : ∀ j, (Fin (P.cover j).cover.count) → ℕ → ℝ) (n k : ℕ) : ℝ := by
  classical
  exact if h : ∃ T : Fin (P.cover (decodeJ d m n)).cover.count, P.n₀ < decodeJ d m n ∧
      decodeJ d m n ≤ m + 1 ∧ decodeK d m n = 0 ∧ tileAt P (decodeJ d m n) (decodeY d m n) = some T
    then εT (decodeJ d m n) h.choose k
    else if k < clearingHaltBound d m u then 1 else 0

/-- **`BoxInvariant` from the kind-split package** and the tile trial tile bounds. -/
theorem boxInvariant_of_K {n₀ : ℕ} {u E Cr cp cg c C : ℝ} (P : TilePlan d m)
    (hn₀ : P.n₀ = n₀) (hu : P.u = u)
    (hTB : ∀ j, P.n₀ < j → j ≤ m + 1 → ∀ (T : Fin (P.cover j).cover.count),
      ∀ x ∈ TileGood C P j T, sourcesLaw (Torus d m) (tileOrderSize P)
        (localFirstFail (tileOrderSize P) (tileBlock P j T) x) ≤ ENNReal.ofReal (birthBound c j))
    (εT : ∀ j, (Fin (P.cover j).cover.count) → ℕ → ℝ)
    (hεT0 : ∀ j T k, 0 ≤ εT j T k) (hεT : ∀ j T, Tendsto (εT j T) atTop (𝓝 0))
    (hTH : ∀ j, P.n₀ < j → j ≤ m + 1 → ∀ (T : Fin (P.cover j).cover.count),
      ∀ x ∈ TileGood C P j T, ∀ k, sourcesLaw (Torus d m) (tileOrderSize P)
        (notHalted (tileOrderSize P) (tileBlock P j T) x k) ≤ ENNReal.ofReal (εT j T k))
    (B : BoxInvariantK d m n₀ u E Cr cp cg c C P) :
    Nonempty (BoxInvariant d m n₀ u E Cr cp cg c P) := by
  subst hn₀ hu
  -- first-failure bounds
  have hbound : ∀ n, ∀ x ∈ B.Inv n, sourcesLaw (Torus d m) (tileOrderSize P)
      (localFirstFail (tileOrderSize P)
        (scheduleBlocks (runOp P B.ts₀ B.cl₀ (clrOf P.n₀ P.u)) n) x) ≤
        ENNReal.ofReal (birthBound c (slotScaleOf d m n)) := by
    intro n x hx
    rw [← opIndex_decode (d := d) (m := m) n] at hx ⊢
    have hk := decodeK_lt (d := d) (m := m) n
    generalize decodeJ d m n = j at hx ⊢
    generalize decodeK d m n = k at hk hx ⊢
    generalize decodeY d m n = y at hx ⊢
    rw [scheduleBlocks_opIndex _ j k y hk, slotScaleOf_opIndex j k y hk]
    have hsimple : ∀ (f : RunRecord d m → RunRecord d m), sourcesLaw (Torus d m) (tileOrderSize P)
        (localFirstFail (tileOrderSize P) (simpleBlock (B.ts₀, B.cl₀) f) x) ≤
          ENNReal.ofReal (birthBound c j) := by
      intro f; rw [simpleBlock_localFirstFail]; simp
    unfold runOp
    by_cases h1 : P.n₀ < j ∧ j ≤ m + 1
    · rw [if_pos h1]
      by_cases hk0 : k = 0
      · subst hk0
        rw [if_pos rfl]
        cases hT : tileAt P j y with
        | none => exact hsimple id
        | some T =>
          rw [localFirstFail_embed (tileOrderSize P) (tileBlock P j T) (tileEmbed B.cl₀) tileProj
            (fun _ => rfl)]
          exact hTB j h1.1 h1.2 T x (B.hgoodT j y T h1.1 h1.2 hT x hx)
      rw [if_neg hk0]
      by_cases hk1 : k = 1
      · rw [if_pos hk1]; split_ifs <;> exact hsimple _
      rw [if_neg hk1]
      by_cases hk2 : k = 2
      · subst hk2
        rw [if_pos rfl]
        split_ifs with hjm
        · rw [localFirstFail_embed (tileOrderSize P) (clrOf (d := d) (m := m) P.n₀ P.u j y)
            (clearEmbed B.ts₀) clearProj (fun _ => rfl)]
          exact B.hboundC j y h1.1 hjm x hx
        · exact hsimple _
      rw [if_neg hk2]
      split_ifs <;> exact hsimple _
    · rw [if_neg h1]; exact hsimple _
  -- halting bounds
  have hhalt : ∀ n k, ∀ x ∈ B.Inv n, sourcesLaw (Torus d m) (tileOrderSize P)
      (notHalted (tileOrderSize P) (scheduleBlocks (runOp P B.ts₀ B.cl₀ (clrOf P.n₀ P.u)) n) x k) ≤
        ENNReal.ofReal (boxEps P P.u εT n k) := by
    intro n k x hx
    classical
    have hblock : scheduleBlocks (runOp P B.ts₀ B.cl₀ (clrOf P.n₀ P.u)) n =
        runOp P B.ts₀ B.cl₀ (clrOf P.n₀ P.u) (decodeJ d m n) (decodeK d m n) (decodeY d m n) := rfl
    unfold boxEps
    by_cases h : ∃ T : Fin (P.cover (decodeJ d m n)).cover.count, P.n₀ < decodeJ d m n ∧
        decodeJ d m n ≤ m + 1 ∧ decodeK d m n = 0 ∧
        tileAt P (decodeJ d m n) (decodeY d m n) = some T
    · rw [dif_pos h]
      obtain ⟨h1, h2, hk0, hT⟩ := h.choose_spec
      have hn : opIndex d m (decodeJ d m n) 0 (decodeY d m n) = n := by
        rw [← hk0]; exact opIndex_decode n
      have heq : scheduleBlocks (runOp P B.ts₀ B.cl₀ (clrOf P.n₀ P.u)) n =
          runOp P B.ts₀ B.cl₀ (clrOf P.n₀ P.u) (decodeJ d m n) 0 (decodeY d m n) := by
        rw [hblock, hk0]
      rw [heq, runOp_tile_notHalted P B.ts₀ B.cl₀ (clrOf P.n₀ P.u) _ _ _ h1 h2 hT]
      have hx' : x ∈ B.Inv (opIndex d m (decodeJ d m n) 0 (decodeY d m n)) := by
        rw [hn]; exact hx
      exact hTH _ h1 h2 _ x (B.hgoodT _ _ _ h1 h2 hT x hx') k
    · rw [dif_neg h]
      split_ifs with hk
      · rw [ENNReal.ofReal_one]; exact prob_le_one
      · have hempty : notHalted (tileOrderSize P)
            (scheduleBlocks (runOp P B.ts₀ B.cl₀ (clrOf P.n₀ P.u)) n) x k = ∅ := by
          rw [hblock]
          unfold runOp
          split_ifs with h1 h2 h3 h4 h5 h6 <;>
            first
            | exact notHalted_simple _ _ _ x k
            | (rw [notHalted_embed (tileOrderSize P) (clrOf (d := d) (m := m) P.n₀ P.u _ _)
                (clearEmbed B.ts₀) clearProj (fun _ => rfl)]
               ext ω
               simp only [Set.mem_empty_iff_false, iff_false]
               exact clr_halts P.n₀ _ P.u _ _ x k ω (by omega))
            | skip
          all_goals
            cases hT : tileAt P (decodeJ d m n) (decodeY d m n) with
            | none => exact notHalted_simple _ _ _ x k
            | some T => exact absurd ⟨T, h1.1, h1.2, h2, hT⟩ h
        rw [hempty]; simp
  -- the final record, along the actual run off the exceptional set (joint induction)
  have hfinal : ∀ ω : RandomSources (Torus d m) (tileOrderSize P),
      ω ∉ exceptionalSet (d := d) (m := m) P.n₀ P.u E (tileOrderSize P) →
      blockStart (tileOrderSize P) (scheduleBlocks (runOp P B.ts₀ B.cl₀ (clrOf P.n₀ P.u))) B.rec₀
        (stageStartIdx d m (m + 2)) ω ≠ ⊤ →
      (blockPrestate (tileOrderSize P) (scheduleBlocks (runOp P B.ts₀ B.cl₀ (clrOf P.n₀ P.u)))
        B.rec₀ (stageStartIdx d m (m + 2)) ω).aborted = false →
      ∃ (s : Endpoint (Torus d m)) (r : Torus d m → ℂ),
        IsDampedEndpoint s r (OAI.Anderson.scaleHeight m P.u) ∧
        TrueSchurIdentity P.n₀ P.u E (trueConfig ω) s ∧
        Fintype.card (Torus d m) ≤ 2 * s.active.card ∧
        (∀ i ∈ s.active, ‖r i‖ ≤ Cr ∧ cp ≤ (r i).im) ∧
        (∀ i ∈ s.active, ‖s.g i i - r i‖ ≤ cp - cg) := by
    intro ω hexc hst hab
    have hj := blockPrestate_mem_joint (tileOrderSize P)
      (scheduleBlocks (runOp P B.ts₀ B.cl₀ (clrOf P.n₀ P.u))) B.rec₀
      (scheduleSets (runOrderSet P)) (scheduleSets (runAuxSet P)) (runOrderSet_disjoint P)
      (runOps_orders P B.ts₀ B.cl₀ (clrOf P.n₀ P.u)
        (fun j y M S => clearingBlock_orders P.n₀ j P.u y M S))
      (runOps_aux P B.ts₀ B.cl₀ (clrOf P.n₀ P.u) (tileOrderSize P)
        (fun j y S => clearingBlock_aux P.n₀ j P.u y _ S)) ω B.Inv (TrueValues P.n₀ P.u ω)
      (fun n x k hx hi hk hh => B.hInv n x k ω hexc hx hi hk hh)
      (fun n x k hx hi hk hh => B.hTV n x k ω hexc hx hi hk hh) B.hInv0 (B.hTV0 ω) _ hst
    exact B.hfinal _ hj.1 hab ω hexc
      (installed_eq_true P.n₀ P.u ω _ hj.2 hab (B.hAT ω hst hab))
  refine ⟨{
    ts₀ := B.ts₀
    cl₀ := B.cl₀
    rec₀ := B.rec₀
    hpend₀ := B.hpend₀
    hrec₀ := B.hrec₀
    Inv := B.Inv
    hInv0 := B.hInv0
    hInv := B.hInv
    hTV0 := B.hTV0
    hTV := B.hTV
    hbound := hbound
    hfinal := hfinal
    ε := boxEps P P.u εT
    hε0 := ?_
    hε := ?_
    hhalt := hhalt }⟩
  · intro n k
    unfold boxEps
    split_ifs
    · exact hεT0 _ _ k
    · norm_num
    · norm_num
  · intro n
    unfold boxEps
    by_cases h : ∃ T : Fin (P.cover (decodeJ d m n)).cover.count, P.n₀ < decodeJ d m n ∧
        decodeJ d m n ≤ m + 1 ∧ decodeK d m n = 0 ∧
        tileAt P (decodeJ d m n) (decodeY d m n) = some T
    · simp only [dif_pos h]; exact hεT _ _
    · simp only [dif_neg h]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (clearingHaltBound d m P.u)] with k hk
      rw [if_neg (by omega)]

theorem birthBound_anti {c c' : ℝ} (h : c ≤ c') (j : ℕ) : birthBound c' j ≤ birthBound c j := by
  unfold birthBound
  apply Real.exp_le_exp.mpr
  have : (4 : ℝ) ^ (c * (j : ℝ)) ≤ (4 : ℝ) ^ (c' * (j : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg j))
  linarith

/-- Lowering the clearing exponent of a kind-split package. -/
def BoxInvariantK.mono {n₀ : ℕ} {u E Cr cp cg c c' C : ℝ} {P : TilePlan d m} (hcc : c ≤ c')
    (B : BoxInvariantK d m n₀ u E Cr cp cg c' C P) : BoxInvariantK d m n₀ u E Cr cp cg c C P where
  ts₀ := B.ts₀
  cl₀ := B.cl₀
  rec₀ := B.rec₀
  hpend₀ := B.hpend₀
  hrec₀ := B.hrec₀
  Inv := B.Inv
  hInv0 := B.hInv0
  hTV0 := B.hTV0
  hInv := B.hInv
  hTV := B.hTV
  hfinal := B.hfinal
  hAT := B.hAT
  hgoodT := B.hgoodT
  hboundC := fun j y h1 h2 x hx =>
    (B.hboundC j y h1 h2 x hx).trans (ENNReal.ofReal_le_ofReal (birthBound_anti hcc j))

/-- Assembles `S78.UniformCertificateInput d e₂` from the tile disciplines,
clearing-block measurability, a `TileTrialBoundStatement`, and uniform kind-split
run-invariant packages for each large box and tile plan with the cover facts. The
tile-trial bound follows from the tile slot law, monitor bounds, and sweep transfer. -/
theorem uniformCertificateInput_of_boxInvariantsK (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (htmark : TileMarkingStatement) (htquery : TileQueryStatement)
    (htpat : TilePatternStatement) (htabort : TileAbortStatement)
    (hthalt : TileHaltPatternStatement)
    (hcmeas : ∀ (m n₀ j : ℕ) (u : ℝ) (y : Torus d m),
      (clearingBlock (d := d) (m := m) n₀ j u y).IsMeasurable)
    (hfailG : ∀ m, ClearingFailGuarded d m) (hrad : ∀ m, ClearingCoreRadius d m)
    (helig : ∀ m, ClearingEligibleIntro d m)
    (hTTB : ∀ C : ℝ, 1 ≤ C → TileTrialBoundStatement d C)
    (hbox : ∀ C : ℝ, 1 ≤ C → ∃ Cg : ℝ, 1 ≤ Cg ∧ ∃ Cr cp cg c : ℝ, 0 < cp ∧ 0 < cg ∧ 0 < c ∧
      ∃ N₀ : ℕ, ∀ n₀ m : ℕ, N₀ ≤ n₀ → 4 * n₀ ≤ m → ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      ∀ E : ℝ, E ∈ OAI.Anderson.energyWindow d e₂ → ∀ P : TilePlan d m, P.n₀ = n₀ → P.u = u →
      (∀ j, StageCoverFacts C ((4 : ℝ) ^ 6 * C) P.u P.n₀ j (P.cover j)) →
      Nonempty (BoxInvariantK d m n₀ u E Cr cp cg c Cg P)) :
    UniformCertificateInput d e₂ := by
  refine uniformCertificateInput_of_boxInvariants d hd e₂ htmark htquery htpat htabort hthalt
    hcmeas hfailG hrad helig (fun C hC => ?_)
  obtain ⟨Cg, hCg, Cr, cp, cg, cC, hcp, hcg, hcC, N₀, hN⟩ := hbox C hC
  obtain ⟨cT, hcT, NT, hNT⟩ := tile_first_trial_bound d Cg (hTTB Cg hCg)
  obtain ⟨NH, hNH⟩ := tile_halting_bound d Cg (tileRetry_of_trialBound d Cg (hTTB Cg hCg))
  refine ⟨Cr, cp, cg, min cT cC, hcp, hcg, lt_min hcT hcC, max N₀ (max NT NH), ?_⟩
  intro n₀ m h1 h2 u hu E hE P hPn hPu hfacts
  obtain ⟨B⟩ := hN n₀ m (le_of_max_le_left h1) h2 u hu E hE P hPn hPu hfacts
  have hNT' : NT ≤ n₀ := le_trans (le_max_left _ _) (le_of_max_le_right h1)
  have hNH' : NH ≤ n₀ := le_trans (le_max_right _ _) (le_of_max_le_right h1)
  have hsizes : ∀ j (T : Fin (P.cover j).cover.count), TileOrderSizes P j T (tileOrderSize P) :=
    fun j T a => tileOrderSize_index P j T a
  have hεex : ∀ j (T : Fin (P.cover j).cover.count), ∃ ε : ℕ → ℝ, (∀ k, 0 ≤ ε k) ∧
      Tendsto ε atTop (𝓝 0) ∧ (P.n₀ < j → j ≤ m + 1 → ∀ x ∈ TileGood Cg P j T, ∀ k,
        sourcesLaw (Torus d m) (tileOrderSize P)
          (notHalted (tileOrderSize P) (tileBlock P j T) x k) ≤ ENNReal.ofReal (ε k)) := by
    intro j T
    by_cases hj : P.n₀ < j ∧ j ≤ m + 1
    · obtain ⟨ε, h0, hlim, hb⟩ := hNH n₀ hNH' m u hu P hPn hPu j (hPn ▸ hj.1) hj.2 T
        (tileOrderSize P) (hsizes j T)
      exact ⟨ε, h0, hlim, fun _ _ => hb⟩
    · exact ⟨fun _ => 0, fun _ => le_rfl, tendsto_const_nhds,
        fun h1 h2 => absurd ⟨h1, h2⟩ hj⟩
  choose εT hεT0 hεT hεTb using hεex
  exact boxInvariant_of_K P hPn hPu
    (fun j h1 h2 T x hx => (hNT n₀ hNT' m u hu P hPn hPu j (hPn ▸ h1) h2 T (tileOrderSize P)
      (hsizes j T) x hx).trans (ENNReal.ofReal_le_ofReal (birthBound_anti (min_le_left _ _) j)))
    εT hεT0 hεT (fun j h1 h2 T x hx k => hεTb j T h1 h2 x hx k)
    (B.mono (min_le_right _ _))

end AndersonAC.AgentS78
