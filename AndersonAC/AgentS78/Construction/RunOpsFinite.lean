import AndersonAC.AgentS78.Construction.RunOpsFresh
import AndersonAC.AgentS78.Construction.ReachedInv
import AndersonAC.AgentS78.Construction.ReachedEv

/-!
# every block of the schedule is reached almost surely

The `hfinite` input of `blockRun_of_runOps` from `all_blocks_reached_of_inv`, with the halting
patterns of the schedule (`scheduleHaltPattern`: `tileHaltPattern` for tile blocks, a
clearing halting pattern for clearing blocks, empty otherwise). Proved here: the embedding
and query-free cases (`notHalted_embed`, `notHalted_simple`), the pattern disciplines of the
tile halting pattern (`tileHaltPattern_disc`), and their freshness at block starts
(`fresh_of_declared_aux`).
-/

open MeasureTheory Filter Topology

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (Query RandomSources sourcesLaw querySigns)

variable {d m : ℕ} {ClSc : Type} [MeasurableSpace ClSc]

theorem notHalted_embed {ι Rec St St' : Type} [Fintype ι] [DecidableEq ι] (M : ℕ → ℕ)
    (B : Block ι Rec St) (e : St → St') (p : St' → St) (hpe : ∀ s, p (e s) = s) (x : Rec)
    (k : ℕ) : notHalted M (B.embed e p) x k = notHalted M B x k := by
  ext ω
  simp only [notHalted, Set.mem_setOf_eq, localState_embed M B e p hpe]
  simp only [Block.embed, hpe]

theorem notHalted_simple {Sc : Type} (M : ℕ → ℕ) (sc₀ : Sc) (f : RunRecord d m → RunRecord d m)
    (x : RunRecord d m) (k : ℕ) : notHalted M (simpleBlock sc₀ f) x k = ∅ := by
  ext ω
  simp only [notHalted, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall]
  exact ⟨0, Nat.zero_le k, by simp [localState, machineState, machineRun, simpleBlock]⟩

/-- The pattern discipline of the tile halting pattern. -/
theorem tileHaltPattern_disc (P : TilePlan d m) (j : ℕ) (T : Fin (P.cover j).cover.count)
    (k : ℕ) (x : RunRecord d m) :
    (∀ z ∈ (tileHaltPattern P j T k x).signs,
      z ∈ declaredFresh x ∨ ∃ a ∈ tileAuxSet d m j T, z = Sum.inr a) ∧
    ∀ o ∈ (tileHaltPattern P j T k x).orders, o ∈ tileOrderSet j T := by
  classical
  unfold tileHaltPattern
  by_cases hab : x.aborted = true
  · simp only [hab]
    refine ⟨fun z hz => ?_, fun o ho => ?_⟩
    · simp [FreshPattern.signs] at hz
    · simp at ho
  · have hab' : x.aborted = false := by simpa using hab
    simp only [hab', Bool.false_eq_true, ↓reduceIte]
    refine ⟨fun z hz => ?_, fun o ho => ?_⟩
    · simp only [FreshPattern.signs, Set.mem_union, Set.mem_setOf_eq] at hz
      rcases hz with ⟨i, hi, k', hk, rfl⟩ | ⟨a, ha, rfl⟩
      · left
        simp only [Finset.mem_sdiff, Finset.mem_inter] at hi
        exact ⟨hab', i, k', rfl, hi.1.2, hi.2, hk⟩
      · right
        simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range] at ha
        obtain ⟨⟨a', i⟩, _, rfl⟩ := ha
        exact ⟨_, ⟨a', i, rfl⟩, rfl⟩
    · simp only [Finset.mem_image, Finset.mem_range] at ho
      obtain ⟨a, _, rfl⟩ := ho
      exact ⟨a, rfl⟩

/-- The halting pattern of operation `(j, k, y)` for the first `k' + 1` states. -/
def runHaltPattern (P : TilePlan d m)
    (clrHalt : ℕ → Torus d m → ℕ → RunRecord d m → FreshPattern (Torus d m)) (j k : ℕ)
    (y : Torus d m) : ℕ → RunRecord d m → FreshPattern (Torus d m) :=
  if P.n₀ < j ∧ j ≤ m + 1 then
    if k = 0 then
      match tileAt P j y with
      | some T => tileHaltPattern P j T
      | none => fun _ _ => emptyPattern d m
    else if k = 2 ∧ j ≤ m / 2 then clrHalt j y
    else fun _ _ => emptyPattern d m
  else fun _ _ => emptyPattern d m

/-- The schedule's halting pattern of block `n`. -/
def scheduleHaltPattern (P : TilePlan d m)
    (clrHalt : ℕ → Torus d m → ℕ → RunRecord d m → FreshPattern (Torus d m)) (n : ℕ) :
    ℕ → RunRecord d m → FreshPattern (Torus d m) :=
  runHaltPattern P clrHalt (decodeJ d m n) (decodeK d m n) (decodeY d m n)

/-- The three shapes of a block of the schedule. -/
theorem block_shape (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClSc)
    (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc))
    (clrHalt : ℕ → Torus d m → ℕ → RunRecord d m → FreshPattern (Torus d m)) (n : ℕ) :
    (∃ (j : ℕ) (T : Fin (P.cover j).cover.count),
      scheduleBlocks (runOp P ts₀ cl₀ clr) n = (tileBlock P j T).embed (tileEmbed cl₀) tileProj ∧
      scheduleSets (d := d) (m := m) (runOrderSet P) n = tileOrderSet j T ∧
      scheduleSets (d := d) (m := m) (runAuxSet P) n = tileAuxSet d m j T ∧
      scheduleHaltPattern P clrHalt n = tileHaltPattern P j T) ∨
    (∃ j y, scheduleBlocks (runOp P ts₀ cl₀ clr) n = (clr j y).embed (clearEmbed ts₀) clearProj ∧
      scheduleSets (d := d) (m := m) (runOrderSet P) n = ∅ ∧
      scheduleSets (d := d) (m := m) (runAuxSet P) n = ∅ ∧
      scheduleHaltPattern P clrHalt n = clrHalt j y) ∨
    (∃ f, scheduleBlocks (runOp P ts₀ cl₀ clr) n = simpleBlock (ts₀, cl₀) f ∧
      scheduleSets (d := d) (m := m) (runOrderSet P) n = ∅ ∧
      scheduleSets (d := d) (m := m) (runAuxSet P) n = ∅ ∧
      scheduleHaltPattern P clrHalt n = fun _ _ => emptyPattern d m) := by
  unfold scheduleBlocks scheduleSets scheduleHaltPattern
  generalize decodeJ d m n = j
  generalize decodeK d m n = k
  generalize decodeY d m n = y
  unfold runOp runOrderSet runAuxSet runHaltPattern
  rcases hT : tileAt P j y with _ | T
  · split_ifs <;> first
      | exact Or.inr (Or.inl ⟨j, y, rfl, rfl, rfl, rfl⟩)
      | exact Or.inr (Or.inr ⟨_, rfl, rfl, rfl, rfl⟩)
      | (rw [if_neg (show ¬(k = 2 ∧ j ≤ m / 2) by omega)]
         exact Or.inr (Or.inr ⟨_, rfl, rfl, rfl, rfl⟩))
      | (exfalso; omega)
      | (exfalso; tauto)
  · split_ifs <;> first
      | exact Or.inl ⟨j, T, rfl, rfl, rfl, rfl⟩
      | exact Or.inr (Or.inl ⟨j, y, rfl, rfl, rfl, rfl⟩)
      | exact Or.inr (Or.inr ⟨_, rfl, rfl, rfl, rfl⟩)
      | (rw [if_neg (show ¬(k = 2 ∧ j ≤ m / 2) by omega)]
         exact Or.inr (Or.inr ⟨_, rfl, rfl, rfl, rfl⟩))
      | (exfalso; omega)
      | (exfalso; tauto)

/-- **Every block of the schedule is reached a.s.** (`hfinite` of `blockRun_of_runOps`). -/
theorem runOps_finite (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClSc)
    (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc))
    (clrHalt : ℕ → Torus d m → ℕ → RunRecord d m → FreshPattern (Torus d m))
    (rec₀ : RunRecord d m)
    (hcmeas : ∀ j y, (clr j y).IsMeasurable)
    (hcorders : ∀ j y (M : ℕ → ℕ) (S : Set ℕ), ∀ x k ω o,
      (clr j y).halted (localState M (clr j y) x k ω) = false →
      (clr j y).next (localState M (clr j y) x k ω) = Query.nextOrder o →
      o ∈ S ∧ ((List.range k).filter fun k' =>
        (clr j y).halted (localState M (clr j y) x k' ω) = false ∧
        (clr j y).next (localState M (clr j y) x k' ω) = Query.nextOrder o).length < M o)
    (hcaux : ∀ j y (M : ℕ → ℕ) (S : Set ℕ), ∀ x k ω a,
      (clr j y).halted (localState M (clr j y) x k ω) = false →
      (clr j y).next (localState M (clr j y) x k ω) = Query.auxiliary a →
      a ∈ S ∧ ∀ k' < k, (clr j y).halted (localState M (clr j y) x k' ω) = false →
        (clr j y).next (localState M (clr j y) x k' ω) ≠ Query.auxiliary a)
    (htquery : TileQueryStatement)
    (hcquery : ∀ j y x k (ω : RandomSources (Torus d m) (tileOrderSize P)),
      (∀ k' < k, (clr j y).halted (localState (tileOrderSize P) (clr j y) x k' ω) = false) →
      (clr j y).halted (localState (tileOrderSize P) (clr j y) x k ω) = true →
      declaredFresh ((clr j y).exit (localState (tileOrderSize P) (clr j y) x k ω)) ⊆
        declaredFresh x ∧
      ∀ k' < k, ∀ z ∈ declaredFresh ((clr j y).exit
          (localState (tileOrderSize P) (clr j y) x k ω)),
        z ∉ querySigns (Torus d m) ((clr j y).next
          (localState (tileOrderSize P) (clr j y) x k' ω)))
    (hthalt : TileHaltPatternStatement)
    (hchm : ∀ j y k, Measurable (clrHalt j y k))
    (hcNHm : ∀ j y k, MeasurableSet {p : RunRecord d m × RandomSources (Torus d m) (tileOrderSize P) |
      p.2 ∈ notHalted (tileOrderSize P) (clr j y) p.1 k})
    (hcNHloc : ∀ j y k x, DependsOnly (Torus d m) (M := tileOrderSize P) (clrHalt j y k x)
      (notHalted (tileOrderSize P) (clr j y) x k))
    (hchd : ∀ j y k x, (∀ z ∈ (clrHalt j y k x).signs, z ∈ declaredFresh x) ∧
      (clrHalt j y k x).orders = ∅)
    (Inv : ℕ → Set (RunRecord d m)) (h₀ : rec₀ ∈ Inv 0)
    (hInv : ∀ n x k (ω : RandomSources (Torus d m) (tileOrderSize P)), x ∈ Inv n →
      (∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ clr) n).halted
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k' ω) = false) →
      (scheduleBlocks (runOp P ts₀ cl₀ clr) n).halted
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k ω) = true →
      (scheduleBlocks (runOp P ts₀ cl₀ clr) n).exit
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k ω) ∈ Inv (n + 1))
    (ε : ℕ → ℕ → ℝ) (hε0 : ∀ n k, 0 ≤ ε n k) (hε : ∀ n, Tendsto (ε n) atTop (𝓝 0))
    (hbound : ∀ n k, ∀ x ∈ Inv n, sourcesLaw (Torus d m) (tileOrderSize P)
      (notHalted (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k) ≤
        ENNReal.ofReal (ε n k)) :
    ∀ n, ∀ᵐ ω ∂sourcesLaw (Torus d m) (tileOrderSize P),
      blockStart (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ n ω ≠ ⊤ := by
  have horders := runOps_orders P ts₀ cl₀ clr hcorders
  have haux := runOps_aux P ts₀ cl₀ clr (tileOrderSize P) (fun j y S => hcaux j y _ S)
  obtain ⟨hQ, hstart, -, hprest, -, -⟩ := blockComposition_proof machineRun_proof (Torus d m)
    (tileOrderSize P) (RunRecord d m) (RunRecord d m × (TileScratch d m × ClSc))
    (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (fun n => runOp_measurable P ts₀ cl₀ clr hcmeas _ _ _)
    (scheduleSets (runOrderSet P)) (runOrderSet_disjoint P) (scheduleSets (runAuxSet P))
    (runAuxSet_disjoint P) horders haux
  have hquery := runOps_query P ts₀ cl₀ clr (tileOrderSize P) htquery hcquery
  refine all_blocks_reached_of_inv (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
    (scheduleSets (runOrderSet P)) (scheduleSets (runAuxSet P)) (runOrderSet_disjoint P)
    horders haux hQ hstart hprest (scheduleHaltPattern P clrHalt) ?_ ?_ ?_ ?_ Inv h₀ hInv ε hε0 hε
    hbound
  · intro n k
    rcases block_shape P ts₀ cl₀ clr clrHalt n with ⟨j, T, -, -, -, hp⟩ | ⟨j, y, -, -, -, hp⟩ |
      ⟨f, -, -, -, hp⟩ <;> rw [hp]
    · exact (hthalt d m P j T (tileOrderSize P) k).1
    · exact hchm j y k
    · exact measurable_const
  · intro n k
    rcases block_shape P ts₀ cl₀ clr clrHalt n with ⟨j, T, hB, -, -, -⟩ | ⟨j, y, hB, -, -, -⟩ |
      ⟨f, hB, -, -, -⟩ <;> rw [hB]
    · simp only [notHalted_embed (tileOrderSize P) (tileBlock P j T) (tileEmbed cl₀) tileProj
        (fun _ => rfl)]
      exact (hthalt d m P j T (tileOrderSize P) k).2.1
    · simp only [notHalted_embed (tileOrderSize P) (clr j y) (clearEmbed ts₀) clearProj
        (fun _ => rfl)]
      exact hcNHm j y k
    · simp only [notHalted_simple, Set.mem_empty_iff_false, Set.ofPred_false]
      exact MeasurableSet.empty
  · intro n k x
    rcases block_shape P ts₀ cl₀ clr clrHalt n with ⟨j, T, hB, -, -, hp⟩ | ⟨j, y, hB, -, -, hp⟩ |
      ⟨f, hB, -, -, hp⟩ <;> rw [hB, hp]
    · rw [notHalted_embed (tileOrderSize P) (tileBlock P j T) (tileEmbed cl₀) tileProj
        (fun _ => rfl)]
      exact (hthalt d m P j T (tileOrderSize P) k).2.2 x
    · rw [notHalted_embed (tileOrderSize P) (clr j y) (clearEmbed ts₀) clearProj (fun _ => rfl)]
      exact hcNHloc j y k x
    · rw [notHalted_simple]
      intro ω ω' _ _
      simp
  · intro n k ω hn
    refine fresh_of_declared_aux (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
      (scheduleSets (runOrderSet P)) (scheduleSets (runAuxSet P)) (runOrderSet_disjoint P)
      (runAuxSet_disjoint P) horders haux declaredFresh hquery
      (fun n => scheduleHaltPattern P clrHalt n k) (fun n' x => ?_) n ω hn
    rcases block_shape P ts₀ cl₀ clr clrHalt n' with ⟨j, T, -, hO, hA, hp⟩ |
      ⟨j, y, -, hO, hA, hp⟩ | ⟨f, -, hO, hA, hp⟩ <;> simp only [hO, hA, hp]
    · exact tileHaltPattern_disc P j T k x
    · refine ⟨fun z hz => Or.inl ((hchd j y k x).1 z hz), fun o ho => ?_⟩
      rw [(hchd j y k x).2] at ho
      exact absurd ho (Finset.notMem_empty o)
    · refine ⟨fun z hz => ?_, fun o ho => ?_⟩
      · rw [emptyPattern_signs] at hz; exact absurd hz (Set.notMem_empty z)
      · simp [emptyPattern] at ho

/-- **Every block of the schedule is reached a.s.**, with clearing blocks that halt
deterministically by step `Kc` (no clearing halting pattern needed). -/
theorem runOps_finite_det (P : TilePlan d m) (ts₀ : TileScratch d m) (cl₀ : ClSc)
    (clr : ℕ → Torus d m → Block (Torus d m) (RunRecord d m) (RunRecord d m × ClSc))
    (rec₀ : RunRecord d m)
    (hcmeas : ∀ j y, (clr j y).IsMeasurable)
    (hcorders : ∀ j y (M : ℕ → ℕ) (S : Set ℕ), ∀ x k ω o,
      (clr j y).halted (localState M (clr j y) x k ω) = false →
      (clr j y).next (localState M (clr j y) x k ω) = Query.nextOrder o →
      o ∈ S ∧ ((List.range k).filter fun k' =>
        (clr j y).halted (localState M (clr j y) x k' ω) = false ∧
        (clr j y).next (localState M (clr j y) x k' ω) = Query.nextOrder o).length < M o)
    (hcaux : ∀ j y (M : ℕ → ℕ) (S : Set ℕ), ∀ x k ω a,
      (clr j y).halted (localState M (clr j y) x k ω) = false →
      (clr j y).next (localState M (clr j y) x k ω) = Query.auxiliary a →
      a ∈ S ∧ ∀ k' < k, (clr j y).halted (localState M (clr j y) x k' ω) = false →
        (clr j y).next (localState M (clr j y) x k' ω) ≠ Query.auxiliary a)
    (htquery : TileQueryStatement)
    (hcquery : ∀ j y x k (ω : RandomSources (Torus d m) (tileOrderSize P)),
      (∀ k' < k, (clr j y).halted (localState (tileOrderSize P) (clr j y) x k' ω) = false) →
      (clr j y).halted (localState (tileOrderSize P) (clr j y) x k ω) = true →
      declaredFresh ((clr j y).exit (localState (tileOrderSize P) (clr j y) x k ω)) ⊆
        declaredFresh x ∧
      ∀ k' < k, ∀ z ∈ declaredFresh ((clr j y).exit
          (localState (tileOrderSize P) (clr j y) x k ω)),
        z ∉ querySigns (Torus d m) ((clr j y).next
          (localState (tileOrderSize P) (clr j y) x k' ω)))
    (hthalt : TileHaltPatternStatement)
    (Kc : ℕ) (hchalt : ∀ j y x k (ω : RandomSources (Torus d m) (tileOrderSize P)), Kc ≤ k →
      ω ∉ notHalted (tileOrderSize P) (clr j y) x k)
    (Inv : ℕ → Set (RunRecord d m)) (h₀ : rec₀ ∈ Inv 0)
    (hInv : ∀ n x k (ω : RandomSources (Torus d m) (tileOrderSize P)), x ∈ Inv n →
      (∀ k' < k, (scheduleBlocks (runOp P ts₀ cl₀ clr) n).halted
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k' ω) = false) →
      (scheduleBlocks (runOp P ts₀ cl₀ clr) n).halted
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k ω) = true →
      (scheduleBlocks (runOp P ts₀ cl₀ clr) n).exit
        (localState (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k ω) ∈ Inv (n + 1))
    (ε : ℕ → ℕ → ℝ) (hε0 : ∀ n k, 0 ≤ ε n k) (hε : ∀ n, Tendsto (ε n) atTop (𝓝 0))
    (hbound : ∀ n k, ∀ x ∈ Inv n, sourcesLaw (Torus d m) (tileOrderSize P)
      (notHalted (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr) n) x k) ≤
        ENNReal.ofReal (ε n k)) :
    ∀ n, ∀ᵐ ω ∂sourcesLaw (Torus d m) (tileOrderSize P),
      blockStart (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ n ω ≠ ⊤ := by
  have horders := runOps_orders P ts₀ cl₀ clr hcorders
  have haux := runOps_aux P ts₀ cl₀ clr (tileOrderSize P) (fun j y S => hcaux j y _ S)
  obtain ⟨hQ, hstart, -, hprest, -, -⟩ := blockComposition_proof machineRun_proof (Torus d m)
    (tileOrderSize P) (RunRecord d m) (RunRecord d m × (TileScratch d m × ClSc))
    (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀ (fun n => runOp_measurable P ts₀ cl₀ clr hcmeas _ _ _)
    (scheduleSets (runOrderSet P)) (runOrderSet_disjoint P) (scheduleSets (runAuxSet P))
    (runAuxSet_disjoint P) horders haux
  set clrHalt : ℕ → Torus d m → ℕ → RunRecord d m → FreshPattern (Torus d m) :=
    fun _ _ _ _ => emptyPattern d m with hclrHalt
  have hquery := runOps_query P ts₀ cl₀ clr (tileOrderSize P) htquery hcquery
  have hnh : ∀ j y x k, Kc ≤ k → notHalted (tileOrderSize P) (clr j y) x k = ∅ := by
    intro j y x k hk
    ext ω
    simp only [Set.mem_empty_iff_false, iff_false]
    exact hchalt j y x k ω hk
  refine all_blocks_reached_of_inv_ev (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
    (scheduleSets (runOrderSet P)) (scheduleSets (runAuxSet P)) (runOrderSet_disjoint P)
    horders haux hQ hstart hprest (fun _ => Kc) (scheduleHaltPattern P clrHalt) ?_ ?_ ?_ ?_ Inv h₀ hInv
    ε hε0 hε (fun n k _ => hbound n k)
  · intro n k _
    rcases block_shape P ts₀ cl₀ clr clrHalt n with ⟨j, T, -, -, -, hp⟩ | ⟨j, y, -, -, -, hp⟩ |
      ⟨f, -, -, -, hp⟩ <;> rw [hp]
    · exact (hthalt d m P j T (tileOrderSize P) k).1
    · exact measurable_const
    · exact measurable_const
  · intro n k hk
    rcases block_shape P ts₀ cl₀ clr clrHalt n with ⟨j, T, hB, -, -, -⟩ | ⟨j, y, hB, -, -, -⟩ |
      ⟨f, hB, -, -, -⟩ <;> rw [hB]
    · simp only [notHalted_embed (tileOrderSize P) (tileBlock P j T) (tileEmbed cl₀) tileProj
        (fun _ => rfl)]
      exact (hthalt d m P j T (tileOrderSize P) k).2.1
    · simp only [notHalted_embed (tileOrderSize P) (clr j y) (clearEmbed ts₀) clearProj
        (fun _ => rfl)]
      simp only [hnh j y _ k hk, Set.mem_empty_iff_false, Set.ofPred_false]
      exact MeasurableSet.empty
    · simp only [notHalted_simple, Set.mem_empty_iff_false, Set.ofPred_false]
      exact MeasurableSet.empty
  · intro n k hk x
    rcases block_shape P ts₀ cl₀ clr clrHalt n with ⟨j, T, hB, -, -, hp⟩ | ⟨j, y, hB, -, -, hp⟩ |
      ⟨f, hB, -, -, hp⟩ <;> rw [hB, hp]
    · rw [notHalted_embed (tileOrderSize P) (tileBlock P j T) (tileEmbed cl₀) tileProj
        (fun _ => rfl)]
      exact (hthalt d m P j T (tileOrderSize P) k).2.2 x
    · rw [notHalted_embed (tileOrderSize P) (clr j y) (clearEmbed ts₀) clearProj (fun _ => rfl)]
      rw [hnh j y x k hk]
      intro ω ω' _ _
      simp
    · rw [notHalted_simple]
      intro ω ω' _ _
      simp
  · intro n k _ ω hn
    refine fresh_of_declared_aux (tileOrderSize P) (scheduleBlocks (runOp P ts₀ cl₀ clr)) rec₀
      (scheduleSets (runOrderSet P)) (scheduleSets (runAuxSet P)) (runOrderSet_disjoint P)
      (runAuxSet_disjoint P) horders haux declaredFresh hquery
      (fun n => scheduleHaltPattern P clrHalt n k) (fun n' x => ?_) n ω hn
    rcases block_shape P ts₀ cl₀ clr clrHalt n' with ⟨j, T, -, hO, hA, hp⟩ |
      ⟨j, y, -, hO, hA, hp⟩ | ⟨f, -, hO, hA, hp⟩ <;> simp only [hO, hA, hp]
    · exact tileHaltPattern_disc P j T k x
    · refine ⟨fun z hz => ?_, fun o ho => ?_⟩
      · change z ∈ (emptyPattern d m).signs at hz
        rw [emptyPattern_signs] at hz; exact absurd hz (Set.notMem_empty z)
      · change o ∈ (emptyPattern d m).orders at ho
        simp [emptyPattern] at ho
    · refine ⟨fun z hz => ?_, fun o ho => ?_⟩
      · rw [emptyPattern_signs] at hz; exact absurd hz (Set.notMem_empty z)
      · simp [emptyPattern] at ho

end AndersonAC.AgentS78
