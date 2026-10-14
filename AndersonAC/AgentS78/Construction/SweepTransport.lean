import AndersonAC.AgentS78.Construction.SweepEnd
import AndersonAC.AgentS78.Construction.SweepEndReserve
import AndersonAC.AgentS78.Construction.FinalSweep
import AndersonAC.AgentS78.PadNorm
import AndersonAC.S45.RestrictLive
import AndersonAC.S45.RestrictLiveEquiv
import AndersonAC.S45.SingleDeletionProof
import AndersonAC.S45.LocalTransferProof

/-!
# The sweep transport (`SweepTransportStatement`)

agent-s78stransp (2026-10-14). Proves `AndersonAC.AgentS78.sweepTransportFull_proof`
(`SweepTransportFullStatement`, agent-s78final's FinalSweep.lean: every sweep `j ≤ m + 1`) and
its digit form `AndersonAC.AgentS78.sweepTransport_proof`: at the end of a sweep the committed sweep, restricted to the start live set (the ports of the active
sites, luna-s78live's `Sequence.restrictLive`) and reindexed along `e : Fin n ≃ active`
(`Sequence.reindex`), satisfies `SweepS45Facts`.

The composite restriction + reindexing is the pull-back of the sweep along the injective port
map `ι (i, b) = ((e i).val, b)`. Every analytic record of the pulled-back sweep is the
corresponding record of the committed sweep read at the ports `ι a`: the `J` and `L` records
are submatrices along `ι` (the `L` Laplacian row sums lose only entries in dead columns), the
start `D` is `stageD0` along `ι`, and the live states are reindexed live states. Validity
transports with it (operator norm of a supported submatrix, quadratic forms of a submatrix are
forms of the zero extension). Symmetry and Ward hold at every step from the start
(argon-s78transfer / agent-s78a3bv3 `wellFormed_symm_ward`, copied here), the start being the
v3 stage start `startV3` reindexed (StartClauses `start_prestate`).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78stransp

open AndersonAC.S45 Matrix
open scoped Matrix.Norms.L2Operator

/-! ## Symmetry and Ward along a well-formed sequence (copied from agent-s78a3bv3 445dd60,
`TileCoreA3b.lean` Section 3) -/

section WellFormedProps
variable {P_port : Type*} [Fintype P_port] [DecidableEq P_port]

theorem state_ext {ι : Type*} {s1 s2 : S45.State ι} (hg : s1.g = s2.g) (hr : s1.r = s2.r) :
    s1 = s2 := by
  cases s1; cases s2; congr

/-- Equivalence between `b.live` and `S45.survivors ⟨x, hx⟩` when `b.live = a.live.erase x`. -/
def stepLiveEquiv {a b : S45.LiveState P_port} {x : P_port}
    (hx : x ∈ a.live) (hsurv : b.live = a.live.erase x) :
    b.live ≃ S45.survivors (⟨x, hx⟩ : a.live) where
  toFun i :=
    have hi : i.1 ∈ a.live.erase x := hsurv ▸ i.2
    ⟨⟨i.1, Finset.mem_of_mem_erase hi⟩,
      Finset.mem_erase.mpr ⟨fun h => (Finset.ne_of_mem_erase hi)
        (congrArg Subtype.val h), Finset.mem_univ _⟩⟩
  invFun j := ⟨j.1.1, by
    rw [hsurv]
    exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp j.2).1 (Subtype.ext h), j.1.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem stepRel_state_eq_reindex {t : ℝ} {r : P_port → ℂ} {a b : S45.LiveState P_port}
    {x : P_port} {ξ : ℝ} (hrel : S45.StepRel t r a b x ξ) :
    b.state r = AgentS45.State.reindex (stepLiveEquiv hrel.pivot_live hrel.survivors)
      (S45.deleteState t (a.state r) ⟨x, hrel.pivot_live⟩ ξ) := by
  apply state_ext
  · ext i j
    have hg := congrFun (congrFun hrel.update i.1) j.1
    change b.g i.1 j.1 = _
    rw [hg]
    simp [AgentS45.State.reindex, stepLiveEquiv, S45.deleteState, S45.LiveState.state,
      S45.restrict, S45.mask, S45.pad, Matrix.submatrix_apply, i.2, j.2]
    rfl
  · ext i
    rfl

lemma ward_polar_identity (gij a zi zj : ℂ) :
    (gij.im : ℂ) - a * zi * (zj.im : ℂ) - star a * star zj * (zi.im : ℂ) +
      ((-a.im : ℝ) : ℂ) * zi * star zj = ((gij - a * zi * zj).im : ℂ) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem deleteState_isSymm (t : ℝ) (s : S45.State P_port) (x : P_port) (ξ : ℝ)
    (hsym : s.g.IsSymm) : (S45.deleteState t s x ξ).g.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  change s.g j.1 i.1 - ((ξ : ℂ) + t * s.r x) * s.g j.1 x * s.g x i.1 /
      (1 + ((ξ : ℂ) + t * s.r x) * s.g x x) =
    s.g i.1 j.1 - ((ξ : ℂ) + t * s.r x) * s.g i.1 x * s.g x j.1 /
      (1 + ((ξ : ℂ) + t * s.r x) * s.g x x)
  rw [hsym.apply j.1 i.1, hsym.apply j.1 x, hsym.apply x i.1]
  ring

theorem deleteState_ward (t : ℝ) (s : S45.State P_port) (x : P_port) (ξ : ℝ) (ht : 0 < t)
    (hsym : s.g.IsSymm) (hw : s.ward t)
    (hden : 1 + ((ξ : ℂ) + t * s.r x) * s.g x x ≠ 0) :
    (S45.deleteState t s x ξ).ward t := by
  classical
  let s' := S45.deleteState t s x ξ
  let c : ℂ := (ξ : ℂ) + t * s.r x
  let d : ℂ := 1 + c * s.g x x
  let a : ℂ := c / d
  have hsqrt_pos : (Real.sqrt t : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 ht))
  have hdne : d ≠ 0 := hden
  have hcim : c.im = t * s.p x := by
    simp [c, S45.State.p, Complex.add_im, Complex.mul_im]
  have hscalar := AgentS45.scalar_ward_coeff t (s.p x) (s.q x) c d (s.g x x)
    hcim (by simp [S45.State.q]) rfl hdne
  have halphaNorm : Complex.normSq a = Complex.normSq c / Complex.normSq d := by
    simp [a]
  have hcoeffBase : Complex.normSq a * s.q x - t * s.p x / Complex.normSq d = -a.im := by
    rw [halphaNorm]; linarith [hscalar]
  have hfactor : 1 - a * s.g x x = d⁻¹ := by
    dsimp [a]; field_simp [hdne]; dsimp [d]; ring
  have hupdate : ∀ i j : S45.survivors x,
      s'.h t i j = s.h t i.1 j.1 - S45.gamma t s x ξ * s.h t i.1 x * s.h t x j.1 := by
    intro i j
    change (Real.sqrt t : ℂ) *
        (s.g i.1 j.1 - ((ξ : ℂ) + t * s.r x) * s.g i.1 x * s.g x j.1 /
          (1 + ((ξ : ℂ) + t * s.r x) * s.g x x)) =
      (Real.sqrt t : ℂ) * s.g i.1 j.1 -
        (((ξ : ℂ) + t * s.r x) /
          ((Real.sqrt t : ℂ) * (1 + ((ξ : ℂ) + t * s.r x) * s.g x x))) *
          ((Real.sqrt t : ℂ) * s.g i.1 x) * ((Real.sqrt t : ℂ) * s.g x j.1)
    field_simp [hden, hsqrt_pos]
  ext i j
  change ((s'.h t * Matrix.diagonal (fun k => (s'.p k : ℂ))) * (s'.h t)ᴴ) i j =
    S45.matrixIm s'.g i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, S45.matrixIm]
  let zi : ℂ := s.g i.1 x
  let zj : ℂ := s.g j.1 x
  let bi : ℂ := a * zi
  let bj : ℂ := a * zj
  let Hi : P_port → ℂ := fun k => s.h t i.1 k - bi * s.h t x k
  let Hj : P_port → ℂ := fun k => s.h t j.1 k - bj * s.h t x k
  have hsymxj : s.g x j.1 = zj := hsym.apply j.1 x
  have hcoeff_i : S45.gamma t s x ξ * s.h t i.1 x = bi := by
    dsimp [S45.gamma, a, bi, c, d, zi, S45.State.h]
    field_simp [hden, hsqrt_pos]
  have hcoeff_j : S45.gamma t s x ξ * s.h t j.1 x = bj := by
    dsimp [S45.gamma, a, bj, c, d, zj, S45.State.h]
    field_simp [hden, hsqrt_pos]
  have hHi (k : S45.survivors x) : s'.h t i k = Hi k.1 := by
    dsimp [Hi]; rw [hupdate i k, hcoeff_i]
  have hHj (k : S45.survivors x) : s'.h t j k = Hj k.1 := by
    dsimp [Hj]; rw [hupdate j k, hcoeff_j]
  have hHx (z : ℂ) : (Real.sqrt t : ℂ) * z - (a * z) * ((Real.sqrt t : ℂ) * s.g x x) =
      (Real.sqrt t : ℂ) * z / d := by
    calc (Real.sqrt t : ℂ) * z - (a * z) * ((Real.sqrt t : ℂ) * s.g x x)
        = (Real.sqrt t : ℂ) * z * (1 - a * s.g x x) := by ring
      _ = (Real.sqrt t : ℂ) * z * d⁻¹ := by rw [hfactor]
      _ = (Real.sqrt t : ℂ) * z / d := by simp [div_eq_mul_inv]
  have hHix : Hi x = (Real.sqrt t : ℂ) * zi / d := hHx zi
  have hHjx : Hj x = (Real.sqrt t : ℂ) * zj / d := hHx zj
  have hsplit : (∑ k : S45.survivors x, s'.h t i k * (s'.p k : ℂ) * star (s'.h t j k)) =
      (∑ k : P_port, Hi k * (s.p k : ℂ) * star (Hj k)) - Hi x * (s.p x : ℂ) * star (Hj x) := by
    rw [show (∑ k : S45.survivors x, s'.h t i k * (s'.p k : ℂ) * star (s'.h t j k)) =
      ∑ k : S45.survivors x, Hi k.1 * (s.p k.1 : ℂ) * star (Hj k.1) from
      Finset.sum_congr rfl fun k _ => by rw [hHi k, hHj k]; rfl]
    exact AgentS45.sum_survivors_sub x (fun k => Hi k * (s.p k : ℂ) * star (Hj k))
  have hfull : (∑ k : P_port, Hi k * (s.p k : ℂ) * star (Hj k)) =
      (s.g i.1 j.1).im - bi * (s.g x j.1).im - star bj * (s.g i.1 x).im +
        bi * star bj * (s.q x : ℂ) := by
    have hterm (k : P_port) : Hi k * (s.p k : ℂ) * star (Hj k) =
        s.h t i.1 k * (s.p k : ℂ) * star (s.h t j.1 k) -
          bi * (s.h t x k * (s.p k : ℂ) * star (s.h t j.1 k)) -
          star bj * (s.h t i.1 k * (s.p k : ℂ) * star (s.h t x k)) +
          bi * star bj * (s.h t x k * (s.p k : ℂ) * star (s.h t x k)) := by
      simp only [Hi, Hj, star_sub, star_mul]; ring
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      AgentS45.ward_entry_h t s hw i.1 j.1, AgentS45.ward_entry_h t s hw x j.1,
      AgentS45.ward_entry_h t s hw i.1 x, AgentS45.ward_entry_h t s hw x x]
    rfl
  have hdel : Hi x * (s.p x : ℂ) * star (Hj x) =
      ((t * s.p x / Complex.normSq d : ℝ) : ℂ) * zi * star zj := by
    rw [hHix, hHjx, star_div₀, star_mul, Complex.star_def, Complex.conj_ofReal]
    have hsqt : (Real.sqrt t : ℂ) * (Real.sqrt t : ℂ) = (t : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt ht.le
    have hdd : d * (starRingEnd ℂ) d = (Complex.normSq d : ℂ) := Complex.mul_conj d
    calc ((Real.sqrt t : ℂ) * zi / d) * (s.p x : ℂ) * ((starRingEnd ℂ) zj * (Real.sqrt t : ℂ) / (starRingEnd ℂ) d)
        = ((Real.sqrt t : ℂ) * (Real.sqrt t : ℂ)) * (s.p x : ℂ) / (d * (starRingEnd ℂ) d) * zi * (starRingEnd ℂ) zj := by ring
      _ = (t : ℂ) * (s.p x : ℂ) / (Complex.normSq d : ℂ) * zi * star zj := by
          rw [hsqt, hdd, Complex.star_def]
      _ = ((t * s.p x / Complex.normSq d : ℝ) : ℂ) * zi * star zj := by push_cast; ring
  have hbibj : bi * star bj * (s.q x : ℂ) =
      ((Complex.normSq a * s.q x : ℝ) : ℂ) * zi * star zj := by
    dsimp [bi, bj]
    have haa : a * star a = (Complex.normSq a : ℂ) := by
      simpa [Complex.star_def] using Complex.mul_conj a
    calc (a * zi) * star (a * zj) * (s.q x : ℂ)
        = (a * star a) * (s.q x : ℂ) * zi * star zj := by rw [star_mul]; ring
      _ = ((Complex.normSq a * s.q x : ℝ) : ℂ) * zi * star zj := by
          rw [haa]; push_cast; ring
  have hgij : s'.g i j = s.g i.1 j.1 - a * zi * zj := by
    dsimp [s', S45.deleteState, a, c, d, zi, zj]
    rw [hsymxj]
    field_simp [hdne]
    ring
  rw [hsplit, hfull, hbibj, hdel, hsymxj, hgij]
  have hcomb : (s.g i.1 j.1).im - bi * (zj.im : ℂ) - star bj * (zi.im : ℂ) +
      ((Complex.normSq a * s.q x : ℝ) : ℂ) * zi * star zj -
      ((t * s.p x / Complex.normSq d : ℝ) : ℂ) * zi * star zj =
      (s.g i.1 j.1).im - a * zi * (zj.im : ℂ) - star a * star zj * (zi.im : ℂ) +
      ((-a.im : ℝ) : ℂ) * zi * star zj := by
    have hbj : star bj = star zj * star a := star_mul a zj
    rw [hbj, ← hcoeffBase]
    dsimp [bi]
    push_cast
    ring
  rw [hcomb]
  exact ward_polar_identity (s.g i.1 j.1) a zi zj

theorem reindex_isSymm {ι κ : Type*} (e : κ ≃ ι) (s : S45.State ι) (hs : s.g.IsSymm) :
    (AgentS45.State.reindex e s).g.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact hs.apply (e i) (e j)

theorem reindex_ward {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (s : S45.State ι) (t : ℝ) (hw : s.ward t) :
    (AgentS45.State.reindex e s).ward t := by
  ext i j
  have h := congrFun (congrFun hw (e i)) (e j)
  change (((AgentS45.State.reindex e s).h t *
      Matrix.diagonal (fun k => ((AgentS45.State.reindex e s).p k : ℂ))) *
    ((AgentS45.State.reindex e s).h t)ᴴ) i j = _
  change ((s.h t * Matrix.diagonal (fun k => (s.p k : ℂ))) * (s.h t)ᴴ) (e i) (e j) = _ at h
  rw [Matrix.mul_apply] at h ⊢
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply,
    S45.matrixIm, AgentS45.State.reindex, S45.State.h, S45.State.p, Matrix.smul_apply] at h ⊢
  rw [← h]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem wellFormed_symm_ward {q : S45.Sequence P_port} {t : ℝ} {r : P_port → ℂ}
    (ht : 0 < t) (hq : q.wellFormed t r)
    (hsym0 : ((q.state 0).state r).g.IsSymm) (hward0 : ((q.state 0).state r).ward t) :
    ∀ s ≤ q.length, ((q.state s).state r).g.IsSymm ∧ ((q.state s).state r).ward t := by
  intro s
  induction s with
  | zero => intro _; exact ⟨hsym0, hward0⟩
  | succ s ih =>
    intro hs1
    have hs : s < q.length := hs1
    obtain ⟨hsym, hward⟩ := ih hs.le
    have hwf := hq.2 s hs
    cases hp : q.pivot s with
    | none =>
      rw [hp] at hwf
      rw [hwf]
      exact ⟨hsym, hward⟩
    | some x =>
      rw [hp] at hwf
      have hrel : S45.StepRel t r (q.state s) (q.state (s + 1)) x (q.scalar s) := hwf
      have hden : 1 + ((q.scalar s : ℂ) + t * ((q.state s).state r).r ⟨x, hrel.pivot_live⟩) *
          ((q.state s).state r).g ⟨x, hrel.pivot_live⟩ ⟨x, hrel.pivot_live⟩ ≠ 0 :=
        hrel.denominator
      rw [stepRel_state_eq_reindex hrel]
      exact ⟨reindex_isSymm _ _ (deleteState_isSymm t _ _ _ hsym),
        reindex_ward _ _ t (deleteState_ward t _ _ _ ht hsym hward hden)⟩

end WellFormedProps

/-! ## States read along an injective port map -/

section Comap
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- A state read at the ports `f b`. -/
def comap (f : β → α) (s : State α) : State β :=
  ⟨fun a b => s.g (f a) (f b), fun a => s.r (f a)⟩

theorem comap_D (f : β → α) (hf : Function.Injective f) (s : State α) (t : ℝ) (a b : β) :
    (comap f s).D t a b = s.D t (f a) (f b) := by
  simp only [State.D, Matrix.sub_apply, AndersonAC.S45.diagonal_sandwich_apply,
    Matrix.diagonal_apply, hf.eq_iff]
  rfl

theorem comap_Jinc (f : β → α) (hf : Function.Injective f) (s : State α) (t : ℝ) (x : β)
    (ξ : ℝ) (a b : β) :
    Jinc t (comap f s) x ξ a b = Jinc t s (f x) ξ (f a) (f b) := by
  have hm : ∀ c : β, c ∈ survivors x ↔ f c ∈ survivors (f x) := by
    intro c; simp [survivors, hf.eq_iff]
  unfold Jinc pad
  by_cases ha : a ∈ survivors x
  · by_cases hb : b ∈ survivors x
    · rw [dif_pos ha, dif_pos hb, dif_pos ((hm a).1 ha), dif_pos ((hm b).1 hb)]
      rfl
    · rw [dif_pos ha, dif_neg hb, dif_pos ((hm a).1 ha), dif_neg (fun h => hb ((hm b).2 h))]
  · rw [dif_neg ha, dif_neg (fun h => ha ((hm a).2 h))]

/-- The `L` increment along an injective map, when the state vanishes in the columns off the
range of the map. -/
theorem comap_Linc (f : β → α) (hf : Function.Injective f) (s : State α) (t : ℝ) (x : β)
    (ξ : ℝ) (hs : ∀ i p, (∀ c, f c ≠ p) → s.g i p = 0) (a b : β) :
    Linc t (comap f s) x ξ a b = Linc t s (f x) ξ (f a) (f b) := by
  have hm : ∀ c : β, c ∈ survivors x ↔ f c ∈ survivors (f x) := by
    intro c; simp [survivors, hf.eq_iff]
  unfold Linc pad
  by_cases ha : a ∈ survivors x
  · by_cases hb : b ∈ survivors x
    · rw [dif_pos ha, dif_pos hb, dif_pos ((hm a).1 ha), dif_pos ((hm b).1 hb)]
      unfold laplacian
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl, if_pos rfl]
        refine Fintype.sum_of_injective (fun c : survivors x => (⟨f c.1, (hm c.1).1 c.2⟩ :
          survivors (f x))) ?_ _ _ ?_ ?_
        · intro c c' h
          exact Subtype.ext (hf (congrArg Subtype.val h))
        · intro c hc
          have hc' : ∀ c' : β, f c' ≠ c.1 := by
            intro c' hcc
            exact hc ⟨⟨c', (hm c').2 (hcc ▸ c.2)⟩, Subtype.ext hcc⟩
          split_ifs with h1
          · rfl
          · have h0 : s.g (f x) c.1 = 0 := hs _ _ hc'
            simp [Ledge, State.h, State.F, entryAbsSquare, Matrix.smul_apply, h0]
        · intro c
          have hiff : (c = ⟨a, ha⟩) ↔ ((⟨f c.1, (hm c.1).1 c.2⟩ : survivors (f x)) =
              ⟨f a, (hm a).1 ha⟩) := by
            constructor
            · intro h; subst h; rfl
            · intro h; exact Subtype.ext (hf (congrArg Subtype.val h))
          by_cases hc : c = ⟨a, ha⟩
          · rw [if_pos hc, if_pos (hiff.1 hc)]
          · rw [if_neg hc, if_neg (fun h => hc (hiff.2 h))]
            rfl
      · have hab' : (⟨f a, (hm a).1 ha⟩ : survivors (f x)) ≠ ⟨f b, (hm b).1 hb⟩ := by
          intro h; exact hab (hf (congrArg Subtype.val h))
        have hab'' : (⟨a, ha⟩ : survivors x) ≠ ⟨b, hb⟩ := by
          intro h; exact hab (congrArg Subtype.val h)
        rw [if_neg hab'', if_neg hab']
        rfl
    · rw [dif_pos ha, dif_neg hb, dif_pos ((hm a).1 ha), dif_neg (fun h => hb ((hm b).2 h))]
  · rw [dif_neg ha, dif_neg (fun h => ha ((hm a).2 h))]

/-- A quadratic form of a submatrix is the form of the zero extension. -/
theorem qform_submatrix (f : β → α) (hf : Function.Injective f) (M : RMat α) (v : β → ℝ)
    (w : α → ℝ) (hw : ∀ c, w (f c) = v c) (hw0 : ∀ p, (∀ c, f c ≠ p) → w p = 0) :
    qform (M.submatrix f f) v = qform M w := by
  have hsum : ∀ G : α → ℝ, (∀ p, (∀ c, f c ≠ p) → G p = 0) →
      ∑ c, G (f c) = ∑ p, G p := by
    intro G hG
    exact Fintype.sum_of_injective f hf _ _ (fun p hp => hG p (fun c hc => hp ⟨c, hc⟩))
      (fun _ => rfl)
  simp only [qform, Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
  have h1 := hsum (fun p => w p * ∑ p', M p p' * w p') (fun p hp => by simp [hw0 p hp])
  beta_reduce at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h2 := hsum (fun p' => M (f c) p' * w p') (fun p hp => by simp [hw0 p hp])
  beta_reduce at h2
  rw [hw c, ← h2]
  simp only [hw]

end Comap

theorem padMem {P : Type*} [DecidableEq P] {γ : Type*} [Zero γ] (S : Finset P)
    (A : Matrix S S γ) {a b : P} (ha : a ∈ S) (hb : b ∈ S) : pad S A a b = A ⟨a, ha⟩ ⟨b, hb⟩ := by
  simp [pad, ha, hb]

/-! ## The pull-back of a sweep sequence: restriction to `S`, then reindexing -/

section Pull
variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  (S : Finset P) (E : Q ≃ {p // p ∈ S})

/-- Restrict to the ports of `S`, then reindex along `E`. -/
def pull (q : Sequence P) : Sequence Q := (q.restrictLive S).reindex E.symm

/-- The port map of the pull-back. -/
def pmap : Q → P := fun a => (E a : P)

theorem pmap_injective : Function.Injective (pmap S E) := by
  intro a b h
  exact E.injective (Subtype.ext h)

theorem pmap_range {p : P} (h : ∀ c, pmap S E c ≠ p) : p ∉ S := by
  intro hp
  exact h (E.symm ⟨p, hp⟩) (by simp [pmap])

variable (q : Sequence P)

@[simp] theorem pull_length : (pull S E q).length = q.length := rfl

theorem pull_g (k : ℕ) (a b : Q) :
    ((pull S E q).state k).g a b = (q.state k).g (pmap S E a) (pmap S E b) := rfl

theorem mem_pull_live (k : ℕ) (a : Q) :
    a ∈ ((pull S E q).state k).live ↔ pmap S E a ∈ (q.state k).live := by
  rw [pull, Sequence.reindex_state_eq, LiveState.mem_reindex, Equiv.symm_symm,
    Sequence.restrictLive_state_eq, LiveState.mem_restrictLive]
  rfl

theorem pull_pivot_some (k : ℕ) (p : P) (hp : p ∈ S) (h : q.pivot k = some p) :
    (pull S E q).pivot k = some (E.symm ⟨p, hp⟩) := by
  simp [pull, Sequence.reindex, Sequence.restrictLive, h, hp]

theorem pull_pivot_none (k : ℕ) (h : q.pivot k = none) : (pull S E q).pivot k = none := by
  simp [pull, Sequence.reindex, Sequence.restrictLive, h]

theorem pull_ambient (k : ℕ) (r : P → ℂ) :
    ((pull S E q).state k).ambient (fun a => r (pmap S E a)) =
      comap (pmap S E) ((q.state k).ambient r) := by
  have hg : ∀ a b, (((pull S E q).state k).ambient (fun a => r (pmap S E a))).g a b =
      (comap (pmap S E) ((q.state k).ambient r)).g a b := by
    intro a b
    change mask ((pull S E q).state k).live ((pull S E q).state k).g a b =
      mask (q.state k).live (q.state k).g (pmap S E a) (pmap S E b)
    have ha := mem_pull_live S E q k a
    have hb := mem_pull_live S E q k b
    by_cases ha' : pmap S E a ∈ (q.state k).live
    · by_cases hb' : pmap S E b ∈ (q.state k).live
      · rw [mask, padMem _ _ (ha.2 ha') (hb.2 hb'), mask, padMem _ _ ha' hb']
        rfl
      · rw [mask_entry_zero' _ _ _ _ (Or.inr (fun h => hb' (hb.1 h))),
          mask_entry_zero' _ _ _ _ (Or.inr hb')]
    · rw [mask_entry_zero' _ _ _ _ (Or.inl (fun h => ha' (ha.1 h))),
        mask_entry_zero' _ _ _ _ (Or.inl ha')]
  cases h1 : ((pull S E q).state k).ambient (fun a => r (pmap S E a)) with
  | mk g1 r1 =>
    cases h2 : comap (pmap S E) ((q.state k).ambient r) with
    | mk g2 r2 =>
      have hg' : g1 = g2 := by
        funext a b
        have := hg a b
        rw [h1, h2] at this
        exact this
      have hr' : r1 = r2 := by
        have e1 : (((pull S E q).state k).ambient (fun a => r (pmap S E a))).r =
            (comap (pmap S E) ((q.state k).ambient r)).r := rfl
        rw [h1, h2] at e1
        exact e1
      rw [hg', hr']

variable {t : ℝ} {r : P → ℂ}

/-- Steps of the pull-back are the steps of the sweep read at the ports `pmap a`. -/
theorem pull_stepJ (hstart : (q.state 0).live = S) (hwf : q.wellFormed t r) (k : ℕ)
    (hk : k < q.length) (a b : Q) :
    (pull S E q).stepJ t (fun a => r (pmap S E a)) k a b =
      q.stepJ t r k (pmap S E a) (pmap S E b) := by
  cases hp : q.pivot k with
  | none =>
    simp [Sequence.stepJ, hp, pull_pivot_none S E q k hp]
  | some p =>
    have hpS : p ∈ S := by
      have h2 : StepRel t r (q.state k) (q.state (k + 1)) p (q.scalar k) := by
        have h3 := hwf.2 k hk
        rw [hp] at h3
        exact h3
      exact Sequence.live_subset_initial q S hstart hwf k hk.le h2.pivot_live
    simp only [Sequence.stepJ, hp, pull_pivot_some S E q k p hpS hp]
    rw [pull_ambient]
    have ha := mem_pull_live S E q (k + 1) a
    have hb := mem_pull_live S E q (k + 1) b
    have hx : pmap S E (E.symm ⟨p, hpS⟩) = p := by simp [pmap]
    by_cases ha' : pmap S E a ∈ (q.state (k + 1)).live
    · by_cases hb' : pmap S E b ∈ (q.state (k + 1)).live
      · rw [mask, padMem _ _ (ha.2 ha') (hb.2 hb'), mask, padMem _ _ ha' hb']
        change Jinc t _ _ _ a b = Jinc t _ _ _ (pmap S E a) (pmap S E b)
        rw [comap_Jinc _ (pmap_injective S E), hx]
        rfl
      · rw [mask_entry_zero' _ _ _ _ (Or.inr (fun h => hb' (hb.1 h))),
          mask_entry_zero' _ _ _ _ (Or.inr hb')]
    · rw [mask_entry_zero' _ _ _ _ (Or.inl (fun h => ha' (ha.1 h))),
        mask_entry_zero' _ _ _ _ (Or.inl ha')]

theorem pull_stepL (hstart : (q.state 0).live = S) (hwf : q.wellFormed t r) (k : ℕ)
    (hk : k < q.length) (a b : Q) :
    (pull S E q).stepL t (fun a => r (pmap S E a)) k a b =
      q.stepL t r k (pmap S E a) (pmap S E b) := by
  cases hp : q.pivot k with
  | none =>
    simp [Sequence.stepL, hp, pull_pivot_none S E q k hp]
  | some p =>
    have hpS : p ∈ S := by
      have h2 : StepRel t r (q.state k) (q.state (k + 1)) p (q.scalar k) := by
        have h3 := hwf.2 k hk
        rw [hp] at h3
        exact h3
      exact Sequence.live_subset_initial q S hstart hwf k hk.le h2.pivot_live
    simp only [Sequence.stepL, hp, pull_pivot_some S E q k p hpS hp]
    rw [pull_ambient]
    have ha := mem_pull_live S E q (k + 1) a
    have hb := mem_pull_live S E q (k + 1) b
    have hx : pmap S E (E.symm ⟨p, hpS⟩) = p := by simp [pmap]
    have hsupp : ∀ i p', (∀ c, pmap S E c ≠ p') → ((q.state k).ambient r).g i p' = 0 := by
      intro i p' hp'
      have hnS := pmap_range S E hp'
      have hnl : p' ∉ (q.state k).live :=
        fun h => hnS (Sequence.live_subset_initial q S hstart hwf k hk.le h)
      exact mask_entry_zero' _ _ _ _ (Or.inr hnl)
    by_cases ha' : pmap S E a ∈ (q.state (k + 1)).live
    · by_cases hb' : pmap S E b ∈ (q.state (k + 1)).live
      · rw [mask, padMem _ _ (ha.2 ha') (hb.2 hb'), mask, padMem _ _ ha' hb']
        change Linc t _ _ _ a b = Linc t _ _ _ (pmap S E a) (pmap S E b)
        rw [comap_Linc _ (pmap_injective S E) _ _ _ _ hsupp, hx]
        rfl
      · rw [mask_entry_zero' _ _ _ _ (Or.inr (fun h => hb' (hb.1 h))),
          mask_entry_zero' _ _ _ _ (Or.inr hb')]
    · rw [mask_entry_zero' _ _ _ _ (Or.inl (fun h => ha' (ha.1 h))),
        mask_entry_zero' _ _ _ _ (Or.inl ha')]

theorem pull_Jrecord (hstart : (q.state 0).live = S) (hwf : q.wellFormed t r) (k : ℕ)
    (hk : k ≤ q.length) :
    (pull S E q).Jrecord t (fun a => r (pmap S E a)) (Finset.range k) =
      (q.Jrecord t r (Finset.range k)).submatrix (pmap S E) (pmap S E) := by
  ext a b
  simp only [Sequence.Jrecord, Matrix.sum_apply, Matrix.submatrix_apply]
  refine Finset.sum_congr rfl fun l hl => ?_
  exact pull_stepJ S E q hstart hwf l (lt_of_lt_of_le (Finset.mem_range.1 hl) hk) a b

theorem pull_Lrecord (hstart : (q.state 0).live = S) (hwf : q.wellFormed t r) (k : ℕ)
    (hk : k ≤ q.length) :
    (pull S E q).Lrecord t (fun a => r (pmap S E a)) (Finset.range k) =
      (q.Lrecord t r (Finset.range k)).submatrix (pmap S E) (pmap S E) := by
  ext a b
  simp only [Sequence.Lrecord, Matrix.sum_apply, Matrix.submatrix_apply]
  refine Finset.sum_congr rfl fun l hl => ?_
  exact pull_stepL S E q hstart hwf l (lt_of_lt_of_le (Finset.mem_range.1 hl) hk) a b

/-- The live ports of the pull-back at a step, as the live ports of the sweep. -/
def pullLiveEquiv (k : ℕ) (hsub : (q.state k).live ⊆ S) :
    ((pull S E q).state k).live ≃ (q.state k).live where
  toFun a := ⟨pmap S E a.1, (mem_pull_live S E q k a.1).1 a.2⟩
  invFun p := ⟨E.symm ⟨p.1, hsub p.2⟩, (mem_pull_live S E q k _).2 (by simp [pmap])⟩
  left_inv a := by apply Subtype.ext; simp [pmap]
  right_inv p := by apply Subtype.ext; simp [pmap]

theorem pull_state (k : ℕ) (hsub : (q.state k).live ⊆ S) :
    ((pull S E q).state k).state (fun a => r (pmap S E a)) =
      AgentS45.State.reindex (pullLiveEquiv S E q k hsub) ((q.state k).state r) := rfl

end Pull

end AndersonAC.AgentS78stransp

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S45 (splitPorts initialPorts reserves)
open AndersonAC.AgentS78stransp
open scoped Matrix.Norms.L2Operator

variable {d m : ℕ}

/-- The ports of `Fin n ≃ active` as the ports of a finset of torus ports over the active
sites. -/
def finPortEquiv {n : ℕ} (x : RunRecord d m) (e : Fin n ≃ x.endpoint.active)
    (S : Finset (Port d m)) (hS : ∀ p : Port d m, p ∈ S ↔ p.1 ∈ x.endpoint.active) :
    initialPorts (Fin n) ≃ {p // p ∈ S} where
  toFun a := ⟨((e a.1).1, a.2), (hS _).2 (e a.1).2⟩
  invFun p := (e.symm ⟨p.1.1, (hS p.1).1 p.2⟩, p.1.2)
  left_inv a := by
    change ((e.symm ⟨(e a.1).1, _⟩, a.2) : Fin n × Bool) = a
    simp
    rfl
  right_inv p := by
    apply Subtype.ext
    change (((e (e.symm ⟨p.1.1, _⟩)).1, p.1.2) : Port d m) = p.1
    simp
    rfl

/-- A finset of torus ports over the active sites as the active-site port space. -/
def activePortEquiv (x : RunRecord d m) (S : Finset (Port d m))
    (hS : ∀ p : Port d m, p ∈ S ↔ p.1 ∈ x.endpoint.active) :
    {p // p ∈ S} ≃ initialPorts {i // i ∈ x.endpoint.active} where
  toFun p := (⟨p.1.1, (hS p.1).1 p.2⟩, p.1.2)
  invFun a := ⟨(a.1.1, a.2), (hS (a.1.1, a.2)).2 a.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The sweep transport for every sweep** (`SweepTransportFullStatement`, FinalSweep.lean:
`SweepTransportStatement` with `j ≤ m + 1`, the final residual sweep included). -/
theorem sweepTransportFull_proof (d : ℕ) : SweepTransportFullStatement d := by
  intro C Cb Crow m n₀ u E ρ P j x hn hu hu' hnj hjm h hrow
  classical
  subst hn hu
  have htpos : 0 < sweepScale P.u m j := sweepScale_pos hu' m j
  set t := sweepScale P.u m j with ht
  set θ := sweepTheta P.u m j with hθ
  have hwf : x.sweep.wellFormed t (portR θ x.r) := h.wellFormed
  set S := (x.sweep.state 0).live with hSdef
  have hS : ∀ p : Port d m, p ∈ S ↔ p.1 ∈ x.endpoint.active := by
    intro p; rw [hSdef, h.start_live]; simp [liveStart]
  have hpiv : ∀ k < x.sweep.length, ∀ p, x.sweep.pivot k = some p → p ∈ S := by
    intro k hk p hp
    have h2 : S45.StepRel t (portR θ x.r) (x.sweep.state k) (x.sweep.state (k + 1)) p
        (x.sweep.scalar k) := by
      have h3 := hwf.2 k hk
      rw [hp] at h3
      exact h3
    exact S45.Sequence.live_subset_initial x.sweep S rfl hwf k hk.le h2.pivot_live
  have hsub : ∀ k ≤ x.sweep.length, (x.sweep.state k).live ⊆ S :=
    fun k hk => S45.Sequence.live_subset_initial x.sweep S rfl hwf k hk
  let e : Fin x.endpoint.active.card ≃ x.endpoint.active := x.endpoint.active.equivFin.symm
  let EE := finPortEquiv x e S hS
  have hr0 : ((splitPorts (Fin x.endpoint.active.card) θ).liftState
      (toS45 x.endpoint x.r e)).r = fun a => portR θ x.r (pmap S EE a) := rfl
  have hwf' : (pull S EE x.sweep).wellFormed t (fun a => portR θ x.r (pmap S EE a)) :=
    S45.Sequence.wellFormed_reindex EE.symm _ t (fun p : {p // p ∈ S} => portR θ x.r p.1) _
      (fun _ => rfl) (S45.Sequence.wellFormed_restrictLive x.sweep S hwf hpiv)
  have hlive0 : ((pull S EE x.sweep).state 0).live = Finset.univ :=
    S45.Sequence.reindex_start EE.symm _ (S45.Sequence.restrictLive_start x.sweep S rfl)
  have hg0 : (x.sweep.state 0).g = (sweepStartLiveState θ x).g := by rw [h.start_lift]
  have hstart_g : ((pull S EE x.sweep).state 0).g = ((splitPorts (Fin x.endpoint.active.card) θ).liftState
      (toS45 x.endpoint x.r e)).g := by
    funext a b
    change (x.sweep.state 0).g (pmap S EE a) (pmap S EE b) = _
    rw [hg0]
    rfl
  have hamb : ((pull S EE x.sweep).state 0).ambient (fun a => portR θ x.r (pmap S EE a)) =
      (splitPorts (Fin x.endpoint.active.card) θ).liftState (toS45 x.endpoint x.r e) := by
    unfold S45.LiveState.ambient
    rw [hlive0, AgentS45.mask_univ, hstart_g]
    rfl
  -- the live start state is the v3 start, reindexed
  have hstart_state : (x.sweep.state 0).state (portR θ x.r) =
      AgentS45.State.reindex (activePortEquiv x S hS) (startV3 P j x.endpoint x.r) := by
    apply state_ext
    · funext a b
      change (x.sweep.state 0).g a.1 b.1 = _
      rw [hg0]
      rfl
    · rfl
  obtain ⟨Λplus, Wstar, hpre, -⟩ := h.start.start_prestate
  have hsw0 : ((((pull S EE x.sweep).state 0).state (fun a => portR θ x.r (pmap S EE a))).g).IsSymm ∧
      (((pull S EE x.sweep).state 0).state (fun a => portR θ x.r (pmap S EE a))).ward t := by
    rw [pull_state S EE x.sweep 0 (hsub 0 (Nat.zero_le _)), hstart_state]
    exact ⟨reindex_isSymm _ _ (reindex_isSymm _ _ hpre.symmetric),
      reindex_ward _ _ _ (reindex_ward _ _ _ hpre.ward)⟩
  have hsw := wellFormed_symm_ward htpos hwf' hsw0.1 hsw0.2
  unfold SweepS45Facts
  refine ⟨x.endpoint.active.card, e, pull S EE x.sweep, ?_, hlive0, hstart_g, ?_, fun i k => rfl, ?_, ?_, ?_⟩
  · rw [hr0]; exact hwf'
  · -- the live set at the end
    ext a
    rw [mem_pull_live, pull_length, h.live_end]
    simp only [reserves, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h' => h'.2, fun h' => ⟨(e a.1).2, h'⟩⟩
  · rw [hr0]; exact hsw
  · intro k hk
    have hk' : k ≤ x.sweep.length := hk
    obtain ⟨v1, v2, v3, v4⟩ := h.valid k hk'
    rw [hr0]
    unfold S45.Sequence.valid
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [pull_Jrecord S EE x.sweep rfl hwf k hk',
        norm_submatrix_of_support (pmap S EE) (pmap_injective S EE)]
      · exact v1
      · intro i i' hii
        exact S45.Sequence.Jrecord_supported x.sweep S t _ hwf rfl _
          (Finset.range_subset_range.2 hk') i i'
          (hii.imp (pmap_range S EE) (pmap_range S EE))
    · intro f
      let w : Port d m → ℝ := fun p => if hp : p ∈ S then f (EE.symm ⟨p, hp⟩) else 0
      have hw : ∀ c, w (pmap S EE c) = f c := by
        intro c
        simp only [w]
        congr 1
        simp [pmap]
      have hw0 : ∀ p, (∀ c, pmap S EE c ≠ p) → w p = 0 := by
        intro p hp
        simp only [w, dite_eq_right_iff]
        intro h; exact absurd h (pmap_range S EE hp)
      have hD : (((splitPorts (Fin x.endpoint.active.card) θ).liftState
          (toS45 x.endpoint x.r e)).D t) =
          (stageD0 P j x).submatrix (pmap S EE) (pmap S EE) := by
        ext a b
        rw [Matrix.submatrix_apply, stageD0, ← hamb, pull_ambient,
          comap_D _ (pmap_injective S EE)]
      rw [pull_Lrecord S EE x.sweep rfl hwf k hk', hD,
        qform_submatrix _ (pmap_injective S EE) _ f w hw hw0,
        qform_submatrix _ (pmap_injective S EE) _ f w hw hw0]
      exact v2 w
    · intro i
      rw [pull_state S EE x.sweep k (hsub k hk'), AgentS45.State.reindex_fourthRow]
      exact v3 _
    · intro i
      rw [pull_state S EE x.sweep k (hsub k hk'), AgentS78send.reindex_lag]
      exact v4 _
  · intro i
    rw [hr0, pull_ambient]
    refine le_trans ?_ (hrow (e i).1 (e i).2)
    have hemb : Function.Injective (pmap S EE) := pmap_injective S EE
    calc ∑ b ∈ (reserves : Finset (initialPorts (Fin x.endpoint.active.card))),
          ‖(comap (pmap S EE) ((x.sweep.state x.sweep.length).ambient (portR θ x.r))).h t
            (i, true) b‖ ^ 4
        = ∑ b ∈ (reserves : Finset (initialPorts (Fin x.endpoint.active.card))),
          ‖((x.sweep.state x.sweep.length).ambient (portR θ x.r)).h t
            ((e i).1, true) (pmap S EE b)‖ ^ 4 := rfl
      _ = ∑ p ∈ (reserves : Finset (initialPorts (Fin x.endpoint.active.card))).map
            ⟨pmap S EE, hemb⟩,
          ‖((x.sweep.state x.sweep.length).ambient (portR θ x.r)).h t ((e i).1, true) p‖ ^ 4 :=
          by rw [Finset.sum_map]; try rfl
      _ ≤ ∑ p ∈ (reserves : Finset (Port d m)),
          ‖((x.sweep.state x.sweep.length).ambient (portR θ x.r)).h t ((e i).1, true) p‖ ^ 4 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
          intro p hp
          obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 hp
          simp only [reserves, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
          exact hb

/-- **The sweep transport** (`SweepTransportStatement`, SweepEnd.lean:180), the digit form. -/
theorem sweepTransport_proof (d : ℕ) : SweepTransportStatement d :=
  (sweepTransportFull_proof d).digit

end AndersonAC.AgentS78
