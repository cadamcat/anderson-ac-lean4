import AndersonAC.AgentS78.Construction.TilePhaseContracts

/-!
# The duplicated-port sweep identity (04-sweep.tex:190–228)

agent-s78schur (2026-10-14). Proof of the frozen contract `SweepSchurStatement`
(TilePhaseContracts.lean). Route: Sherman–Morrison for every `StepRel` step.

Invariant along the sweep: with `K` the port weights of `splitPorts θ`
(`w^{1/4}` on bit ports, `θ^{1/4}` on reserve ports), on the live ports at step `k`

  `(q.state k).g p p' = K_p K_{p'} G_k (p.1) (p'.1)`,  `H_k G_k = 1` on the active block,

where `H_k = M_A − t·diag r + diag(√w·S_k + t·w·r·[bit port deleted])` and `S_k i` is the sum
of the scalars of the steps `< k` that delete the bit port of `i`. Deleting the bit port
`(i, false)` with scalar `ξ` is the rank-one update `H ↦ H + (√w ξ + t w r_i) E_ii`. At the end
every bit port of an active site is deleted, so `H_end = M_A + diag ζ − θ t·diag r`
(`ζ = √w S`), and the reserve block of `g` is `√θ·H_end⁻¹`.

The corollary `sweepEndMapTheta_isDamped` states the consumer form: after a complete sweep
from the start lift of a damped endpoint, the endpoint committed by `sweepEndMapTheta`
(lane/agent-s78 3c09f7f, `M := M + diag(sweepIncrement)`) is damped at `θ t`.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- Sherman–Morrison for a rank-one diagonal update `H + u E_ii`. -/
theorem shermanMorrison_diag {n : Type*} [Fintype n] [DecidableEq n]
    (H G : Matrix n n ℂ) (hHG : H * G = 1) (i : n) (u : ℂ) (hd : 1 + u * G i i ≠ 0) :
    (H + Matrix.diagonal (Pi.single i u)) *
      Matrix.of (fun a b => G a b - u * G a i * G i b / (1 + u * G i i)) = 1 := by
  have h1 : ∀ a b, ∑ c, H a c * G c b = (1 : Matrix n n ℂ) a b := fun a b => by
    rw [← hHG]; rfl
  ext a b
  rw [Matrix.add_mul, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_apply]
  simp only [Matrix.of_apply]
  have hs : ∑ c, H a c * (G c b - u * G c i * G i b / (1 + u * G i i)) =
      (∑ c, H a c * G c b) - (∑ c, H a c * G c i) * (u * G i b / (1 + u * G i i)) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [hs, h1, h1]
  by_cases hai : a = i
  · subst hai
    simp only [Pi.single_eq_same, Matrix.one_apply_eq]
    field_simp
    ring
  · simp [Pi.single_eq_of_ne hai, Matrix.one_apply_ne hai]

/-- `a^{1/4} · a^{1/4} = √a` for `a > 0`. -/
theorem power_quarter_mul_self {a : ℝ} (ha : 0 < a) :
    S45.power a (1 / 4) * S45.power a (1 / 4) = Real.sqrt a := by
  show a ^ (1 / 4 : ℝ) * a ^ (1 / 4 : ℝ) = Real.sqrt a
  rw [← Real.rpow_add ha, Real.sqrt_eq_rpow]
  norm_num

/-- The bit port `(i, false)`, typed in `Port d m`. -/
def bitPort {d m : ℕ} (i : Torus d m) : Port d m := (i, false)

/-- The reserve port `(i, true)`, typed in `Port d m`. -/
def resPort {d m : ℕ} (i : Torus d m) : Port d m := (i, true)

theorem bitPort_injective {d m : ℕ} : Function.Injective (bitPort (d := d) (m := m)) := by
  intro i j h
  have := congrArg Prod.fst h
  exact this

theorem portR_bitPort {d m : ℕ} (θ : ℝ) (r : Torus d m → ℂ) (i : Torus d m) :
    portR θ r (bitPort i) =
      ((S45.splitPorts (Torus d m) θ).weight (bitPort i) : ℂ) ^ 2 * r i := by
  simp [portR, S45.PortMap.liftState, bitPort, S45.splitPorts]

open Classical in
/-- **The duplicated-port sweep identity** (04-sweep.tex:190–228). -/
theorem sweepSchur_proof : SweepSchurStatement := by
  intro d m t θ x q ht hθ0 hθ1 hD hwf h0 hpiv hend
  classical
  -- notation
  let A := x.endpoint.active
  let r := x.r
  let L : ℕ → Finset (Port d m) := fun k => (q.state k).live
  let kw : Port d m → ℝ := (S45.splitPorts (Torus d m) θ).weight
  let s : ℝ := Real.sqrt (1 - θ)
  let S : ℕ → Torus d m → ℝ := fun k i => ∑ l ∈ Finset.range k,
    if q.pivot l = some (bitPort i) then q.scalar l else 0
  let H0 : Matrix A A ℂ := x.endpoint.M.submatrix Subtype.val Subtype.val -
    (t : ℂ) • Matrix.diagonal fun i : A => r i.val
  let D : ℕ → A → ℂ := fun k i => ((s * S k i.val : ℝ) : ℂ) +
    if bitPort i.val ∈ L k then 0 else ((t * (1 - θ) : ℝ) : ℂ) * r i.val
  let H : ℕ → Matrix A A ℂ := fun k => H0 + Matrix.diagonal (D k)
  have hw : 0 < 1 - θ := by linarith
  have hkbit : ∀ i : Torus d m, kw (bitPort i) * kw (bitPort i) = s := by
    intro i
    show S45.power (if false = true then θ else 1 - θ) (1 / 4) *
      S45.power (if false = true then θ else 1 - θ) (1 / 4) = _
    rw [if_neg Bool.false_ne_true]
    exact power_quarter_mul_self hw
  have hkres : ∀ i : Torus d m, kw (resPort i) * kw (resPort i) = Real.sqrt θ := by
    intro i
    show S45.power (if true = true then θ else 1 - θ) (1 / 4) *
      S45.power (if true = true then θ else 1 - θ) (1 / 4) = _
    rw [if_pos rfl]
    exact power_quarter_mul_self hθ0
  have hs2 : s * s = 1 - θ := Real.mul_self_sqrt hw.le
  -- the invariant
  have inv : ∀ k ≤ q.length, (∀ p ∈ L k, p.1 ∈ A) ∧
      ∃ G : Matrix (Torus d m) (Torus d m) ℂ,
        H k * G.submatrix Subtype.val Subtype.val = 1 ∧
        ∀ p ∈ L k, ∀ p' ∈ L k, (q.state k).g p p' = (kw p : ℂ) * (kw p' : ℂ) * G p.1 p'.1 := by
    intro k
    induction k with
    | zero =>
      intro _
      have hL0 : ∀ p : Port d m, p ∈ L 0 ↔ p.1 ∈ A := by
        intro p
        show p ∈ (q.state 0).live ↔ _
        rw [h0]
        simp [sweepStartLiveState, A]
      refine ⟨fun p hp => (hL0 p).mp hp, x.endpoint.g, ?_, ?_⟩
      · have hH : H 0 = x.endpoint.M.submatrix (fun i : A => i.val) (fun i : A => i.val) -
            (t : ℂ) • Matrix.diagonal (fun i : A => r i.val) := by
          have hD0 : D 0 = 0 := by
            funext i
            have hi : bitPort i.val ∈ L 0 := (hL0 _).mpr i.2
            simp [D, S, hi]
          show H0 + Matrix.diagonal (D 0) = _
          rw [hD0, show Matrix.diagonal (0 : A → ℂ) = 0 from Matrix.diagonal_zero, add_zero]
        rw [hH]
        exact hD.2.2.1
      · intro p _ p' _
        rw [h0]
        rfl
    | succ k ih =>
      intro hk
      have hk' : k < q.length := hk
      obtain ⟨hLA, G, hHG, hg⟩ := ih hk'.le
      obtain ⟨i, hpk'⟩ := hpiv k hk'
      have hpk : q.pivot k = some (bitPort i) := hpk'
      have hstep : S45.StepRel t (portR θ x.r) (q.state k) (q.state (k + 1))
          (bitPort i) (q.scalar k) := by
        have := hwf.2 k hk'
        rw [hpk] at this
        exact this
      have hx : bitPort i ∈ L k := hstep.pivot_live
      have hLs : L (k + 1) = (L k).erase (bitPort i) := hstep.survivors
      have hi : i ∈ A := hLA _ hx
      let ii : A := ⟨i, hi⟩
      let c : ℂ := (q.scalar k : ℂ) + t * portR θ x.r (bitPort i)
      let u : ℂ := c * (kw (bitPort i) : ℂ) * (kw (bitPort i) : ℂ)
      have hk2 : ((kw (bitPort i) : ℂ)) * (kw (bitPort i) : ℂ) = (s : ℂ) := by
        rw [← Complex.ofReal_mul, hkbit]
      have hu : u = ((s * q.scalar k : ℝ) : ℂ) + ((t * (1 - θ) : ℝ) : ℂ) * r i := by
        have hpr : portR θ x.r (bitPort i) = (kw (bitPort i) : ℂ) ^ 2 * r i :=
          portR_bitPort θ x.r i
        have hs2c : (s : ℂ) * (s : ℂ) = 1 - (θ : ℂ) := by
          rw [← Complex.ofReal_mul, hs2]; push_cast; ring
        simp only [u, c, hpr]
        rw [mul_assoc, hk2, sq, hk2]
        push_cast
        linear_combination (t : ℂ) * r i * hs2c
      have hden : 1 + c * (q.state k).g (bitPort i) (bitPort i) =
          1 + u * (G.submatrix Subtype.val Subtype.val) ii ii := by
        rw [hg _ hx _ hx]
        show 1 + c * (_ * _ * G i i) = _
        simp only [u, Matrix.submatrix_apply, ii]
        ring
      have hden' : 1 + c * (q.state k).g (bitPort i) (bitPort i) = 1 + u * G i i := by
        rw [hden]; rfl
      have hd : 1 + u * (G.submatrix Subtype.val Subtype.val) ii ii ≠ 0 := by
        rw [← hden]; exact hstep.denominator
      have hLsub : ∀ p ∈ L (k + 1), p ∈ L k := fun p hp => by
        rw [hLs] at hp; exact Finset.mem_of_mem_erase hp
      refine ⟨fun p hp => hLA p (hLsub p hp),
        fun a b => G a b - u * G a i * G i b / (1 + u * G i i), ?_, ?_⟩
      · have hDs : D (k + 1) = D k + Pi.single ii u := by
          funext a
          simp only [Pi.add_apply]
          by_cases hai : a = ii
          · subst hai
            have hnot : bitPort i ∉ L (k + 1) := by
              rw [hLs]; exact Finset.notMem_erase _ _
            simp only [D, S, Finset.sum_range_succ, hpk, if_pos rfl, if_pos hx, if_neg hnot,
              Pi.single_eq_same, hu, ii]
            push_cast
            ring
          · have hne : a.val ≠ i := fun h => hai (Subtype.ext h)
            have hne' : bitPort a.val ≠ bitPort i := fun h => hne (bitPort_injective h)
            have hmem : bitPort a.val ∈ L (k + 1) ↔ bitPort a.val ∈ L k := by
              rw [hLs, Finset.mem_erase]
              exact ⟨fun h => h.2, fun h => ⟨hne', h⟩⟩
            have hpne : q.pivot k ≠ some (bitPort a.val) := by
              rw [hpk]; exact fun h => hne' (Option.some_injective _ h).symm
            simp only [D, S, Finset.sum_range_succ, if_neg hpne, add_zero, hmem,
              Pi.single_eq_of_ne hai]
        have hH : H (k + 1) = H k + Matrix.diagonal (Pi.single ii u) := by
          show H0 + Matrix.diagonal (D (k + 1)) = H0 + Matrix.diagonal (D k) + _
          rw [hDs, add_assoc, Matrix.diagonal_add]
          rfl
        rw [hH]
        exact shermanMorrison_diag _ _ hHG ii u hd
      · intro p hp p' hp'
        have hpk' := hLsub p hp
        have hp'k := hLsub p' hp'
        rw [hstep.update]
        simp only [S45.mask, S45.pad, S45.restrict, Matrix.submatrix_apply]
        rw [dif_pos hp, dif_pos hp']
        change (q.state k).g p p' - c * (q.state k).g p (bitPort i) *
          (q.state k).g (bitPort i) p' / (1 + c * (q.state k).g (bitPort i) (bitPort i)) = _
        rw [hden']
        rw [hg _ hpk' _ hp'k, hg _ hpk' _ hx, hg _ hx _ hp'k]
        have hb1 : (bitPort i).1 = i := rfl
        simp only [u, hb1]
        ring
  -- the end of the sweep
  obtain ⟨_, G, hHG, hg⟩ := inv q.length le_rfl
  have hbit : ∀ i : Torus d m, bitPort i ∉ L q.length := by
    intro i hi
    have := ((hend _).mp hi).2
    exact Bool.false_ne_true this
  have hres : ∀ i : A, resPort i.val ∈ L q.length := fun i =>
    (hend _).mpr ⟨i.2, rfl⟩
  intro ζ B G'
  have hBH : B = H q.length := by
    ext a b
    have hζ : ζ a.val = s * S q.length a.val := by
      simp only [ζ, S, Finset.mul_sum, mul_ite, mul_zero]
      refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd h1 h2
      · exact absurd h2 h1
      · rfl
    by_cases hab : a = b
    · subst hab
      have hD' : D q.length a = ((s * S q.length a.val : ℝ) : ℂ) +
          ((t * (1 - θ) : ℝ) : ℂ) * r a.val := by
        simp only [D, if_neg (hbit a.val)]
      simp only [B, H, H0, Matrix.sub_apply, Matrix.add_apply, Matrix.submatrix_apply,
        Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul, hD', hζ, r]
      push_cast
      ring
    · have hab' : a.val ≠ b.val := fun h => hab (Subtype.ext h)
      simp [B, H, H0, Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ hab']
  have hGG : G' = G.submatrix Subtype.val Subtype.val := by
    ext a b
    have hθc : (Real.sqrt θ : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr hθ0).ne'
    have hk : (kw (resPort a.val) : ℂ) * (kw (resPort b.val) : ℂ) = (Real.sqrt θ : ℂ) := by
      have hab : kw (resPort a.val) = kw (resPort b.val) := rfl
      rw [← Complex.ofReal_mul, ← hab, hkres]
    show (q.state q.length).g (resPort a.val) (resPort b.val) / (Real.sqrt θ : ℂ) = _
    rw [hg _ (hres a) _ (hres b), hk, Matrix.submatrix_apply]
    show (Real.sqrt θ : ℂ) * G a.val b.val / (Real.sqrt θ : ℂ) = G a.val b.val
    field_simp
  rw [hBH, hGG]
  exact ⟨hHG, mul_eq_one_comm.mp hHG⟩

/-- `IsDampedEndpoint` read through an equality of the active set. -/
theorem isDampedEndpoint_of_active_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Endpoint ι) (r : ι → ℂ) (t : ℝ) (A : Finset ι) (hA : s.active = A)
    (hsym : ∀ i j, s.M i j = s.M j i ∧ (s.M i j).im = 0)
    (hzero : ∀ i j, i ∉ A ∨ j ∉ A → s.g i j = 0)
    (hB : let B := s.M.submatrix (fun i : A => i.val) (fun i : A => i.val) -
        (t : ℂ) • Matrix.diagonal (fun i : A => r i.val)
      let G := s.g.submatrix (fun i : A => i.val) (fun i : A => i.val)
      B * G = 1 ∧ G * B = 1) :
    IsDampedEndpoint s r t := by
  subst hA
  exact ⟨hsym, hzero, hB⟩

/-- **Consumer form.** After a complete sweep from the start lift of a damped endpoint (tile
blocks keep `endpoint`, so `y.endpoint = x.endpoint`), the endpoint committed by
`sweepEndMapTheta θ` (`M + diag(sweepIncrement)`, reserve block `/ √θ`) is damped at `θ t`
with the unchanged `r`. -/
theorem sweepEndMapTheta_isDamped {d m : ℕ} {t θ : ℝ} (x y : RunRecord d m)
    (ht : 0 < t) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hD : IsDampedEndpoint x.endpoint x.r t)
    (hy : y.endpoint = x.endpoint)
    (hwf : y.sweep.wellFormed t (portR θ x.r))
    (h0 : y.sweep.state 0 = sweepStartLiveState θ x)
    (hpiv : ∀ k < y.sweep.length, ∃ i, y.sweep.pivot k = some ((i, false) : Port d m))
    (hend : ∀ p : Port d m, p ∈ (y.sweep.state y.sweep.length).live ↔
      p.1 ∈ x.endpoint.active ∧ p.2 = true) :
    IsDampedEndpoint (sweepEndMapTheta θ y).endpoint x.r (θ * t) := by
  classical
  have hS := sweepSchur_proof d m t θ x y.sweep ht hθ0 hθ1 hD hwf h0 hpiv hend
  obtain ⟨h1, h2⟩ := hS
  have hact : sweepEndActive y = x.endpoint.active := by
    ext i
    simp only [sweepEndActive, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hend (resPort i)).trans ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩
  have hGeq : (sweepEndMatrixTheta θ y).submatrix (fun i : x.endpoint.active => i.val)
      (fun i : x.endpoint.active => i.val) = fun i k =>
        (y.sweep.state y.sweep.length).g ((i.val, true) : Port d m) ((k.val, true) : Port d m) /
          (Real.sqrt θ : ℂ) := by
    ext i k
    simp [sweepEndMatrixTheta, Matrix.submatrix_apply, hact, i.2, k.2]
  have hMeq : sweepEndMTheta θ y = x.endpoint.M + Matrix.diagonal fun i =>
      (((∑ k ∈ Finset.range y.sweep.length,
        if y.sweep.pivot k = some ((i, false) : Port d m) then
          Real.sqrt (1 - θ) * y.sweep.scalar k else 0 : ℝ)) : ℂ) := by
    simp only [sweepEndMTheta, sweepIncrement, hy, Finset.mul_sum, mul_ite, mul_zero]
  refine isDampedEndpoint_of_active_eq _ _ _ _ hact ?_ ?_ ?_
  · intro i j
    simp only [sweepEndMapTheta, hMeq, Matrix.add_apply]
    obtain ⟨hs, hr⟩ := hD.1 i j
    have hr' := (hD.1 j i).2
    by_cases hij : i = j
    · subst hij
      simp [hr]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij), hs, hr']
  · intro i j hij
    show sweepEndMatrixTheta θ y i j = 0
    simp only [sweepEndMatrixTheta, hact]
    rw [if_neg]
    tauto
  · dsimp only [sweepEndMapTheta]
    rw [hGeq, hMeq]
    convert And.intro h1 h2 using 7 <;>
    · refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd h1 h2
      · exact absurd h2 h1
      · rfl

end AndersonAC.AgentS78
