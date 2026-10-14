import AndersonAC.AgentS78.Construction.SweepSchur
import AndersonAC.AgentS78.Construction.TileStartDecayProof

/-!
# WP10 tile phase: the prefix Schur identity (P1)

agent-s78start (2026-10-14). `prefixPhys_proof : PrefixPhysStatement`: the invariant of
agent-s78schur's `sweepSchur_proof` (lane/agent-s78schur 009e745, Sherman–Morrison per
`StepRel` step) at every prefix of a well-formed bit-pivot sequence (steps without pivot
allowed), in the form `M_A + diag ζ − t diag(ϑ r)` of eq:sweep-physical-prefix (04:46–55).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

open Classical in
/-- **The prefix Schur identity (P1).** -/
theorem prefixPhys_proof : PrefixPhysStatement := by
  intro d m t θ x q ht hθ0 hθ1 hD hwf h0 hpiv
  classical
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
  have hs2 : s * s = 1 - θ := Real.mul_self_sqrt hw.le
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
      have hwk := hwf.2 k hk'
      cases hpk : q.pivot k with
      | none =>
        rw [hpk] at hwk
        have hst : q.state (k + 1) = q.state k := hwk
        have hLk : L (k + 1) = L k := by simp only [L, hst]
        have hSk : ∀ i, S (k + 1) i = S k i := by
          intro i
          simp only [S, Finset.sum_range_succ, hpk]
          simp
        have hDk : D (k + 1) = D k := by
          funext a; simp only [D, hSk, hLk]
        refine ⟨fun p hp => hLA p (by rw [← hLk]; exact hp), G, ?_, ?_⟩
        · have hHk : H (k + 1) = H k := by simp only [H, hDk]
          rw [hHk]; exact hHG
        · intro p hp p' hp'
          rw [hst]
          exact hg p (by rw [← hLk]; exact hp) p' (by rw [← hLk]; exact hp')
      | some y =>
        have hy2 : y.2 = false := hpiv k hk' y hpk
        set i := y.1
        have hyb : y = bitPort i := Prod.ext rfl hy2
        rw [hpk] at hwk
        have hpk2 : q.pivot k = some (bitPort i) := by rw [hpk, hyb]
        have hstep : S45.StepRel t (portR θ x.r) (q.state k) (q.state (k + 1))
            (bitPort i) (q.scalar k) := hyb ▸ hwk
        have hx : bitPort i ∈ L k := hstep.pivot_live
        have hLs : L (k + 1) = (L k).erase (bitPort i) := hstep.survivors
        have hi : i ∈ A := hLA (bitPort i) hx
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
              simp only [D, S, Finset.sum_range_succ, hpk2, if_pos rfl, if_pos hx, if_neg hnot,
                Pi.single_eq_same, hu, ii]
              push_cast
              ring
            · have hne : a.val ≠ i := fun h => hai (Subtype.ext h)
              have hne' : bitPort a.val ≠ bitPort i := fun h => hne (bitPort_injective h)
              have hmem : bitPort a.val ∈ L (k + 1) ↔ bitPort a.val ∈ L k := by
                rw [hLs, Finset.mem_erase]
                exact ⟨fun h => h.2, fun h => ⟨hne', h⟩⟩
              have hpne : q.pivot k ≠ some (bitPort a.val) := by
                rw [hpk2]; exact fun h => hne' (Option.some_injective _ h).symm
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
  -- the prefix form
  intro k hk
  obtain ⟨_, G, hHG, hg⟩ := inv k hk
  refine ⟨fun i => s * S k i, G, ?_, fun p p' hp hp' => hg p hp p' hp'⟩
  have hBH : H k = x.endpoint.M.submatrix (Subtype.val : A → Torus d m) Subtype.val +
      Matrix.diagonal (fun i : A => (((s * S k i.val : ℝ)) : ℂ)) -
      ((t : ℝ) : ℂ) • Matrix.diagonal (fun i : A =>
        ((prefixVartheta θ (q.state k).live i.val : ℝ) : ℂ) * x.r i.val) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp only [H, H0, D, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.diagonal_apply_eq, smul_eq_mul, prefixVartheta, r, L]
      by_cases hb : bitPort a.val ∈ (q.state k).live
      · have hb' : ((a.val, false) : Port d m) ∈ (q.state k).live := hb
        simp only [if_pos hb, if_pos hb']
        push_cast; ring
      · have hb' : ((a.val, false) : Port d m) ∉ (q.state k).live := hb
        simp only [if_neg hb, if_neg hb']
        push_cast; ring
    · have hab' : a.val ≠ b.val := fun h => hab (Subtype.ext h)
      simp [H, H0, Matrix.diagonal_apply_ne _ hab]
  rw [← hBH]
  exact hHG

/-- **The duplicated stage start (v3), conditional only on Combes–Thomas (P2).** -/
theorem tileStartV3_of_CT {d : ℕ} (hd : 3 ≤ d) (hCT : ActiveCTStatement d) :
    TileStartV3Statement d :=
  tileStartV3_of_parts hd prefixPhys_proof hCT

end AndersonAC.AgentS78
