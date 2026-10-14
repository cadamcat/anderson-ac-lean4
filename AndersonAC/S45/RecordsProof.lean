import AndersonAC.S45.Definitions

noncomputable section
open Matrix
open scoped BigOperators

namespace AndersonAC.AgentS45

open AndersonAC.S45

theorem schur_add_supported_proof_records {P : Type*} [Fintype P] [DecidableEq P]
    {𝕜 : Type*} [RCLike 𝕜] (A : Matrix P P 𝕜) (E : Finset P)
    (B : Matrix (↑(Eᶜ) : Type _) (↑(Eᶜ) : Type _) 𝕜) :
    schur (A + pad Eᶜ B) E = schur A E + B := by
  have hEE : restrict (A + pad Eᶜ B) E = restrict A E := by
    ext i j
    simp [restrict, pad]
  have hRR : restrict (A + pad Eᶜ B) Eᶜ = restrict A Eᶜ + B := by
    ext i j
    simp [restrict, pad]
  have hRE :
      (A + pad Eᶜ B).submatrix (fun i : (↑(Eᶜ) : Type _) => i.val)
        (fun j : E => j.val) =
      A.submatrix (fun i : (↑(Eᶜ) : Type _) => i.val) (fun j : E => j.val) := by
    ext i j
    simp [pad]
  have hER :
      (A + pad Eᶜ B).submatrix (fun i : E => i.val)
        (fun j : (↑(Eᶜ) : Type _) => j.val) =
      A.submatrix (fun i : E => i.val) (fun j : (↑(Eᶜ) : Type _) => j.val) := by
    ext i j
    simp [pad]
  unfold schur
  rw [hRR, hRE, hEE, hER]
  ext i j
  simp [Matrix.sub_apply, Matrix.add_apply]
  ring

private theorem scalarSchur_mulVec_eq {P : Type*} [Fintype P] [DecidableEq P]
    (A : Matrix P P ℂ) (x : P) (u z : P → ℂ) (hAu : A *ᵥ u = z)
    (ha : A x x ≠ 0) :
    ∀ i : survivors x,
      (scalarSchur A x *ᵥ (fun j => u j.val)) i =
        z i.val - A i.val x * (A x x)⁻¹ * z x := by
  let Rset := survivors x
  let R : Type _ := (↑Rset : Type _)
  have hattach (f : P → ℂ) : (∑ j : R, f j.val) = ∑ j ∈ Rset, f j := by
    simpa [R, Rset] using (Finset.sum_attach (s := Rset) (f := f))
  have hsplit (f : P → ℂ) :
      (∑ j : P, f j) = (∑ j : R, f j.val) + f x := by
    rw [← Finset.univ.sum_erase_add f (Finset.mem_univ x)]
    simpa [Rset, survivors] using congrArg (fun a : ℂ => a + f x) (hattach f).symm
  intro i
  have hrowi : (∑ j : P, A i.val j * u j) = z i.val := by
    simpa [Matrix.mulVec, dotProduct] using congrFun hAu i.val
  have hrowx : (∑ j : P, A x j * u j) = z x := by
    simpa [Matrix.mulVec, dotProduct] using congrFun hAu x
  have hsplit_i := hsplit (fun j => A i.val j * u j)
  have hsplit_x := hsplit (fun j => A x j * u j)
  rw [hrowi] at hsplit_i
  rw [hrowx] at hsplit_x
  have hsum_i : (∑ j : R, A i.val j.val * u j.val) =
      z i.val - A i.val x * u x := by
    calc
      (∑ j : R, A i.val j.val * u j.val) =
          ((∑ j : R, A i.val j.val * u j.val) + A i.val x * u x) -
            A i.val x * u x := by ring
      _ = z i.val - A i.val x * u x := by rw [← hsplit_i]
  have hsum_x : (∑ j : R, A x j.val * u j.val) =
      z x - A x x * u x := by
    calc
      (∑ j : R, A x j.val * u j.val) =
          ((∑ j : R, A x j.val * u j.val) + A x x * u x) - A x x * u x := by ring
      _ = z x - A x x * u x := by rw [← hsplit_x]
  have hfact :
      (∑ j : R, (A i.val x * (A x x)⁻¹ * A x j.val) * u j.val) =
        A i.val x * (A x x)⁻¹ * (∑ j : R, A x j.val * u j.val) := by
    calc
      (∑ j : R, (A i.val x * (A x x)⁻¹ * A x j.val) * u j.val) =
          ∑ j : R, (A i.val x * (A x x)⁻¹) * (A x j.val * u j.val) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = A i.val x * (A x x)⁻¹ * (∑ j : R, A x j.val * u j.val) := by
            rw [← Finset.mul_sum]
  calc
    (scalarSchur A x *ᵥ (fun j => u j.val)) i =
        (∑ j : R, A i.val j.val * u j.val) -
          A i.val x * (A x x)⁻¹ * (∑ j : R, A x j.val * u j.val) := by
            simp only [scalarSchur, Matrix.mulVec, dotProduct]
            simp_rw [sub_mul]
            rw [Finset.sum_sub_distrib, hfact]
    _ = z i.val - A i.val x * (A x x)⁻¹ * z x := by
          rw [hsum_i, hsum_x]
          field_simp [ha]
          ring

private theorem sum_range_sub_telescope {α : Type*} [AddCommGroup α]
    (f : ℕ → α) (n : ℕ) :
    (∑ k ∈ Finset.range n, (f (k + 1) - f k)) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      abel

private theorem sequence_live_step_subset {P : Type*} [Fintype P] [DecidableEq P]
    (q : Sequence P) (t : ℝ) (r : P → ℂ) (hseq : q.wellFormed t r)
    (k : ℕ) (hk : k < q.length) :
    (q.state (k + 1)).live ⊆ (q.state k).live := by
  unfold Sequence.wellFormed at hseq
  have hstep := hseq.2 k hk
  cases hp : q.pivot k with
  | none =>
      simp [hp] at hstep
      rw [hstep]
  | some x =>
      simp [hp] at hstep
      rw [hstep.survivors]
      exact Finset.erase_subset _ _

private theorem final_live_subset {P : Type*} [Fintype P] [DecidableEq P]
    (q : Sequence P) (t : ℝ) (r : P → ℂ) (hseq : q.wellFormed t r) :
    ∀ k ≤ q.length, (q.state q.length).live ⊆ (q.state k).live := by
  have hback : ∀ n, n ≤ q.length →
      (q.state q.length).live ⊆ (q.state (q.length - n)).live := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
        intro hn
        have hn' : n ≤ q.length := by omega
        have hklt : q.length - (n + 1) < q.length := by omega
        have hidx : q.length - n = (q.length - (n + 1)) + 1 := by omega
        have hprev := ih hn'
        rw [hidx] at hprev
        have hmono := sequence_live_step_subset q t r hseq
          (q.length - (n + 1)) hklt
        exact hprev.trans hmono
  intro k hk
  have h := hback (q.length - k) (Nat.sub_le _ _)
  have heq : q.length - (q.length - k) = k := by omega
  simpa [heq] using h

private theorem lag_record_eq_final_sub_initial {P : Type*} [Fintype P]
    [DecidableEq P] (q : Sequence P) (t : ℝ) (r : P → ℂ)
    (hseq : q.wellFormed t r) (i : P)
    (hi : i ∈ (q.state q.length).live) :
    q.lagRecord t r (Finset.range q.length) i =
      (q.state q.length).ambientLag t r i - (q.state 0).ambientLag t r i := by
  have hsub := final_live_subset q t r hseq
  have hterm : ∀ k < q.length, q.stepLag t r k i =
      (q.state (k + 1)).ambientLag t r i - (q.state k).ambientLag t r i := by
    intro k hk
    have hik : i ∈ (q.state (k + 1)).live := hsub (k + 1) (by omega) hi
    simp [Sequence.stepLag, hik]
  have hsum : (∑ k ∈ Finset.range q.length, q.stepLag t r k i) =
      ∑ k ∈ Finset.range q.length,
        ((q.state (k + 1)).ambientLag t r i - (q.state k).ambientLag t r i) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hterm k (Finset.mem_range.mp hk)
  calc
    q.lagRecord t r (Finset.range q.length) i =
        ∑ k ∈ Finset.range q.length, q.stepLag t r k i := by
          simp [Sequence.lagRecord]
    _ = ∑ k ∈ Finset.range q.length,
        ((q.state (k + 1)).ambientLag t r i - (q.state k).ambientLag t r i) := hsum
    _ = (q.state q.length).ambientLag t r i - (q.state 0).ambientLag t r i := by
      simpa using sum_range_sub_telescope (fun k => (q.state k).ambientLag t r i) q.length

private def sequence_row_energy {P : Type*} [Fintype P] [DecidableEq P]
    (q : Sequence P) (t : ℝ) (r : P → ℂ) (cols : Finset P) (i : P) (k : ℕ) : ℝ :=
  ∑ j ∈ cols ∩ (q.state k).live, ‖((q.state k).ambient r).h t i j‖ ^ 4

private theorem sequence_row_energy_step_bound {P : Type*} [Fintype P]
    [DecidableEq P] (q : Sequence P) (t : ℝ) (r : P → ℂ) (cols : Finset P)
    (ht : 0 < t) (hseq : q.wellFormed t r) (i : P)
    (hi : i ∈ (q.state q.length).live) (k : ℕ) (hk : k < q.length) :
    sequence_row_energy q t r cols i (k + 1) - sequence_row_energy q t r cols i k ≤
      rowCap t * q.stepRow t r cols k i := by
  have hsub := final_live_subset q t r hseq
  have hik : i ∈ (q.state (k + 1)).live := hsub (k + 1) (by omega) hi
  let S₀ := cols ∩ (q.state k).live
  let S₁ := cols ∩ (q.state (k + 1)).live
  let a : P → ℝ := fun j => ‖((q.state k).ambient r).h t i j‖ ^ 4
  let b : P → ℝ := fun j => ‖((q.state (k + 1)).ambient r).h t i j‖ ^ 4
  have hlive := sequence_live_step_subset q t r hseq k hk
  have hS : S₁ ⊆ S₀ := by
    intro j hj
    rcases Finset.mem_inter.mp hj with ⟨hjcols, hjnext⟩
    exact Finset.mem_inter.mpr ⟨hjcols, hlive hjnext⟩
  have hsum : (∑ j ∈ S₁, a j) ≤ ∑ j ∈ S₀, a j :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (by
      intro j _ _
      exact pow_nonneg (norm_nonneg _) _)
  have henergy₁ : sequence_row_energy q t r cols i (k + 1) = ∑ j ∈ S₁, b j := by
    simp [sequence_row_energy, S₁, b]
  have henergy₀ : sequence_row_energy q t r cols i k = ∑ j ∈ S₀, a j := by
    simp [sequence_row_energy, S₀, a]
  have hrow : q.stepRow t r cols k i =
      ((∑ j ∈ S₁, b j) - (∑ j ∈ S₁, a j)) / rowCap t := by
    simp [Sequence.stepRow, S₁, a, b, hik, Finset.sum_sub_distrib]
  have hcap : rowCap t ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht _)
  have hscale : rowCap t * q.stepRow t r cols k i =
      (∑ j ∈ S₁, b j) - (∑ j ∈ S₁, a j) := by
    rw [hrow]
    calc
      rowCap t * (((∑ j ∈ S₁, b j) - (∑ j ∈ S₁, a j)) / rowCap t) =
          (((∑ j ∈ S₁, b j) - (∑ j ∈ S₁, a j)) / rowCap t) * rowCap t := by ring
      _ = (∑ j ∈ S₁, b j) - (∑ j ∈ S₁, a j) := div_mul_cancel₀ _ hcap
  calc
    sequence_row_energy q t r cols i (k + 1) - sequence_row_energy q t r cols i k ≤
        (∑ j ∈ S₁, b j) - (∑ j ∈ S₁, a j) := by
          rw [henergy₁, henergy₀]
          linarith
    _ = rowCap t * q.stepRow t r cols k i := hscale.symm

theorem scalar_records_proof {P : Type*} [Fintype P] [DecidableEq P]
    (q : Sequence P) (t : ℝ) (r : P → ℂ) (cols : Finset P)
    (ht : 0 < t) (hseq : q.wellFormed t r)
    (hu0 : ∀ i ∈ (q.state 0).live, (q.state 0).ambientLag t r i = 0) :
    ∀ i ∈ (q.state q.length).live,
      q.lagRecord t r (Finset.range q.length) i = (q.state q.length).ambientLag t r i ∧
      (∑ j ∈ cols ∩ (q.state q.length).live,
        ‖((q.state q.length).ambient r).h t i j‖ ^ 4) ≤
        (∑ j ∈ cols ∩ (q.state 0).live,
          ‖((q.state 0).ambient r).h t i j‖ ^ 4) +
          rowCap t * q.rowRecord t r cols (Finset.range q.length) i := by
  intro i hi
  constructor
  · have hlag := lag_record_eq_final_sub_initial q t r hseq i hi
    have hsub := final_live_subset q t r hseq
    have hi0 : i ∈ (q.state 0).live := hsub 0 (Nat.zero_le _) hi
    rw [hlag, hu0 i hi0]
    simp
  · let energy := sequence_row_energy q t r cols i
    have htel := sum_range_sub_telescope energy q.length
    have hsteps :
        (∑ k ∈ Finset.range q.length, (energy (k + 1) - energy k)) ≤
          ∑ k ∈ Finset.range q.length, rowCap t * q.stepRow t r cols k i := by
      apply Finset.sum_le_sum
      intro k hk
      exact sequence_row_energy_step_bound q t r cols ht hseq i hi k
        (Finset.mem_range.mp hk)
    have hfactor :
        (∑ k ∈ Finset.range q.length, rowCap t * q.stepRow t r cols k i) =
          rowCap t * q.rowRecord t r cols (Finset.range q.length) i := by
      rw [← Finset.mul_sum]
      simp [Sequence.rowRecord]
    have hbound : energy q.length ≤
        energy 0 + rowCap t * q.rowRecord t r cols (Finset.range q.length) i := by
      calc
        energy q.length = energy 0 + (energy q.length - energy 0) := by ring
        _ = energy 0 + ∑ k ∈ Finset.range q.length, (energy (k + 1) - energy k) := by
          rw [← htel]
        _ ≤ energy 0 +
            ∑ k ∈ Finset.range q.length, rowCap t * q.stepRow t r cols k i := by
          calc
            energy 0 + ∑ k ∈ Finset.range q.length,
                (energy (k + 1) - energy k) =
                (∑ k ∈ Finset.range q.length, (energy (k + 1) - energy k)) + energy 0 := by ring
            _ ≤ (∑ k ∈ Finset.range q.length, rowCap t * q.stepRow t r cols k i) + energy 0 :=
              add_le_add_left hsteps _
            _ = energy 0 +
                ∑ k ∈ Finset.range q.length, rowCap t * q.stepRow t r cols k i := by ring
        _ = energy 0 + rowCap t * q.rowRecord t r cols (Finset.range q.length) i := by
          rw [hfactor]
    simpa [energy, sequence_row_energy] using hbound

private theorem delete_scaled_z_eq {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (x : P) (ξ : ℝ) (ht : 0 < t)
    (hsym : s.g.IsSymm) (hden : 1 + ((ξ : ℂ) + t * s.r x) * s.g x x ≠ 0) :
    ∀ i : survivors x,
      (deleteState t s x ξ).z t i = s.z t i.val - gamma t s x ξ * s.K t i.val x := by
  intro i
  let c : ℂ := (ξ : ℂ) + t * s.r x
  let d : ℂ := 1 + c * s.g x x
  have hd : d ≠ 0 := by simpa [d, c] using hden
  have hα : (Real.sqrt t : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 ht))
  have hsymi : s.g x i.val = s.g i.val x := hsym.apply i.val x
  have hγK : gamma t s x ξ * s.K t i.val x =
      (Real.sqrt t : ℂ) * c * s.g i.val x ^ 2 / d := by
    simp [gamma, State.K, State.h, entrywiseSquare,
      AndersonAC.Blueprint.entrywiseSquare, Matrix.smul_apply, smul_eq_mul, c, d]
    field_simp [hd, hα]
  simp [State.z, State.rawLag, deleteState, hsymi]
  rw [hγK]
  field_simp [hd]
  ring

private theorem delete_A_update {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (x : P) (ξ : ℝ) (ht : 0 < t)
    (ha : 1 - s.K t x x ≠ 0)
    (hden : 1 + ((ξ : ℂ) + t * s.r x) * s.g x x ≠ 0) :
    1 - (deleteState t s x ξ).K t =
      scalarSchur (1 - s.K t) x - restrict (Jinc t s x ξ) (survivors x) := by
  let α : ℂ := (Real.sqrt t : ℂ)
  let c : ℂ := (ξ : ℂ) + t * s.r x
  let d : ℂ := 1 + c * s.g x x
  let a : ℂ := 1 - α ^ 2 * s.g x x ^ 2
  let A : CMat P := 1 - s.K t
  have hα : α ≠ 0 := by
    dsimp [α]
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 ht))
  have hd : d ≠ 0 := by simpa [d, c] using hden
  have hKentry (u v : P) : s.K t u v = α ^ 2 * s.g u v ^ 2 := by
    simp [State.K, State.h, entrywiseSquare, AndersonAC.Blueprint.entrywiseSquare,
      Pi.smul_apply, smul_eq_mul, α]
    ring
  have hh (u v : P) : s.h t u v = α * s.g u v := by
    simp [State.h, Pi.smul_apply, smul_eq_mul, α]
  have hAentry (u v : P) : A u v = (if u = v then 1 else 0) - α ^ 2 * s.g u v ^ 2 := by
    simp [A, Matrix.sub_apply, Matrix.one_apply, hKentry]
  have hAxx : A x x = a := by
    simp [a, hAentry]
  have haA : A x x ≠ 0 := by simpa [A, Matrix.one_apply] using ha
  have ha' : a ≠ 0 := by simpa [hAxx] using haA
  ext i j
  have hix : (i.val : P) ≠ x := by
    simpa [survivors] using i.property
  have hxj : x ≠ (j.val : P) := by
    have hjx : (j.val : P) ≠ x := by simpa [survivors] using j.property
    exact hjx.symm
  let δ : ℂ := if i.val = j.val then 1 else 0
  have hAij : A i.val j.val = δ - α ^ 2 * s.g i.val j.val ^ 2 := by
    simpa [δ] using hAentry i.val j.val
  have hAix : A i.val x = -(α ^ 2 * s.g i.val x ^ 2) := by
    rw [hAentry]
    simp [hix]
  have hAxj : A x j.val = -(α ^ 2 * s.g x j.val ^ 2) := by
    rw [hAentry]
    simp [hxj]
  have hQ : scalarSchur A x i j =
      δ - α ^ 2 * s.g i.val j.val ^ 2 -
        α ^ 4 * s.g i.val x ^ 2 * s.g x j.val ^ 2 / a := by
    unfold scalarSchur
    rw [hAij, hAix, hAxx, hAxj]
    dsimp [δ]
    ring
  have hJ : (restrict (Jinc t s x ξ) (survivors x)) i j =
      -2 * gamma t s x ξ * (α * s.g i.val x) * (α * s.g i.val j.val) *
        (α * s.g x j.val) +
      (gamma t s x ξ ^ 2 - a⁻¹) *
        (α ^ 2 * s.g i.val x ^ 2) * (α ^ 2 * s.g x j.val ^ 2) := by
    change Jinc t s x ξ i.val j.val = _
    simp only [Jinc, pad, i.property, j.property]
    rw [hh i.val x, hh i.val j.val, hh x j.val,
      hKentry i.val x, hKentry x j.val, hKentry x x]
    simp [a]
  have hKnew : (deleteState t s x ξ).K t i j =
      α ^ 2 * (s.g i.val j.val - c * s.g i.val x * s.g x j.val / d) ^ 2 := by
    change ((Real.sqrt t : ℂ) * (deleteState t s x ξ).g i j) ^ 2 = _
    simp [deleteState, α, c, d]
    ring
  have hden' : α * d ≠ 0 := mul_ne_zero hα hd
  calc
    (1 - (deleteState t s x ξ).K t) i j =
        δ - α ^ 2 * (s.g i.val j.val - c * s.g i.val x * s.g x j.val / d) ^ 2 := by
          simp [Matrix.sub_apply, Matrix.one_apply, hKnew, δ]
    _ = (scalarSchur A x i j) - (restrict (Jinc t s x ξ) (survivors x) i j) := by
          rw [hQ, hJ]
          dsimp [gamma, c, d, a, α]
          have hroot : (Real.sqrt t : ℂ) ≠ 0 := by simpa [α] using hα
          have hγden : (Real.sqrt t : ℂ) *
              (1 + ((ξ : ℂ) + t * s.r x) * s.g x x) ≠ 0 := mul_ne_zero hroot hden
          field_simp [hd, ha', hroot, hγden]
          ring
    _ = (scalarSchur A x - restrict (Jinc t s x ξ) (survivors x)) i j := by
          simp [Matrix.sub_apply]

private theorem state_U_apply {P : Type*} [Fintype P] [DecidableEq P]
    (s : State P) (t : ℝ) (i : P) :
    s.U t i = (Real.sqrt t : ℂ) * s.lag t i := by
  have h := congrFun (show s.U t = (Real.sqrt t : ℂ) • s.lag t from by
    ext j
    simp [State.U, State.z, State.lag, State.P, Matrix.mulVec_smul]) i
  simpa [Pi.smul_apply, smul_eq_mul] using h

private theorem pad_mulVec_apply {P : Type*} [Fintype P] [DecidableEq P]
    (S : Finset P) (B : Matrix S S ℂ) (u : P → ℂ) (i : S) :
    (pad S B *ᵥ u) i.val = (B *ᵥ (fun j : S => u j.val)) i := by
  classical
  let f : P → ℂ := fun x => if hx : x ∈ S then B i ⟨x, hx⟩ * u x else 0
  have hsubset : (∑ x ∈ S, f x) = ∑ x : P, f x := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro x hx hxnot
    simp [f, hxnot]
  have hattach : (∑ x ∈ S, f x) = ∑ x ∈ S.attach, f x := by
    exact (Finset.sum_attach (s := S) (f := f)).symm
  calc
    (pad S B *ᵥ u) i.val = ∑ x : P, f x := by
      simp [Matrix.mulVec, dotProduct, pad, f, i.property]
    _ = ∑ x ∈ S, f x := hsubset.symm
    _ = ∑ x ∈ S.attach, f x := hattach
    _ = (B *ᵥ (fun j : S => u j.val)) i := by simp [Matrix.mulVec, dotProduct, f]

theorem lag_exact_proof {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (x : P) (ξ : ℝ) (ht : 0 < t)
    (hsym : s.g.IsSymm) (hA : IsUnit (1 - s.K t))
    (ha : 1 - s.K t x x ≠ 0)
    (hden : 1 + ((ξ : ℂ) + t * s.r x) * s.g x x ≠ 0)
    (hnew : IsUnit (1 - (deleteState t s x ξ).K t)) :
    ∀ (i : P) (hi : i ∈ survivors x),
      (Real.sqrt t : ℂ) * lagInc t s x ξ i =
        ((deleteState t s x ξ).P t *ᵥ (fun j => forcing t s x ξ j)) ⟨i, hi⟩ := by
  intro i hi
  let R : Type _ := (↑(survivors x) : Type _)
  let newS : State R := deleteState t s x ξ
  let oldA : CMat P := 1 - s.K t
  let newA : Matrix R R ℂ := 1 - newS.K t
  let oldU : P → ℂ := s.U t
  let oldZ : P → ℂ := s.z t
  let newU : R → ℂ := newS.U t
  let newZ : R → ℂ := newS.z t
  let oldUR : R → ℂ := fun j => oldU j.val
  let deltaU : R → ℂ := fun j => (Real.sqrt t : ℂ) * lagInc t s x ξ j.val
  have hold_det : IsUnit oldA.det := by
    apply (Matrix.isUnit_iff_isUnit_det oldA).mp
    simpa [oldA] using hA
  have hold_sys : oldA *ᵥ oldU = oldZ := by
    change oldA *ᵥ (oldA⁻¹ *ᵥ oldZ) = oldZ
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv oldA hold_det]
    simp
  have hnew_det : IsUnit newA.det := by
    apply (Matrix.isUnit_iff_isUnit_det newA).mp
    simpa [newA, newS] using hnew
  have hnew_sys : newA *ᵥ newU = newZ := by
    change newA *ᵥ (newA⁻¹ *ᵥ newZ) = newZ
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv newA hnew_det]
    simp
  have haA : oldA x x ≠ 0 := by simpa [oldA, Matrix.one_apply] using ha
  have hschur := scalarSchur_mulVec_eq oldA x oldU oldZ hold_sys haA
  have hAupdate : newA = scalarSchur oldA x - restrict (Jinc t s x ξ) (survivors x) := by
    change 1 - (deleteState t s x ξ).K t =
      scalarSchur (1 - s.K t) x - restrict (Jinc t s x ξ) (survivors x)
    exact delete_A_update t s x ξ ht ha hden
  have hdelta : deltaU = newU - oldUR := by
    funext j
    have hlag : lagInc t s x ξ j.val = newS.lag t j - s.lag t j.val := by
      simp [lagInc, newS, j.property]
    change (Real.sqrt t : ℂ) * lagInc t s x ξ j.val = _
    rw [hlag]
    have hnewU := state_U_apply newS t j
    have holdU := state_U_apply s t j.val
    calc
      (Real.sqrt t : ℂ) * (newS.lag t j - s.lag t j.val) =
          (Real.sqrt t : ℂ) * newS.lag t j - (Real.sqrt t : ℂ) * s.lag t j.val := by ring
      _ = newU j - oldUR j := by
        rw [← hnewU, ← holdU]
  have hZupdate : ∀ j : R,
      newZ j = oldZ j.val - gamma t s x ξ * s.K t j.val x := by
    intro j
    simpa [newZ, oldZ, newS] using
      delete_scaled_z_eq t s x ξ ht hsym hden j
  have hArow : ∀ j : R, oldA j.val x = -s.K t j.val x := by
    intro j
    have hjx : j.val ≠ x := by simpa [survivors] using j.property
    simp [oldA, Matrix.sub_apply, Matrix.one_apply, hjx]
  let JB : Matrix (survivors x) (survivors x) ℂ := fun a b =>
    -2 * gamma t s x ξ * s.h t a.val x * s.h t a.val b.val * s.h t x b.val +
      ((gamma t s x ξ) ^ 2 - (1 - s.K t x x)⁻¹) *
        s.K t a.val x * s.K t x b.val
  have hJdef : Jinc t s x ξ = pad (survivors x) JB := rfl
  have hJrestrict : restrict (Jinc t s x ξ) (survivors x) = JB := by
    rw [hJdef]
    ext a b
    simp [restrict, pad]
  have hJfull : ∀ j : R,
      (restrict (Jinc t s x ξ) (survivors x) *ᵥ oldUR) j =
        (Jinc t s x ξ *ᵥ oldU) j.val := by
    intro j
    rw [hJrestrict, hJdef]
    exact (pad_mulVec_apply (survivors x) JB oldU j).symm
  have hEq : newA *ᵥ deltaU = fun j => forcing t s x ξ j.val := by
    funext j
    calc
      (newA *ᵥ deltaU) j = (newA *ᵥ (newU - oldUR)) j := by rw [hdelta]
      _ = (newA *ᵥ newU) j - (newA *ᵥ oldUR) j := by
        rw [Matrix.mulVec_sub]
        rfl
      _ = newZ j - ((scalarSchur oldA x - restrict (Jinc t s x ξ) (survivors x)) *ᵥ oldUR) j := by
        rw [hnew_sys, hAupdate]
      _ = newZ j - (scalarSchur oldA x *ᵥ oldUR) j +
          (restrict (Jinc t s x ξ) (survivors x) *ᵥ oldUR) j := by
        rw [Matrix.sub_mulVec]
        simp only [Pi.sub_apply]
        abel
      _ = forcing t s x ξ j.val := by
        have hjx : j.val ≠ x := by simpa [survivors] using j.property
        rw [hZupdate j, hschur j, hJfull j, hArow j]
        simp [forcing, oldZ, oldA, oldU, Matrix.one_apply, hjx]
        ring
  have hnewinv : newA⁻¹ * newA = 1 := Matrix.nonsing_inv_mul newA hnew_det
  have hpoint : deltaU ⟨i, hi⟩ =
      (newA⁻¹ *ᵥ (fun j => forcing t s x ξ j.val)) ⟨i, hi⟩ := by
    calc
      deltaU ⟨i, hi⟩ = ((newA⁻¹ * newA) *ᵥ deltaU) ⟨i, hi⟩ := by rw [hnewinv]; simp
      _ = (newA⁻¹ *ᵥ (newA *ᵥ deltaU)) ⟨i, hi⟩ := by rw [← Matrix.mulVec_mulVec]
      _ = (newA⁻¹ *ᵥ (fun j => forcing t s x ξ j.val)) ⟨i, hi⟩ := by rw [hEq]
  simpa [deltaU, newA, newS, State.P] using hpoint

end AndersonAC.AgentS45
