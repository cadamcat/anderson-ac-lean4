import AndersonAC.AgentS78.Construction.TileStartDecay
import AndersonAC.AgentS78.Construction.SweepEndDecay
import AndersonAC.S45.LocalityProof
import AndersonAC.S45.GammaProof
import AndersonAC.S78Moment.Geometry

/-!
# the active-block Combes--Thomas estimate

Transport the torus active block to a finite-index graph, apply the proved S45 locality
estimate, and transfer its collapsed-distance bounds back to the physical torus metric.
-/

noncomputable section
set_option autoImplicit false

open scoped BigOperators

namespace AndersonAC.AgentS78

open AndersonAC.S78
open Classical

private theorem nn_adj_iff_ct {d m : ℕ} (x y : Torus d m) :
    (nnGraph d m).Adj x y ↔ x ≠ y ∧
      ∃ i : Fin d, y = x + OAI.Anderson.torusBasisVector i ∨
        y = x - OAI.Anderson.torusBasisVector i := by
  unfold nnGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · obtain ⟨i, hi | hi⟩ := h
      · exact ⟨hne, i, Or.inr (by rw [hi]; abel)⟩
      · exact ⟨hne, i, Or.inl (by rw [hi]; abel)⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩

private noncomputable def torusFinEquiv (d m : ℕ) :
    Torus d m ≃ Fin (Fintype.card (Torus d m)) := Fintype.equivFin _

private def ctGraph (d m : ℕ) : SimpleGraph (Fin (Fintype.card (Torus d m))) :=
  (nnGraph d m).comap (torusFinEquiv d m).symm

private theorem ctGraph_connected (d m : ℕ) : (ctGraph d m).Connected := by
  classical
  let e := torusFinEquiv d m
  have hconn := AndersonAC.SolS78.nnGraph_connected_proof (d := d) (m := m)
  let f : nnGraph d m →g ctGraph d m :=
    { toFun := e
      map_rel' := by
        intro u v huv
        simpa [ctGraph, e] using huv }
  refine { preconnected := ?_, nonempty := ⟨e 0⟩ }
  intro i j
  have w := hconn.preconnected (e.symm i) (e.symm j)
  simpa [f, e] using w.map f

private theorem ctGraph_degree (d m : ℕ) (i : Fin (Fintype.card (Torus d m))) :
    (Finset.univ.filter ((ctGraph d m).Adj i)).card ≤ 2 * d := by
  classical
  let e := torusFinEquiv d m
  let f : Fin d × Bool → Fin (Fintype.card (Torus d m)) := fun p =>
    e (if p.2 then e.symm i + OAI.Anderson.torusBasisVector p.1
      else e.symm i - OAI.Anderson.torusBasisVector p.1)
  have hsub : (Finset.univ.filter ((ctGraph d m).Adj i)) ⊆
      Finset.univ.image f := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hadj : (nnGraph d m).Adj (e.symm i) (e.symm j) := by
      simpa [ctGraph, e] using hj
    obtain ⟨-, k, hk | hk⟩ := (nn_adj_iff_ct (e.symm i) (e.symm j)).1 hadj
    · apply Finset.mem_image.mpr
      refine ⟨(k, true), Finset.mem_univ _, ?_⟩
      have hjEq : e (e.symm i + OAI.Anderson.torusBasisVector k) = j := by
        calc
          e (e.symm i + OAI.Anderson.torusBasisVector k) = e (e.symm j) :=
            congrArg e hk.symm
          _ = j := e.apply_symm_apply j
      simpa [f] using hjEq
    · apply Finset.mem_image.mpr
      refine ⟨(k, false), Finset.mem_univ _, ?_⟩
      have hjEq : e (e.symm i - OAI.Anderson.torusBasisVector k) = j := by
        calc
          e (e.symm i - OAI.Anderson.torusBasisVector k) = e (e.symm j) :=
            congrArg e hk.symm
          _ = j := e.apply_symm_apply j
      simpa [f] using hjEq
  calc
    (Finset.univ.filter ((ctGraph d m).Adj i)).card ≤
        (Finset.univ.image f).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin d × Bool)).card := Finset.card_image_le
    _ = 2 * d := by simp [Fintype.card_prod]; omega

private noncomputable def ctGeometry (d m : ℕ) :
    AndersonAC.S45.FiniteGeometry (Fin (Fintype.card (Torus d m))) d := by
  classical
  exact
    { graph := ctGraph d m
      decidable := inferInstance
      connected := ctGraph_connected d m
      degree := ctGraph_degree d m }

private def ctFinset {I : Type*} [Fintype I] [DecidableEq I]
    (e : I ≃ Fin (Fintype.card I)) (A : Finset I) :
    Finset (Fin (Fintype.card I)) :=
  Finset.univ.filter fun i => e.symm i ∈ A

private def ctActiveEquiv {I : Type*} [Fintype I] [DecidableEq I]
    (e : I ≃ Fin (Fintype.card I)) (A : Finset I) :
    A ≃ ctFinset e A where
  toFun a := ⟨e a.val, by simp [ctFinset, a.property]⟩
  invFun b := ⟨e.symm b.val, by simpa [ctFinset] using b.property⟩
  left_inv a := by apply Subtype.ext; simp
  right_inv b := by apply Subtype.ext; simp

private def ctTerminalEquiv {I : Type*} [Fintype I] [DecidableEq I]
    (e : I ≃ Fin (Fintype.card I)) (A : Finset I) :
    (↑(Aᶜ) : Type _) ≃ (↑((ctFinset e A)ᶜ) : Type _) where
  toFun a := ⟨e a.val, by
    apply Finset.mem_compl.mpr
    intro hmem
    have hA := (Finset.mem_filter.mp hmem).2
    exact (Finset.mem_compl.mp a.property) (by simpa using hA)⟩
  invFun b := ⟨e.symm b.val, by
    apply Finset.mem_compl.mpr
    intro hA
    have hmem : b.val ∈ ctFinset e A :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hA⟩
    exact (Finset.mem_compl.mp b.property) hmem⟩
  left_inv a := by apply Subtype.ext; simp
  right_inv b := by apply Subtype.ext; simp

private theorem s78_pathCost_support_eq_walkCost {I : Type} [DecidableEq I]
    (G : SimpleGraph I) (T : Finset I) {i j : I} (w : G.Walk i j) :
    AndersonAC.S78.pathCost T w.support = AndersonAC.S45.walkCost G T w := by
  induction w with
  | nil => simp [AndersonAC.S78.pathCost, AndersonAC.S45.walkCost]
  | @cons a b c hab w ih =>
      have hrec : AndersonAC.S78.pathCost T (a :: w.support) =
          (if a ∈ T ∨ b ∈ T then 0 else 1) +
            AndersonAC.S78.pathCost T w.support := by
        cases w with
        | nil => simp [AndersonAC.S78.pathCost]
        | @cons b c d h w' =>
            simp [AndersonAC.S78.pathCost]
      rw [SimpleGraph.Walk.support_cons, hrec, AndersonAC.S45.walkCost, ih]

private def ctGraphHom (d m : ℕ) : ctGraph d m →g nnGraph d m :=
  { toFun := (torusFinEquiv d m).symm
    map_rel' := by
      intro u v huv
      simpa [ctGraph] using huv }

private theorem walkCost_ctMap {d m : ℕ} (A : Finset (Torus d m))
    {i j : Fin (Fintype.card (Torus d m))}
    (w : (ctGraph d m).Walk i j) :
    AndersonAC.S45.walkCost (ctGraph d m) ((ctFinset (torusFinEquiv d m) A)ᶜ) w =
      AndersonAC.S45.walkCost (nnGraph d m) Aᶜ (w.map (ctGraphHom d m)) := by
  classical
  induction w with
  | nil => simp [AndersonAC.S45.walkCost]
  | @cons u v z huv p ih =>
      have hu : u ∉ ctFinset (torusFinEquiv d m) A ↔
          (torusFinEquiv d m).symm u ∉ A := by simp [ctFinset]
      have hv : v ∉ ctFinset (torusFinEquiv d m) A ↔
          (torusFinEquiv d m).symm v ∉ A := by simp [ctFinset]
      simp [AndersonAC.S45.walkCost, ih, hu, hv, ctGraphHom]

private theorem terminal_le_collapsed_ct {d m : ℕ} (A : Finset (Torus d m))
    (i j : Fin (Fintype.card (Torus d m))) :
    (terminalDistance (nnGraph d m) Aᶜ
        ((torusFinEquiv d m).symm i) ((torusFinEquiv d m).symm j) : ℝ) ≤
      AndersonAC.S45.collapsedDistance (ctGraph d m)
        (ctFinset (torusFinEquiv d m) A)ᶜ i j := by
  classical
  let G := ctGraph d m
  let e := torusFinEquiv d m
  have hset : {a : ℝ | ∃ w : G.Walk i j,
      a = (AndersonAC.S45.walkCost G ((ctFinset e A)ᶜ) w : ℝ)}.Nonempty := by
    rcases (ctGraph_connected d m).preconnected i j with ⟨w⟩
    exact ⟨(AndersonAC.S45.walkCost G ((ctFinset e A)ᶜ) w : ℝ), w, rfl⟩
  unfold AndersonAC.S45.collapsedDistance
  apply le_csInf hset
  intro a ha
  rcases ha with ⟨w, rfl⟩
  let wt := w.map (ctGraphHom d m)
  have hhead : wt.support.head? = some (e.symm i) := by
    rw [List.head?_eq_some_head (SimpleGraph.Walk.support_ne_nil wt)]
    simp [wt, SimpleGraph.Walk.head_support, ctGraphHom, e]
  have hlast : wt.support.getLast? = some (e.symm j) := by
    rw [List.getLast?_eq_getLast_of_ne_nil (SimpleGraph.Walk.support_ne_nil wt)]
    simp [wt, SimpleGraph.Walk.getLast_support, ctGraphHom, e]
  have hpath : wt.support.IsChain (nnGraph d m).Adj :=
    SimpleGraph.Walk.isChain_adj_support wt
  have hcost : AndersonAC.S78.pathCost Aᶜ wt.support =
      AndersonAC.S45.walkCost G ((ctFinset e A)ᶜ) w := by
    calc
      AndersonAC.S78.pathCost Aᶜ wt.support =
          AndersonAC.S45.walkCost (nnGraph d m) Aᶜ wt :=
        s78_pathCost_support_eq_walkCost (nnGraph d m) Aᶜ wt
      _ = AndersonAC.S45.walkCost G ((ctFinset e A)ᶜ) w :=
        (walkCost_ctMap A w).symm
  have hnat : terminalDistance (nnGraph d m) Aᶜ (e.symm i) (e.symm j) ≤
      AndersonAC.S78.pathCost Aᶜ wt.support := by
    unfold terminalDistance
    have hNat :
        sInf {n : ℕ | ∃ xs : List (Torus d m),
          xs.IsChain (nnGraph d m).Adj ∧ xs.head? = some (e.symm i) ∧
            xs.getLast? = some (e.symm j) ∧ AndersonAC.S78.pathCost Aᶜ xs = n} ≤
          AndersonAC.S78.pathCost Aᶜ wt.support := by
      apply Nat.sInf_le
      exact ⟨wt.support, hpath, hhead, hlast, rfl⟩
    exact_mod_cast hNat
  rw [hcost] at hnat
  exact_mod_cast hnat

private theorem ct_map_ringInverse (x : ℝ) :
    (algebraMap ℝ ℂ) (Ring.inverse x) = Ring.inverse ((algebraMap ℝ ℂ) x) := by
  simp only [Ring.inverse_eq_inv, map_inv₀]

private theorem ct_realMatrix_map_inv {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℝ) :
    (M.map (algebraMap ℝ ℂ))⁻¹ = (M⁻¹).map (algebraMap ℝ ℂ) := by
  change ((algebraMap ℝ ℂ).mapMatrix M)⁻¹ =
    (algebraMap ℝ ℂ).mapMatrix (M⁻¹)
  rw [Matrix.inv_def, Matrix.inv_def,
    ← RingHom.map_det (algebraMap ℝ ℂ) M,
    ← RingHom.map_adjugate (algebraMap ℝ ℂ) M]
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply,
    smul_eq_mul, RingHom.map_mul]
  rw [← ct_map_ringInverse]

private theorem ct_matrix_inv_smul {I : Type*} [Fintype I] [DecidableEq I]
    (c : ℝ) (hc : c ≠ 0) (M : Matrix I I ℝ) :
    (c • M)⁻¹ = c⁻¹ • M⁻¹ := by
  by_cases hM : IsUnit M.det
  · letI : Invertible c := invertibleOfNonzero hc
    simpa [invertibleOfNonzero] using (Matrix.inv_smul (A := M) c hM)
  · have hdet0 : M.det = 0 := by
      by_contra hn
      exact hM (isUnit_iff_ne_zero.mpr hn)
    have hcM : ¬ IsUnit (c • M).det := by
      rw [Matrix.det_smul, hdet0, mul_zero]
      exact not_isUnit_zero
    rw [Matrix.nonsing_inv_apply_not_isUnit (A := M) hM,
      Matrix.nonsing_inv_apply_not_isUnit (A := c • M) hcM]
    simp

private theorem ct_terminalSchur_smul {I : Type*} [Fintype I] [DecidableEq I]
    (c : ℝ) (hc : c ≠ 0) (H : Matrix I I ℝ) (A : Finset I) :
    AndersonAC.S45.terminalSchur (c • H) A =
      c • AndersonAC.S45.terminalSchur H A := by
  classical
  have hAA : AndersonAC.S45.restrict (c • H) A =
      c • AndersonAC.S45.restrict H A := by
    ext i j
    simp [AndersonAC.S45.restrict, Matrix.smul_apply]
  have hAC : (c • H).submatrix (Subtype.val : A → I)
      (Subtype.val : (↑(Aᶜ) : Type _) → I) =
      c • H.submatrix (Subtype.val : A → I) (Subtype.val : (↑(Aᶜ) : Type _) → I) := by
    ext i j
    simp [Matrix.smul_apply]
  have hCC : AndersonAC.S45.restrict (c • H) Aᶜ =
      c • AndersonAC.S45.restrict H Aᶜ := by
    ext i j
    simp [AndersonAC.S45.restrict, Matrix.smul_apply]
  have hCA : (c • H).submatrix (Subtype.val : (↑(Aᶜ) : Type _) → I)
      (Subtype.val : A → I) =
      c • H.submatrix (Subtype.val : (↑(Aᶜ) : Type _) → I) (Subtype.val : A → I) := by
    ext i j
    simp [Matrix.smul_apply]
  rw [AndersonAC.S45.terminalSchur, AndersonAC.S45.terminalSchur,
    hAA, hAC, hCC, hCA, ct_matrix_inv_smul c hc]
  let X := H.submatrix (Subtype.val : A → I) (Subtype.val : (↑(Aᶜ) : Type _) → I)
  let T := (AndersonAC.S45.restrict H Aᶜ)⁻¹
  let Y := H.submatrix (Subtype.val : (↑(Aᶜ) : Type _) → I) (Subtype.val : A → I)
  have hfirst : (c • X) * (c⁻¹ • T) = X * T := by
    calc
      (c • X) * (c⁻¹ • T) = c • (X * (c⁻¹ • T)) := Matrix.smul_mul _ _ _
      _ = c • (c⁻¹ • (X * T)) := by rw [Matrix.mul_smul]
      _ = (c * c⁻¹) • (X * T) := by rw [smul_smul]
      _ = X * T := by rw [mul_inv_cancel₀ hc, one_smul]
  change c • AndersonAC.S45.restrict H A -
      (c • X) * (c⁻¹ • T) * (c • Y) =
    c • (AndersonAC.S45.restrict H A - X * T * Y)
  rw [hfirst]
  rw [Matrix.mul_smul]
  rw [smul_sub]

private theorem ct_terminalSchur_add_activeDiag {I : Type*} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℝ) (A : Finset I) (D : I → ℝ) :
    AndersonAC.S45.terminalSchur
        (H + Matrix.diagonal (fun i => if i ∈ A then D i else 0)) A =
      AndersonAC.S45.terminalSchur H A +
        Matrix.diagonal (fun i : A => D i.val) := by
  classical
  let H' := H + Matrix.diagonal (fun i => if i ∈ A then D i else 0)
  have hAA : AndersonAC.S45.restrict H' A =
      AndersonAC.S45.restrict H A + Matrix.diagonal (fun i : A => D i.val) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [H', AndersonAC.S45.restrict, Matrix.diagonal_apply, i.property]
    · simp [H', AndersonAC.S45.restrict, Matrix.diagonal_apply, hij]
  have hAC : H'.submatrix (Subtype.val : A → I)
        (Subtype.val : (↑(Aᶜ) : Type _) → I) =
      H.submatrix (Subtype.val : A → I) (Subtype.val : (↑(Aᶜ) : Type _) → I) := by
    ext i j
    have hne : i.val ≠ j.val := by
      intro h
      apply (Finset.mem_compl.mp j.property)
      rw [← h]
      exact i.property
    simp [H', Matrix.diagonal_apply, hne]
  have hCC : AndersonAC.S45.restrict H' Aᶜ =
      AndersonAC.S45.restrict H Aᶜ := by
    ext i j
    simp [H', AndersonAC.S45.restrict, Matrix.diagonal_apply,
      Finset.mem_compl.mp i.property]
  have hCA : H'.submatrix (Subtype.val : (↑(Aᶜ) : Type _) → I)
        (Subtype.val : A → I) =
      H.submatrix (Subtype.val : (↑(Aᶜ) : Type _) → I) (Subtype.val : A → I) := by
    ext i j
    have hne : i.val ≠ j.val := by
      intro h
      apply (Finset.mem_compl.mp i.property)
      rw [h]
      exact j.property
    simp [H', Matrix.diagonal_apply, hne]
  rw [show AndersonAC.S45.terminalSchur H' A = _ by
    rw [AndersonAC.S45.terminalSchur, hAA, hAC, hCC, hCA]]
  rw [AndersonAC.S45.terminalSchur]
  noncomm_ring

private def ctComplexTerminalEquiv {I : Type} [Fintype I] [DecidableEq I]
    (A : Finset I) : (↑(Aᶜ) : Type _) ≃ {i : I // i ∉ A} where
  toFun i := ⟨i.val, Finset.mem_compl.mp i.property⟩
  invFun i := ⟨i.val, Finset.mem_compl.mpr i.property⟩
  left_inv i := by apply Subtype.ext; rfl
  right_inv i := by apply Subtype.ext; rfl

private theorem ct_terminalSchur_map {I : Type} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℝ) (A : Finset I) :
    (AndersonAC.S45.terminalSchur H A).map (algebraMap ℝ ℂ) =
      AndersonAC.SolS78.activeSchur (H.map (algebraMap ℝ ℂ)) A := by
  classical
  let f := algebraMap ℝ ℂ
  let eT := ctComplexTerminalEquiv A
  let Xr := H.submatrix (Subtype.val : A → I)
    (Subtype.val : (↑(Aᶜ) : Type _) → I)
  let Tr := AndersonAC.S45.restrict H Aᶜ
  let Yr := H.submatrix (Subtype.val : (↑(Aᶜ) : Type _) → I)
    (Subtype.val : A → I)
  let Xc := (H.map f).submatrix (Subtype.val : A → I)
    (Subtype.val : {i : I // i ∉ A} → I)
  let Tc := (H.map f).submatrix (Subtype.val : {i : I // i ∉ A} → I)
    (Subtype.val : {i : I // i ∉ A} → I)
  let Yc := (H.map f).submatrix (Subtype.val : {i : I // i ∉ A} → I)
    (Subtype.val : A → I)
  have hX : Xc = Matrix.reindex (Equiv.refl A) eT (Xr.map f) := by
    ext i j
    rfl
  have hT : Tc = Matrix.reindex eT eT (Tr.map f) := by
    ext i j
    rfl
  have hY : Yc = Matrix.reindex eT (Equiv.refl A) (Yr.map f) := by
    ext i j
    rfl
  have hTinv : Tc⁻¹ = Matrix.reindex eT eT ((Tr⁻¹).map f) := by
    rw [hT, Matrix.inv_reindex]
    simpa [f] using congrArg (Matrix.reindex eT eT) (ct_realMatrix_map_inv Tr)
  have hprod : Xc * Tc⁻¹ * Yc = (Xr * Tr⁻¹ * Yr).map f := by
    rw [hX, hTinv, hY]
    change (Xr.map f).submatrix (Equiv.refl A).symm eT.symm *
        ((Tr⁻¹).map f).submatrix eT.symm eT.symm *
        (Yr.map f).submatrix eT.symm (Equiv.refl A).symm =
      (Xr * Tr⁻¹ * Yr).map f
    calc
      _ = ((Xr.map f).submatrix (Equiv.refl A).symm eT.symm *
          ((Tr⁻¹).map f).submatrix eT.symm eT.symm) *
          (Yr.map f).submatrix eT.symm (Equiv.refl A).symm := by
        rw [Matrix.mul_assoc]
      _ = ((Xr.map f * (Tr⁻¹).map f).submatrix
          (Equiv.refl A).symm eT.symm) *
          (Yr.map f).submatrix eT.symm (Equiv.refl A).symm := by
        rw [Matrix.submatrix_mul_equiv]
      _ = ((Xr.map f * (Tr⁻¹).map f) * (Yr.map f)).submatrix
          (Equiv.refl A).symm (Equiv.refl A).symm := by
        rw [Matrix.submatrix_mul_equiv]
      _ = (Xr * Tr⁻¹ * Yr).map f := by
        change (Xr.map f * (Tr⁻¹).map f * Yr.map f) =
          (Xr * Tr⁻¹ * Yr).map f
        rw [Matrix.map_mul, Matrix.map_mul]
  change (AndersonAC.S45.restrict H A - Xr * Tr⁻¹ * Yr).map f =
      (H.map f).submatrix (Subtype.val : A → I) (Subtype.val : A → I) -
        Xc * Tc⁻¹ * Yc
  have hmapSub : (AndersonAC.S45.restrict H A).map f =
      (H.map f).submatrix (Subtype.val : A → I) (Subtype.val : A → I) := by
    rw [AndersonAC.S45.restrict, ← Matrix.submatrix_map]
  have hmapSub' : (AndersonAC.S45.restrict H A - Xr * Tr⁻¹ * Yr).map f =
      (AndersonAC.S45.restrict H A).map f - (Xr * Tr⁻¹ * Yr).map f := by
    exact Matrix.map_sub f (by intro a b; simp) _ _
  rw [hmapSub', hprod, hmapSub]

private def ctHoppingCount (d m : ℕ) (x y : Torus d m) : ℝ :=
  ∑ k : Fin d, ((if y = x + OAI.Anderson.torusBasisVector k then 1 else 0) +
      (if y = x - OAI.Anderson.torusBasisVector k then 1 else 0))

private theorem ctHoppingCount_complex {d m : ℕ} (x y : Torus d m) :
    (ctHoppingCount d m x y : ℂ) =
      ∑ k : Fin d,
        ((if y = x + OAI.Anderson.torusBasisVector k then 1 else 0) +
          (if y = x - OAI.Anderson.torusBasisVector k then 1 else 0)) := by
  unfold ctHoppingCount
  norm_cast

private theorem ctHoppingCount_symm {d m : ℕ} (x y : Torus d m) :
    ctHoppingCount d m x y = ctHoppingCount d m y x := by
  have hplus (k : Fin d) :
      (y = x + OAI.Anderson.torusBasisVector k) ↔
        (x = y - OAI.Anderson.torusBasisVector k) := by
    constructor <;> intro h <;> rw [h] <;> abel
  have hminus (k : Fin d) :
      (y = x - OAI.Anderson.torusBasisVector k) ↔
        (x = y + OAI.Anderson.torusBasisVector k) := by
    constructor <;> intro h <;> rw [h] <;> abel
  unfold ctHoppingCount
  simp only [hplus, hminus]
  congr 1
  funext k
  ring

private def ctBaseReal {d m : ℕ} (E : ℝ) (x : RunRecord d m) :
    Matrix (Torus d m) (Torus d m) ℝ := fun i j =>
      -ctHoppingCount d m i j + if i = j then x.installed i - E else 0

private theorem installedShifted_eq_ctBaseReal_map {d m : ℕ} (E : ℝ)
    (x : RunRecord d m) :
    installedShifted E x = (ctBaseReal E x).map (algebraMap ℝ ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [installedShifted, zeroConfig, ctBaseReal,
      OAI.Anderson.periodicHamiltonian, Matrix.diagonal_apply,
      Matrix.one_apply, ctHoppingCount_complex]
    <;> ring_nf
  · simp [installedShifted, zeroConfig, ctBaseReal,
      OAI.Anderson.periodicHamiltonian, Matrix.diagonal_apply,
      Matrix.one_apply, ctHoppingCount_complex, hij]
    <;> ring_nf

private theorem ctBaseReal_isSymm {d m : ℕ} (E : ℝ) (x : RunRecord d m) :
    (ctBaseReal E x).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [ctBaseReal, Matrix.sub_apply]
  rw [ctHoppingCount_symm]
  by_cases h : i = j <;> simp [h, eq_comm]

private def ctActiveDiagonal {d m : ℕ} (A : Finset (Torus d m))
    (D : Torus d m → ℝ) : Matrix (Torus d m) (Torus d m) ℝ :=
  Matrix.diagonal (fun i => if i ∈ A then D i else 0)

private def ctRealShift {d m : ℕ} (E : ℝ) (x : RunRecord d m)
    (A : Finset (Torus d m)) (D : Torus d m → ℝ) :
    Matrix (Torus d m) (Torus d m) ℝ := ctBaseReal E x + ctActiveDiagonal A D

private def ctScale (d : ℕ) : ℝ := 2 * (d : ℝ) + 1

private def ctScaledReal {d m : ℕ} (E : ℝ) (x : RunRecord d m)
    (A : Finset (Torus d m)) (D : Torus d m → ℝ) :
    Matrix (Torus d m) (Torus d m) ℝ := (ctScale d)⁻¹ • ctRealShift E x A D

private theorem ctHoppingCount_bounds {d m : ℕ} (x y : Torus d m) :
    0 ≤ ctHoppingCount d m x y ∧ ctHoppingCount d m x y ≤ ctScale d := by
  unfold ctHoppingCount ctScale
  constructor
  · positivity
  · calc
      (∑ k : Fin d,
          ((if y = x + OAI.Anderson.torusBasisVector k then 1 else 0) +
            (if y = x - OAI.Anderson.torusBasisVector k then 1 else 0)))
          ≤ ∑ _k : Fin d, (2 : ℝ) := by
            apply Finset.sum_le_sum
            intro k hk
            split_ifs <;> norm_num
      _ = 2 * (d : ℝ) := by simp [mul_comm]
      _ ≤ ctScale d := by dsimp [ctScale]; linarith

private theorem ctHoppingCount_zero_of_nonadj {d m : ℕ} (x y : Torus d m)
    (hne : x ≠ y) (hadj : ¬(nnGraph d m).Adj x y) :
    ctHoppingCount d m x y = 0 := by
  have hplus (k : Fin d) : y ≠ x + OAI.Anderson.torusBasisVector k := by
    intro h
    apply hadj
    exact (nn_adj_iff_ct x y).2 ⟨hne, k, Or.inl h⟩
  have hminus (k : Fin d) : y ≠ x - OAI.Anderson.torusBasisVector k := by
    intro h
    apply hadj
    exact (nn_adj_iff_ct x y).2 ⟨hne, k, Or.inr h⟩
  unfold ctHoppingCount
  simp [hplus, hminus]

private theorem ctRealShift_isSymm {d m : ℕ} (E : ℝ) (x : RunRecord d m)
    (A : Finset (Torus d m)) (D : Torus d m → ℝ) :
    (ctRealShift E x A D).IsSymm := by
  have hbase := ctBaseReal_isSymm E x
  have hdiag : (ctActiveDiagonal A D).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    by_cases h : i = j
    · subst j
      simp [ctActiveDiagonal, Matrix.diagonal_apply]
    · simp [ctActiveDiagonal, Matrix.diagonal_apply, h, eq_comm]
  exact hbase.add hdiag

private def ctFinRealMatrix {d m : ℕ} (E : ℝ) (x : RunRecord d m)
    (D : Torus d m → ℝ) :
    Matrix (Fin (Fintype.card (Torus d m))) (Fin (Fintype.card (Torus d m))) ℝ :=
  Matrix.reindex (torusFinEquiv d m) (torusFinEquiv d m)
    (ctScaledReal E x x.endpoint.active D)

private theorem ctFinRealMatrix_isSymm {d m : ℕ} (E : ℝ) (x : RunRecord d m)
    (D : Torus d m → ℝ) : (ctFinRealMatrix E x D).IsSymm := by
  unfold ctFinRealMatrix
  exact ((ctRealShift_isSymm E x x.endpoint.active D).smul ((ctScale d)⁻¹)).reindex
    (torusFinEquiv d m)

private theorem ctFinHop_bounds {d m : ℕ} (E : ℝ) (x : RunRecord d m)
    (A : Finset (Torus d m)) (D : Torus d m → ℝ) :
    ∀ i j : Fin (Fintype.card (Torus d m)), i ≠ j →
      ((ctGraph d m).Adj i j →
        |(ctFinRealMatrix E x D) i j| ≤ 1) ∧
      (¬(ctGraph d m).Adj i j → (ctFinRealMatrix E x D) i j = 0) := by
  classical
  intro i j hij
  let e := torusFinEquiv d m
  have hne : e.symm i ≠ e.symm j := by
    intro h
    apply hij
    simpa using congrArg e h
  have hentry : (ctFinRealMatrix E x D) i j =
      (ctScale d)⁻¹ * (-ctHoppingCount d m (e.symm i) (e.symm j)) := by
    simp [ctFinRealMatrix, Matrix.reindex_apply, ctScaledReal, ctRealShift,
      ctBaseReal, ctActiveDiagonal, ctHoppingCount, hne, hij, e]
  have hK : 0 < ctScale d := by
    dsimp [ctScale]
    positivity
  have hb := ctHoppingCount_bounds (d := d) (m := m) (e.symm i) (e.symm j)
  constructor
  · intro _hadj
    rw [hentry]
    have hAbs : |(ctScale d)⁻¹ * (-ctHoppingCount d m (e.symm i) (e.symm j))| =
        (ctScale d)⁻¹ * ctHoppingCount d m (e.symm i) (e.symm j) := by
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hK.le), abs_neg,
        abs_of_nonneg hb.1]
    rw [hAbs]
    calc
      (ctScale d)⁻¹ * ctHoppingCount d m (e.symm i) (e.symm j) ≤
          (ctScale d)⁻¹ * ctScale d :=
        mul_le_mul_of_nonneg_left hb.2 (inv_nonneg.mpr hK.le)
      _ = 1 := by field_simp [ne_of_gt hK]
  · intro hnon
    rw [hentry]
    have hnot : ¬(nnGraph d m).Adj (e.symm i) (e.symm j) := by
      intro hadj
      apply hnon
      simpa [ctGraph, e] using hadj
    rw [ctHoppingCount_zero_of_nonadj (e.symm i) (e.symm j) hne hnot]
    simp

private def ctReplaceTerminalBlock {I : Type*} [DecidableEq I]
    (H : Matrix I I ℝ) (A : Finset I) : Matrix I I ℝ := fun i j =>
  if hi : i ∈ A then if hj : j ∈ A then H i j else 0
  else if hj : j ∈ A then 0 else if i = j then 1 else 0

private theorem ctReplaceTerminalBlock_isSymm {I : Type*} [DecidableEq I]
    (H : Matrix I I ℝ) (A : Finset I) (hH : H.IsSymm) :
    (ctReplaceTerminalBlock H A).IsSymm := by
  classical
  apply Matrix.IsSymm.ext
  intro i j
  by_cases hi : i ∈ A
  · by_cases hj : j ∈ A
    · simp [ctReplaceTerminalBlock, hi, hj, hH.apply]
    · simp [ctReplaceTerminalBlock, hi, hj]
  · by_cases hj : j ∈ A
    · simp [ctReplaceTerminalBlock, hi, hj]
    · simp [ctReplaceTerminalBlock, hi, hj, eq_comm]

private theorem ctReplaceTerminalBlock_terminal_eq_one {I : Type*} [Fintype I]
    [DecidableEq I] (H : Matrix I I ℝ) (A : Finset I) :
    AndersonAC.S45.restrict (ctReplaceTerminalBlock H A) Aᶜ = 1 := by
  classical
  ext i j
  change ctReplaceTerminalBlock H A i.val j.val =
    (if i = j then (1 : ℝ) else 0)
  by_cases hij : i = j
  · subst j
    simp [ctReplaceTerminalBlock, Finset.mem_compl.mp i.property]
  · have hne : i.val ≠ j.val := by
      intro h
      exact hij (Subtype.ext h)
    simp [ctReplaceTerminalBlock, Finset.mem_compl.mp i.property,
      Finset.mem_compl.mp j.property, hij, hne]

private theorem ctReplaceTerminalBlock_schur {I : Type*} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℝ) (A : Finset I)
    (hT : ¬ IsUnit (AndersonAC.S45.restrict H Aᶜ).det) :
    AndersonAC.S45.terminalSchur (ctReplaceTerminalBlock H A) A =
      AndersonAC.S45.terminalSchur H A := by
  classical
  let H' := ctReplaceTerminalBlock H A
  have hAA : AndersonAC.S45.restrict H' A = AndersonAC.S45.restrict H A := by
    ext i j
    change ctReplaceTerminalBlock H A i.val j.val = H i.val j.val
    simp [ctReplaceTerminalBlock, i.property, j.property]
  have hAT : H'.submatrix (Subtype.val : A → I)
        (Subtype.val : (↑(Aᶜ) : Type _) → I) = 0 := by
    ext i j
    change ctReplaceTerminalBlock H A i.val j.val = 0
    simp [ctReplaceTerminalBlock, i.property,
      Finset.mem_compl.mp j.property]
  have hTT : AndersonAC.S45.restrict H' Aᶜ = 1 := by
    ext i j
    change ctReplaceTerminalBlock H A i.val j.val =
      (if i = j then (1 : ℝ) else 0)
    by_cases hij : i = j
    · subst j
      simp [H', ctReplaceTerminalBlock, Finset.mem_compl.mp i.property]
    · have hne : i.val ≠ j.val := by
        intro h
        exact hij (Subtype.ext h)
      simp [H', ctReplaceTerminalBlock, Finset.mem_compl.mp i.property,
        Finset.mem_compl.mp j.property, hij, hne]
  have hTA : H'.submatrix (Subtype.val : (↑(Aᶜ) : Type _) → I)
        (Subtype.val : A → I) = 0 := by
    ext i j
    change ctReplaceTerminalBlock H A i.val j.val = 0
    simp [ctReplaceTerminalBlock, j.property,
      Finset.mem_compl.mp i.property]
  have hInv : (AndersonAC.S45.restrict H Aᶜ)⁻¹ = 0 :=
    Matrix.nonsing_inv_apply_not_isUnit (A := AndersonAC.S45.restrict H Aᶜ) hT
  unfold AndersonAC.S45.terminalSchur
  rw [hAA, hAT, hTT, hTA, hInv]
  simp

private theorem ct_collapsed_nonneg {d m : ℕ} (A : Finset (Torus d m))
    (i j : Fin (Fintype.card (Torus d m))) :
    0 ≤ AndersonAC.S45.collapsedDistance (ctGraph d m)
      (ctFinset (torusFinEquiv d m) A)ᶜ i j := by
  classical
  let G := ctGraph d m
  let e := torusFinEquiv d m
  have hset : {a : ℝ | ∃ w : G.Walk i j,
      a = (AndersonAC.S45.walkCost G ((ctFinset e A)ᶜ) w : ℝ)}.Nonempty := by
    rcases (ctGraph_connected d m).preconnected i j with ⟨w⟩
    exact ⟨(AndersonAC.S45.walkCost G ((ctFinset e A)ᶜ) w : ℝ), w, rfl⟩
  unfold AndersonAC.S45.collapsedDistance
  apply le_csInf hset
  intro a ha
  rcases ha with ⟨w, rfl⟩
  exact_mod_cast Nat.zero_le (AndersonAC.S45.walkCost G ((ctFinset e A)ᶜ) w)

private theorem ct_terminalSchur_reindex {I : Type} [Fintype I] [DecidableEq I]
    (e : I ≃ Fin (Fintype.card I)) (H : Matrix I I ℝ) (A : Finset I) :
    AndersonAC.S45.terminalSchur (Matrix.reindex e e H) (ctFinset e A) =
      Matrix.reindex (ctActiveEquiv e A) (ctActiveEquiv e A)
        (AndersonAC.S45.terminalSchur H A) := by
  classical
  let Hfin := Matrix.reindex e e H
  let Afin := ctFinset e A
  let eA := ctActiveEquiv e A
  let eT := ctTerminalEquiv e A
  have hAA : AndersonAC.S45.restrict Hfin Afin =
      Matrix.reindex eA eA (AndersonAC.S45.restrict H A) := by
    ext i j
    change H (e.symm i.val) (e.symm j.val) =
      H ((eA.symm i).val) ((eA.symm j).val)
    rfl
  have hAT : Hfin.submatrix (Subtype.val : Afin → Fin (Fintype.card I))
        (Subtype.val : (↑(Afinᶜ) : Type _) → Fin (Fintype.card I)) =
      Matrix.reindex eA eT
        (H.submatrix (Subtype.val : A → I) (Subtype.val : (↑(Aᶜ) : Type _) → I)) := by
    ext i j
    change H (e.symm i.val) (e.symm j.val) =
      H ((eA.symm i).val) ((eT.symm j).val)
    rfl
  have hTT : AndersonAC.S45.restrict Hfin Afinᶜ =
      Matrix.reindex eT eT (AndersonAC.S45.restrict H Aᶜ) := by
    ext i j
    change H (e.symm i.val) (e.symm j.val) =
      H ((eT.symm i).val) ((eT.symm j).val)
    rfl
  have hTA : Hfin.submatrix (Subtype.val : (↑(Afinᶜ) : Type _) → Fin (Fintype.card I))
        (Subtype.val : Afin → Fin (Fintype.card I)) =
      Matrix.reindex eT eA
        (H.submatrix (Subtype.val : (↑(Aᶜ) : Type _) → I) (Subtype.val : A → I)) := by
    ext i j
    change H (e.symm i.val) (e.symm j.val) =
      H ((eT.symm i).val) ((eA.symm j).val)
    rfl
  have hTinv : (AndersonAC.S45.restrict Hfin Afinᶜ)⁻¹ =
      Matrix.reindex eT eT ((AndersonAC.S45.restrict H Aᶜ)⁻¹) := by
    rw [hTT, Matrix.inv_reindex]
  have hprod :
      Matrix.reindex eA eT
          (H.submatrix (Subtype.val : A → I)
            (Subtype.val : (↑(Aᶜ) : Type _) → I)) *
        Matrix.reindex eT eT ((AndersonAC.S45.restrict H Aᶜ)⁻¹) *
        Matrix.reindex eT eA
          (H.submatrix (Subtype.val : (↑(Aᶜ) : Type _) → I)
            (Subtype.val : A → I)) =
      Matrix.reindex eA eA
        ((H.submatrix (Subtype.val : A → I)
          (Subtype.val : (↑(Aᶜ) : Type _) → I)) *
          (AndersonAC.S45.restrict H Aᶜ)⁻¹ *
          (H.submatrix (Subtype.val : (↑(Aᶜ) : Type _) → I)
            (Subtype.val : A → I))) := by
    simp only [Matrix.reindex_apply]
    calc
      _ = ((H.submatrix (Subtype.val : A → I)
          (Subtype.val : (↑(Aᶜ) : Type _) → I)).submatrix
          eA.symm eT.symm *
          ((AndersonAC.S45.restrict H Aᶜ)⁻¹).submatrix eT.symm eT.symm) *
          (H.submatrix (Subtype.val : (↑(Aᶜ) : Type _) → I)
            (Subtype.val : A → I)).submatrix
            eT.symm eA.symm := by rw [Matrix.mul_assoc]
      _ = ((H.submatrix (Subtype.val : A → I)
          (Subtype.val : (↑(Aᶜ) : Type _) → I)) *
          (AndersonAC.S45.restrict H Aᶜ)⁻¹).submatrix eA.symm eT.symm *
          (H.submatrix (Subtype.val : (↑(Aᶜ) : Type _) → I)
            (Subtype.val : A → I)).submatrix
            eT.symm eA.symm := by
            rw [Matrix.submatrix_mul_equiv]
      _ = ((H.submatrix (Subtype.val : A → I)
          (Subtype.val : (↑(Aᶜ) : Type _) → I)) *
          (AndersonAC.S45.restrict H Aᶜ)⁻¹ *
          (H.submatrix (Subtype.val : (↑(Aᶜ) : Type _) → I)
            (Subtype.val : A → I))).submatrix
            eA.symm eA.symm := by
            rw [Matrix.submatrix_mul_equiv]
      _ = _ := rfl
  unfold AndersonAC.S45.terminalSchur
  rw [hAA, hAT, hTinv, hTA, hprod]
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply,
    eA, ctActiveEquiv]

private def ctActiveBaseTarget {d m : ℕ} (x : RunRecord d m)
    (D : Torus d m → ℝ) : Matrix x.endpoint.active x.endpoint.active ℂ :=
  x.endpoint.M.submatrix (Subtype.val : x.endpoint.active → Torus d m) Subtype.val +
    Matrix.diagonal (fun i : x.endpoint.active => (D i.val : ℂ))

private def ctActiveTarget {d m : ℕ} (x : RunRecord d m)
    (D τ : Torus d m → ℝ) : Matrix x.endpoint.active x.endpoint.active ℂ :=
  x.endpoint.M.submatrix (Subtype.val : x.endpoint.active → Torus d m) Subtype.val +
    Matrix.diagonal (fun i : x.endpoint.active =>
      (D i.val : ℂ) - Complex.I * (τ i.val : ℂ))

private def ctScaledTau {d m : ℕ} (A : Finset (Torus d m))
    (τ : Torus d m → ℝ) : ctFinset (torusFinEquiv d m) A → ℝ :=
  fun i => (ctScale d)⁻¹ * τ ((torusFinEquiv d m).symm i.val)

private theorem ct_realSchur_activeShift {d m : ℕ} (E : ℝ) (x : RunRecord d m)
    (D : Torus d m → ℝ) (hphys : PhysicalIdentity E x) :
    (AndersonAC.S45.terminalSchur (ctRealShift E x x.endpoint.active D)
      x.endpoint.active).map (algebraMap ℝ ℂ) =
      ctActiveBaseTarget x D := by
  classical
  have hdiagmap :
      (Matrix.diagonal (fun i : x.endpoint.active => D i.val)).map (algebraMap ℝ ℂ) =
        Matrix.diagonal (fun i : x.endpoint.active => (D i.val : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hmapadd :
      (AndersonAC.S45.terminalSchur (ctBaseReal E x) x.endpoint.active +
        Matrix.diagonal (fun i : x.endpoint.active => D i.val)).map
          (algebraMap ℝ ℂ) =
      (AndersonAC.S45.terminalSchur (ctBaseReal E x) x.endpoint.active).map
          (algebraMap ℝ ℂ) +
        (Matrix.diagonal (fun i : x.endpoint.active => D i.val)).map
          (algebraMap ℝ ℂ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hSchurAdd :
      AndersonAC.S45.terminalSchur
          (ctBaseReal E x + Matrix.diagonal (fun i => if i ∈ x.endpoint.active then D i else 0))
          x.endpoint.active =
        AndersonAC.S45.terminalSchur (ctBaseReal E x) x.endpoint.active +
          Matrix.diagonal (fun i : x.endpoint.active => D i.val) :=
    ct_terminalSchur_add_activeDiag (ctBaseReal E x) x.endpoint.active D
  unfold ctRealShift ctActiveDiagonal
  rw [hSchurAdd, hmapadd, ct_terminalSchur_map,
    ← installedShifted_eq_ctBaseReal_map, ← hphys, hdiagmap]
  rfl

private theorem ct_scaledSchur_torus {d m : ℕ} (E : ℝ) (x : RunRecord d m)
    (D : Torus d m → ℝ) (hphys : PhysicalIdentity E x) :
    (AndersonAC.S45.terminalSchur (ctScaledReal E x x.endpoint.active D)
      x.endpoint.active).map (algebraMap ℝ ℂ) =
      ((ctScale d)⁻¹ : ℂ) • ctActiveBaseTarget x D := by
  have hK : ctScale d ≠ 0 := by
    dsimp [ctScale]
    positivity
  have hmapSmul (R : Matrix (x.endpoint.active) (x.endpoint.active) ℝ) :
      ((ctScale d)⁻¹ • R).map (algebraMap ℝ ℂ) =
        ((ctScale d)⁻¹ : ℂ) • R.map (algebraMap ℝ ℂ) := by
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  rw [ctScaledReal, ct_terminalSchur_smul _ (inv_ne_zero hK) _ _, hmapSmul,
    ct_realSchur_activeShift E x D hphys]

private theorem ct_dampedActive_reindex {d m : ℕ} (E : ℝ) (x : RunRecord d m)
    (D τ : Torus d m → ℝ) (hphys : PhysicalIdentity E x) :
    AndersonAC.S45.dampedActive (ctFinRealMatrix E x D)
        (ctFinset (torusFinEquiv d m) x.endpoint.active)
        (ctScaledTau x.endpoint.active τ) =
      ((ctScale d)⁻¹ : ℂ) •
        Matrix.reindex (ctActiveEquiv (torusFinEquiv d m) x.endpoint.active)
          (ctActiveEquiv (torusFinEquiv d m) x.endpoint.active) (ctActiveTarget x D τ) := by
  classical
  let e := torusFinEquiv d m
  let A := x.endpoint.active
  let Afin := ctFinset e A
  let eA := ctActiveEquiv e A
  have hSchurFin :
      (AndersonAC.S45.terminalSchur (ctFinRealMatrix E x D) Afin).map
          (algebraMap ℝ ℂ) =
        Matrix.reindex eA eA
          (((ctScale d)⁻¹ : ℂ) • ctActiveBaseTarget x D) := by
    change (AndersonAC.S45.terminalSchur
        (Matrix.reindex e e (ctScaledReal E x A D)) Afin).map (algebraMap ℝ ℂ) = _
    rw [ct_terminalSchur_reindex]
    have hcomm (R : Matrix A A ℝ) :
        (Matrix.reindex eA eA R).map (algebraMap ℝ ℂ) =
          Matrix.reindex eA eA (R.map (algebraMap ℝ ℂ)) := by
      ext i j
      simp [Matrix.reindex_apply, Matrix.submatrix_map]
    rw [hcomm, ct_scaledSchur_torus E x D hphys]
  have hf : (fun z : ℝ => (z : ℂ)) = (algebraMap ℝ ℂ) := by
    funext z
    rfl
  rw [← hf] at hSchurFin
  have hSchurFin' := hSchurFin
  dsimp [Afin, A, e] at hSchurFin'
  let BFin := Matrix.reindex eA eA (ctActiveBaseTarget x D)
  let Q : Matrix A A ℂ := Matrix.diagonal (fun i : A => Complex.I * (τ i.val : ℂ))
  let QFin := Matrix.reindex eA eA Q
  have hSchurFin'' :
      (AndersonAC.S45.terminalSchur (ctFinRealMatrix E x D) Afin).map
          (fun z : ℝ => (z : ℂ)) = ((ctScale d)⁻¹ : ℂ) • BFin := by
    rw [hSchurFin']
    ext i j
    simp [BFin, Matrix.reindex_apply, Matrix.smul_apply, smul_eq_mul,
      ctActiveEquiv]
  have hQ : Matrix.diagonal (fun i : Afin => Complex.I *
      ((ctScaledTau A τ i : ℝ) : ℂ)) = ((ctScale d)⁻¹ : ℂ) • QFin := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [QFin, Matrix.reindex_apply, Matrix.submatrix_apply,
        Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply]
      simp only [if_true, Q, Matrix.diagonal_apply]
      have hval : (eA.symm i).val = e.symm i.val := rfl
      rw [hval]
      simp [ctScaledTau, e, A]
      ring_nf
    · simp [QFin, Q, Matrix.reindex_apply, Matrix.diagonal_apply, hij]
  have hpoint (i j : A) : ctActiveTarget x D τ i j =
      ctActiveBaseTarget x D i j - Q i j := by
    by_cases hij : i = j
    · subst j
      simp [ctActiveTarget, ctActiveBaseTarget, Q, Matrix.diagonal_apply]
      ring_nf
    · simp [ctActiveTarget, ctActiveBaseTarget, Q, Matrix.diagonal_apply, hij]
  have hTarget : Matrix.reindex eA eA (ctActiveTarget x D τ) = BFin - QFin := by
    ext i j
    change ctActiveTarget x D τ (eA.symm i) (eA.symm j) =
      ctActiveBaseTarget x D (eA.symm i) (eA.symm j) - Q (eA.symm i) (eA.symm j)
    exact hpoint (eA.symm i) (eA.symm j)
  unfold AndersonAC.S45.dampedActive
  rw [hSchurFin'', hQ, hTarget, smul_sub]

/-- **Terminal-distance Combes--Thomas decay on the torus active block** (05-local-sweeps.tex:62–90,
Lemma `locality`, `eq:local-ct`): the S45 locality estimate transported to the torus; the
collapsed walk distance dominates the list-path terminal distance. -/
theorem terminalCT_proof (d : ℕ) : TerminalCTStatement d := by
  classical
  intro c₀ C₀ hc₀ hc₀C
  let K : ℝ := ctScale d
  have hK : 0 < K := by dsimp [K, ctScale]; positivity
  have hC₀ : 0 < C₀ := lt_of_lt_of_le hc₀ hc₀C
  let Cgeo : ℝ := 1 + K / c₀ + C₀ / K
  have hCgeo : 1 ≤ Cgeo := by
    dsimp [Cgeo]
    have h1 : 0 ≤ K / c₀ := div_nonneg hK.le hc₀.le
    have h2 : 0 ≤ C₀ / K := div_nonneg hC₀.le hK.le
    linarith
  have hCgeoPos : 0 < Cgeo := lt_of_lt_of_le zero_lt_one hCgeo
  have hCgeoLow : K / c₀ ≤ Cgeo := by
    dsimp [Cgeo]
    have h2 : 0 ≤ C₀ / K := div_nonneg hC₀.le hK.le
    linarith
  have hCgeoHigh : C₀ / K ≤ Cgeo := by
    dsimp [Cgeo]
    have h1 : 0 ≤ K / c₀ := div_nonneg hK.le hc₀.le
    linarith
  have hDampLow : 1 / Cgeo ≤ c₀ / K := by
    have hmul' : K ≤ Cgeo * c₀ := (div_le_iff₀ hc₀).mp hCgeoLow
    have hmul : K ≤ c₀ * Cgeo := by nlinarith [hmul']
    exact (div_le_div_iff₀ hCgeoPos hK).2 (by nlinarith [hmul])
  obtain ⟨a, ha, CLoc, hCLoc, tLoc, htLoc, hLocality⟩ :=
    AndersonAC.AgentS45.locality_proof d Cgeo hCgeo
  refine ⟨a, ha, max 1 CLoc, le_max_left _ _, tLoc, htLoc, ?_⟩
  intro m t E x D τ G ht htt hphys hτ hleft
  let e := torusFinEquiv d m
  let A := x.endpoint.active
  let Afin := ctFinset e A
  let eA := ctActiveEquiv e A
  let Hfin := ctFinRealMatrix E x D
  let Hrep := ctReplaceTerminalBlock Hfin Afin
  let Huse := if IsUnit (AndersonAC.S45.restrict Hfin Afinᶜ) then Hfin else Hrep
  have hUseFin : IsUnit (AndersonAC.S45.restrict Hfin Afinᶜ) → Huse = Hfin := by
    intro ht
    simp [Huse, ht]
  have hUseRep : ¬ IsUnit (AndersonAC.S45.restrict Hfin Afinᶜ) → Huse = Hrep := by
    intro ht
    simp [Huse, ht]
  let τfin := ctScaledTau A τ
  have htLoc' : t < tLoc := htt
  have hτfin : ∀ i : Afin, t / Cgeo ≤ τfin i ∧ τfin i ≤ Cgeo * t := by
    intro i
    have hiA : e.symm i.val ∈ A := (Finset.mem_filter.mp i.property).2
    have hinput := hτ (e.symm i.val) hiA
    constructor
    · change t / Cgeo ≤ K⁻¹ * τ (e.symm i.val)
      calc
        t / Cgeo = t * (1 / Cgeo) := by ring
        _ ≤ t * (c₀ / K) := mul_le_mul_of_nonneg_left hDampLow ht.le
        _ = (c₀ * t) / K := by ring
        _ ≤ τ (e.symm i.val) / K :=
          div_le_div_of_nonneg_right hinput.1 hK.le
        _ = K⁻¹ * τ (e.symm i.val) := by rw [div_eq_mul_inv]; ring
    · change K⁻¹ * τ (e.symm i.val) ≤ Cgeo * t
      calc
        K⁻¹ * τ (e.symm i.val) = τ (e.symm i.val) / K := by
          rw [div_eq_mul_inv]; ring
        _ ≤ (C₀ * t) / K := div_le_div_of_nonneg_right hinput.2 hK.le
        _ = (C₀ / K) * t := by ring
        _ ≤ Cgeo * t := mul_le_mul_of_nonneg_right hCgeoHigh ht.le
  have hHsym : Huse.IsSymm := by
    by_cases ht : IsUnit (AndersonAC.S45.restrict Hfin Afinᶜ)
    · rw [hUseFin ht]
      exact ctFinRealMatrix_isSymm E x D
    · rw [hUseRep ht]
      exact ctReplaceTerminalBlock_isSymm Hfin Afin (ctFinRealMatrix_isSymm E x D)
  have hHopFin := ctFinHop_bounds E x A D
  have hHopUse : ∀ i j, i ≠ j →
      (((ctGeometry d m).graph.Adj i j → |Huse i j| ≤ 1) ∧
        (¬(ctGeometry d m).graph.Adj i j → Huse i j = 0)) := by
    intro i j hij
    by_cases ht : IsUnit (AndersonAC.S45.restrict Hfin Afinᶜ)
    · rw [hUseFin ht]
      simpa [ctGeometry] using hHopFin i j hij
    · have hbase := hHopFin i j hij
      rw [hUseRep ht]
      have hreplace : ∀ i j, i ≠ j → (i ∉ Afin ∨ j ∉ Afin) → Hrep i j = 0 := by
        intro i j hne hmem
        change ctReplaceTerminalBlock Hfin Afin i j = 0
        rcases hmem with hi | hj
        · simp [ctReplaceTerminalBlock, hi, hne]
        · simp [ctReplaceTerminalBlock, hj, hne]
      constructor
      · intro hadj
        by_cases hi : i ∈ Afin <;> by_cases hj : j ∈ Afin
        · have hentry : Hrep i j = Hfin i j := by
            change ctReplaceTerminalBlock Hfin Afin i j = Hfin i j
            simp [ctReplaceTerminalBlock, hi, hj]
          have hAdj : (ctGraph d m).Adj i j := by simpa [ctGeometry] using hadj
          have hbound : |Hfin i j| ≤ 1 := by simpa [Hfin] using hbase.1 hAdj
          exact hentry.symm ▸ hbound
        · have hz := hreplace i j hij (Or.inr hj)
          simp [hz]
        · have hz := hreplace i j hij (Or.inl hi)
          simp [hz]
        · have hz := hreplace i j hij (Or.inl hi)
          simp [hz]
      · intro hnon
        by_cases hi : i ∈ Afin <;> by_cases hj : j ∈ Afin
        · have hentry : Hrep i j = Hfin i j := by
            change ctReplaceTerminalBlock Hfin Afin i j = Hfin i j
            simp [ctReplaceTerminalBlock, hi, hj]
          rw [hentry]
          simpa [Hfin] using hbase.2 (by simpa [ctGeometry] using hnon)
        · exact hreplace i j hij (Or.inr hj)
        · exact hreplace i j hij (Or.inl hi)
        · exact hreplace i j hij (Or.inl hi)
  have hSchurUse : AndersonAC.S45.terminalSchur Huse Afin =
      AndersonAC.S45.terminalSchur Hfin Afin := by
    by_cases ht : IsUnit (AndersonAC.S45.restrict Hfin Afinᶜ)
    · rw [hUseFin ht]
    · have hdet : ¬ IsUnit (AndersonAC.S45.restrict Hfin Afinᶜ).det := by
        intro hdet
        exact ht ((Matrix.isUnit_iff_isUnit_det _).2 hdet)
      rw [hUseRep ht]
      exact ctReplaceTerminalBlock_schur Hfin Afin hdet
  have hTermUse : IsUnit (AndersonAC.S45.restrict Huse Afinᶜ) := by
    by_cases ht : IsUnit (AndersonAC.S45.restrict Hfin Afinᶜ)
    · rw [hUseFin ht]
      exact ht
    · rw [hUseRep ht, ctReplaceTerminalBlock_terminal_eq_one]
      exact isUnit_one
  have hDampedUse : AndersonAC.S45.dampedActive Huse Afin τfin =
      AndersonAC.S45.dampedActive Hfin Afin τfin := by
    simp [AndersonAC.S45.dampedActive, hSchurUse]
  have hActiveLeft : ctActiveTarget x D τ *
      G.submatrix (Subtype.val : A → Torus d m) (Subtype.val : A → Torus d m) = 1 := by
    exact hleft
  let Gfin := Matrix.reindex eA eA
    (G.submatrix (Subtype.val : A → Torus d m) (Subtype.val : A → Torus d m))
  have hGprod : Matrix.reindex eA eA (ctActiveTarget x D τ) * Gfin = 1 := by
    change (ctActiveTarget x D τ).submatrix eA.symm eA.symm *
      (G.submatrix (Subtype.val : A → Torus d m)
        (Subtype.val : A → Torus d m)).submatrix eA.symm eA.symm = 1
    rw [Matrix.submatrix_mul_equiv, hActiveLeft]
    simp
  have hLocalMat : AndersonAC.S45.dampedActive Huse Afin τfin =
      ((ctScale d)⁻¹ : ℂ) • Matrix.reindex eA eA (ctActiveTarget x D τ) := by
    rw [hDampedUse, ct_dampedActive_reindex E x D τ hphys]
  let Cstar := ctGeometry d m
  have hLoc := hLocality (Fintype.card (Torus d m)) Cstar Huse Afin τfin t
    ht htLoc' hHsym hHopUse hTermUse hτfin
  have hUnit : IsUnit (AndersonAC.S45.dampedActive Huse Afin τfin) := hLoc.1
  have hKinv : ((ctScale d)⁻¹ : ℂ) * (ctScale d : ℂ) = 1 := by
    exact_mod_cast (inv_mul_cancel₀ (ne_of_gt hK))
  have hRight : AndersonAC.S45.dampedActive Huse Afin τfin *
      ((ctScale d : ℂ) • Gfin) = 1 := by
    calc
      _ = (((ctScale d)⁻¹ : ℂ) • Matrix.reindex eA eA (ctActiveTarget x D τ)) *
          ((ctScale d : ℂ) • Gfin) := by rw [hLocalMat]
      _ = (((ctScale d)⁻¹ : ℂ) * (ctScale d : ℂ)) •
          (Matrix.reindex eA eA (ctActiveTarget x D τ) * Gfin) :=
        smul_mul_smul_comm ((ctScale d)⁻¹ : ℂ)
          (Matrix.reindex eA eA (ctActiveTarget x D τ)) (ctScale d : ℂ) Gfin
      _ = 1 := by rw [hKinv, hGprod, one_smul]
  have hInv : (AndersonAC.S45.dampedActive Huse Afin τfin)⁻¹ =
      (ctScale d : ℂ) • Gfin := by
    have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hUnit
    have hInvUnit : (AndersonAC.S45.dampedActive Huse Afin τfin)⁻¹ *
        AndersonAC.S45.dampedActive Huse Afin τfin = 1 :=
      Matrix.nonsing_inv_mul (A := AndersonAC.S45.dampedActive Huse Afin τfin) hdet
    calc
      (AndersonAC.S45.dampedActive Huse Afin τfin)⁻¹ =
          (AndersonAC.S45.dampedActive Huse Afin τfin)⁻¹ *
            (AndersonAC.S45.dampedActive Huse Afin τfin * ((ctScale d : ℂ) • Gfin)) := by
              rw [hRight]; simp
      _ = ((AndersonAC.S45.dampedActive Huse Afin τfin)⁻¹ *
            AndersonAC.S45.dampedActive Huse Afin τfin) * ((ctScale d : ℂ) • Gfin) := by
              rw [Matrix.mul_assoc]
      _ = (ctScale d : ℂ) • Gfin := by
        rw [hInvUnit]
        simp
  intro i hi k hk
  let ii : Afin := eA ⟨i, hi⟩
  let kk : Afin := eA ⟨k, hk⟩
  have hGik : Gfin ii kk = G i k := by
    change G (eA.symm (eA ⟨i, hi⟩)).val (eA.symm (eA ⟨k, hk⟩)).val = G i k
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have hb := hLoc.2 ii kk
  rw [hInv, Matrix.smul_apply, smul_eq_mul, hGik] at hb
  have hnormK : ‖(Real.sqrt t : ℂ) * ((ctScale d : ℂ) * G i k)‖ =
      K * ‖(Real.sqrt t : ℂ) * G i k‖ := by
    rw [mul_left_comm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hK]
  have hK1 : 1 ≤ K := by
    dsimp [K, ctScale]
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  have hcoll : terminalDistance (nnGraph d m) (Finset.univ \ x.endpoint.active) i k ≤
      AndersonAC.S45.collapsedDistance Cstar.graph Afinᶜ (ii : Fin (Fintype.card (Torus d m)))
        (kk : Fin (Fintype.card (Torus d m))) := by
    have h := terminal_le_collapsed_ct x.endpoint.active (e i) (e k)
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      Finset.compl_eq_univ_sdiff x.endpoint.active] at h
    exact h
  have hat : 0 ≤ a * t := (mul_pos ha ht).le
  have hexp : Real.exp (-a * t * AndersonAC.S45.collapsedDistance Cstar.graph Afinᶜ
        (ii : Fin (Fintype.card (Torus d m))) (kk : Fin (Fintype.card (Torus d m)))) ≤
      Real.exp (-a * t * terminalDistance (nnGraph d m) (Finset.univ \ x.endpoint.active) i k) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hcoll hat
    linarith
  have hsq : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  calc ‖(Real.sqrt t : ℂ) * G i k‖ ≤ K * ‖(Real.sqrt t : ℂ) * G i k‖ :=
        le_mul_of_one_le_left (norm_nonneg _) hK1
    _ = ‖(Real.sqrt t : ℂ) * ((ctScale d : ℂ) * G i k)‖ := hnormK.symm
    _ ≤ CLoc / Real.sqrt t * Real.exp (-a * t * AndersonAC.S45.collapsedDistance Cstar.graph
          Afinᶜ (ii : Fin (Fintype.card (Torus d m))) (kk : Fin (Fintype.card (Torus d m)))) := hb
    _ ≤ max 1 CLoc / Real.sqrt t *
          Real.exp (-a * t * terminalDistance (nnGraph d m) (Finset.univ \ x.endpoint.active) i k) :=
        mul_le_mul (div_le_div_of_nonneg_right (le_max_right _ _) hsq) hexp
          (Real.exp_pos _).le (div_nonneg (le_trans zero_le_one (le_max_left _ _)) hsq)

/-- **Active-block Combes--Thomas decay in the physical distance** (05-local-sweeps.tex:62–100, Lemma
`locality` with `eq:local-physical-decay` and the split at distance `t^{-2}`). -/
theorem activeCT_proof (d : ℕ) (hd : 3 ≤ d) : ActiveCTStatement d := by
  intro c₀ C₀ hc₀ hc₀C
  obtain ⟨a, ha, Cc, hCc, tc, htc, hCT⟩ := terminalCT_proof d c₀ C₀ hc₀ hc₀C
  have hCcpos : 0 < Cc := lt_of_lt_of_le one_pos hCc
  obtain ⟨cT3, hcT3, Cphys, hCphys, tPhys, htPhys, hPD⟩ :=
    AndersonAC.AgentS45.physical_decay_proof Cc a hCcpos ha
  let Cf : ℝ := max (max 4 Cc) (max Cphys (max cT3⁻¹ (4 / a)))
  have hCf4 : 4 ≤ Cf := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCfCc : Cc ≤ Cf := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCfP : Cphys ≤ Cf := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCfc : cT3⁻¹ ≤ Cf :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hCfa : 4 / a ≤ Cf :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hCfpos : 0 < Cf := by linarith
  have hrate3 : 1 / Cf ≤ cT3 := by
    have h := one_div_le_one_div_of_le (inv_pos.mpr hcT3) hCfc
    rwa [one_div, one_div, inv_inv, ← one_div] at h
  have hrateA : 1 / Cf ≤ a / 4 := by
    have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 4 / a) hCfa
    rwa [one_div_div] at h
  refine ⟨Cf, by linarith, min tc (min tPhys 1), lt_min htc (lt_min htPhys one_pos), ?_⟩
  intro m t E x D τ G ht htt hphys hmetric hτ hleft i hi k hk
  have htc' : t < tc := lt_of_lt_of_le htt (min_le_left _ _)
  have htP : t < tPhys := lt_of_lt_of_le htt ((min_le_right _ _).trans (min_le_left _ _))
  have ht1 : t < 1 := lt_of_lt_of_le htt ((min_le_right _ _).trans (min_le_right _ _))
  have hdec := hCT m t E x D τ G ht htc' hphys hτ hleft i hi k hk
  have hdT0 : 0 ≤ terminalDistance (nnGraph d m) (Finset.univ \ x.endpoint.active) i k := by
    unfold terminalDistance
    exact Nat.cast_nonneg _
  have hr0 : 0 ≤ physicalDistance d m i k := by
    unfold physicalDistance
    exact Nat.cast_nonneg _
  have hmet := hmetric i k
  set z : ℂ := (Real.sqrt t : ℂ) * G i k with hz
  set dT := terminalDistance (nnGraph d m) (Finset.univ \ x.endpoint.active) i k with hdT
  set r := physicalDistance d m i k with hr
  have hsq : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hpow : AndersonAC.S45.power t (-103 / 100) = t ^ (-1.03 : ℝ) := by
    simp only [AndersonAC.S45.power, Real.rpow_eq_pow]
    norm_num
  have hrough : ‖z‖ ≤ Cc / Real.sqrt t := by
    have h1 : Real.exp (-a * t * dT) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have := mul_nonneg (mul_pos ha ht).le hdT0
      linarith
    exact hdec.trans (mul_le_of_le_one_right (div_nonneg hCcpos.le hsq) h1)
  constructor
  · have h1 := hPD t r dT z ht htP hr0 (by rw [hpow]; linarith) hrough hdec
    have hx : 0 ≤ t ^ 3 * r := mul_nonneg (pow_nonneg ht.le 3) hr0
    have hexp : Real.exp (-cT3 * t ^ 3 * r) ≤ Real.exp (-t ^ 3 * r / Cf) := by
      apply Real.exp_le_exp.mpr
      have h2 := mul_le_mul_of_nonneg_right hrate3 hx
      have e1 : -t ^ 3 * r / Cf = -(1 / Cf * (t ^ 3 * r)) := by ring
      rw [e1]
      linarith
    exact h1.trans (mul_le_mul (div_le_div_of_nonneg_right hCfP hsq) hexp
      (Real.exp_pos _).le (div_nonneg hCfpos.le hsq))
  · intro hfar
    have hP0 : 0 ≤ AndersonAC.S45.power t (-2) := by
      simp only [AndersonAC.S45.power, Real.rpow_eq_pow]
      exact Real.rpow_nonneg ht.le _
    have hpow2 : t ^ (-1.03 : ℝ) ≤ AndersonAC.S45.power t (-2) := by
      simp only [AndersonAC.S45.power, Real.rpow_eq_pow]
      exact Real.rpow_le_rpow_of_exponent_ge ht ht1.le (by norm_num)
    have h4P := mul_le_mul_of_nonneg_right hCf4 hP0
    have hdTr : r / 4 ≤ dT := by linarith
    have hexp : Real.exp (-a * t * dT) ≤ Real.exp (-t * r / Cf) := by
      apply Real.exp_le_exp.mpr
      have h1 := mul_le_mul_of_nonneg_right hrateA (mul_nonneg ht.le hr0)
      have h2 := mul_le_mul_of_nonneg_left hdTr (mul_pos ha ht).le
      have e1 : -t * r / Cf = -(1 / Cf * (t * r)) := by ring
      rw [e1]
      nlinarith
    exact hdec.trans (mul_le_mul (div_le_div_of_nonneg_right hCfCc hsq) hexp
      (Real.exp_pos _).le (div_nonneg hCfpos.le hsq))

end AndersonAC.AgentS78
