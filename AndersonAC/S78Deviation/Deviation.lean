import AndersonAC.S78Deviation.Coordinates
import AndersonAC.S78.AssemblyEstimates

open scoped BigOperators

noncomputable section

namespace AndersonAC.SolS78Deviation

open AndersonAC.S78

def coordCubeMean {d l : ℕ} (v : CoordCube d l → ℂ) : ℂ :=
  (Fintype.card (CoordCube d l) : ℂ)⁻¹ * ∑ i, v i

def coordCubeNormSq {d l : ℕ} (v : CoordCube d l → ℂ) : ℝ :=
  ∑ i, ‖v i‖ ^ 2

/-- The raw endpoint supplied by S3's weighted-cube theorem, written over the
same coordinate cube used by the local torus transport. -/
def S3WeightedCubeStatement (d : ℕ) : Prop :=
  ∃ Cw : ℝ, 0 < Cw ∧ ∀ (l : ℕ), 1 ≤ l →
    ∀ (v : CoordCube d l → ℂ) (a : CoordCube d l → ℝ),
      (∀ i, 0 ≤ a i) →
      coordCubeNormSq (fun i => v i - coordCubeMean v) ≤
          Cw * (l : ℝ) ^ 2 * coordCubeEnergy v ∧
      (∑ i, a i * ‖v i - coordCubeMean v‖ ^ 2) ≤
        Cw * Real.rpow (sSup (Set.range a)) (1 / 3 : ℝ) *
          Real.rpow (∑ i, a i) (2 / 3 : ℝ) * coordCubeEnergy v

lemma coordCubeMean_eq_localCubeMean (d m : ℕ) (z : Torus d m) (R : ℝ)
    (hR : 1 ≤ R) (hside : 4 * R < (OAI.Anderson.sideLength m : ℝ))
    (v : Torus d m → ℝ) :
    coordCubeMean (fun x : CoordCube d (localCubeLength R) =>
      (v (localCubeToTorus z R x) : ℂ)) =
        (AndersonAC.SolS78.localCubeMean d m z R v : ℂ) := by
  classical
  let Q : Finset (Torus d m) := cube d m z (2 * R)
  let e := localCubeEquiv z R hR hside
  let vC : CoordCube d (localCubeLength R) → ℂ :=
    fun x => (v (localCubeToTorus z R x) : ℂ)
  have heval (x : CoordCube d (localCubeLength R)) :
      (e x).val = localCubeToTorus z R x := rfl
  have hsumR : (∑ x, v (localCubeToTorus z R x)) = ∑ i ∈ Q, v i := by
    calc
      (∑ x, v (localCubeToTorus z R x)) = ∑ x, v (e x).val := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [heval]
      _ = ∑ x : localCubeDomain z R, v x.val :=
        Equiv.sum_comp e (fun x : localCubeDomain z R => v x.val)
      _ = ∑ i ∈ Q, v i := by
        simpa [Q] using localCubeDomain_sum z R v
  have hcard : Fintype.card (CoordCube d (localCubeLength R)) = Q.card := by
    calc
      Fintype.card (CoordCube d (localCubeLength R)) =
          Fintype.card (localCubeDomain z R) := Fintype.card_congr e
      _ = Q.card := by
        change Fintype.card {x : Torus d m // x ∈ Q} = Q.card
        rw [Fintype.card_subtype]
        simp [Q]
  have hcardR : (Fintype.card (CoordCube d (localCubeLength R)) : ℝ) = Q.card := by
    exact_mod_cast hcard
  have hcast : coordCubeMean vC =
      (((Fintype.card (CoordCube d (localCubeLength R)) : ℝ)⁻¹ *
        ∑ x, v (localCubeToTorus z R x) : ℝ) : ℂ) := by
    simp [coordCubeMean, vC, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_natCast, Complex.ofReal_sum]
  rw [hcast, hsumR, hcardR]
  simp [AndersonAC.SolS78.localCubeMean, Q, div_eq_mul_inv]
  ring

lemma cube_inner_subset_outer (d m : ℕ) (z : Torus d m) (R : ℝ) :
    cube d m z R ⊆ cube d m z (2 * R) := by
  intro i hi
  simp only [cube, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  intro j
  have h := hi j
  linarith

theorem localDeviationInput_of_weightedCube
    (hCube : ∀ d : ℕ, 3 ≤ d → S3WeightedCubeStatement d) :
    AndersonAC.SolS78.LocalDeviationInput := by
  classical
  intro d hd
  obtain ⟨Cw, hCw, hCubeBounds⟩ := hCube d hd
  refine ⟨25 * (Cw + 1), by positivity, ?_⟩
  intro m z R Lmax Ltotal l v hR hside hLmax hLtotal hl hsupport htotal
  let Q : Finset (Torus d m) := cube d m z (2 * R)
  let e := localCubeEquiv z R hR hside
  let vC : CoordCube d (localCubeLength R) → ℂ :=
    fun x => (v (localCubeToTorus z R x) : ℂ)
  let lC : CoordCube d (localCubeLength R) → ℝ :=
    fun x => l (localCubeToTorus z R x)
  let μC : ℂ := coordCubeMean vC
  have heval (x : CoordCube d (localCubeLength R)) :
      (e x).val = localCubeToTorus z R x := rfl
  have hlen : 1 ≤ localCubeLength R := by
    unfold localCubeLength localCubeRadius
    omega
  have hinner : cube d m z R ⊆ Q := by
    simpa [Q] using cube_inner_subset_outer d m z R
  have hweightC : ∀ x, 0 ≤ lC x ∧ lC x ≤ Lmax := by
    intro x
    exact hl (localCubeToTorus z R x)
  have hzeroQ (i : Torus d m) (hi : i ∉ Q) : l i = 0 := by
    apply hsupport
    intro hiInner
    exact hi (hinner hiInner)
  have hsumQ : (∑ i ∈ Q, l i) = ∑ i, l i := by
    apply Finset.sum_subset (s₁ := Q) (s₂ := Finset.univ)
    · exact Finset.subset_univ _
    · intro i hiQ hiNot
      simp [hzeroQ i hiNot]
  have hsumC : (∑ x, lC x) ≤ Ltotal := by
    calc
      (∑ x, lC x) = ∑ x, l (e x).val := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [lC, heval]
      _ = ∑ x : localCubeDomain z R, l x.val :=
        Equiv.sum_comp e (fun x : localCubeDomain z R => l x.val)
      _ = ∑ i ∈ Q, l i := by
        simpa [Q] using localCubeDomain_sum z R l
      _ ≤ Ltotal := by simpa [hsumQ] using htotal
  have hrange_ne : (Set.range lC).Nonempty := by
    let x : CoordCube d (localCubeLength R) := fun _ => ⟨0, by
      unfold localCubeLength localCubeRadius
      omega⟩
    exact ⟨lC x, ⟨x, rfl⟩⟩
  have hrange_bdd : BddAbove (Set.range lC) := (Set.finite_range lC).bddAbove
  have hsup : sSup (Set.range lC) ≤ Lmax := by
    apply csSup_le hrange_ne
    rintro y ⟨x, rfl⟩
    exact (hweightC x).2
  have hsup_nonneg : 0 ≤ sSup (Set.range lC) := by
    obtain ⟨y, hy⟩ := hrange_ne
    have hle := le_csSup hrange_bdd hy
    rcases hy with ⟨x, rfl⟩
    exact le_trans (hweightC x).1 hle
  have hsum_nonneg : 0 ≤ ∑ x, lC x := Finset.sum_nonneg fun x hx => (hweightC x).1
  have hsup_pow : Real.rpow (sSup (Set.range lC)) (1 / 3 : ℝ) ≤
      Real.rpow Lmax (1 / 3 : ℝ) :=
    Real.rpow_le_rpow hsup_nonneg hsup (by norm_num)
  have hsum_pow : Real.rpow (∑ x, lC x) (2 / 3 : ℝ) ≤
      Real.rpow Ltotal (2 / 3 : ℝ) :=
    Real.rpow_le_rpow hsum_nonneg hsumC (by norm_num)
  have hcube := hCubeBounds (localCubeLength R) hlen vC lC (fun x => (hweightC x).1)
  have hcoord_nonneg : 0 ≤ coordCubeEnergy vC := by
    unfold coordCubeEnergy
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro x hx
    apply Finset.sum_nonneg
    intro y hy
    split_ifs <;> positivity
  have hcoord_energy := coordCubeEnergy_le_cubeGradient z R hR hside v
  have hscale_nonneg :
      0 ≤ Real.rpow Lmax (1 / 3 : ℝ) * Real.rpow Ltotal (2 / 3 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hLmax _) (Real.rpow_nonneg hLtotal _)
  have hcoef_nonneg :
      0 ≤ Cw * Real.rpow Lmax (1 / 3 : ℝ) * Real.rpow Ltotal (2 / 3 : ℝ) :=
    mul_nonneg (mul_nonneg (le_of_lt hCw) (Real.rpow_nonneg hLmax _))
      (Real.rpow_nonneg hLtotal _)
  have hscaledCube :
      Cw * Real.rpow (sSup (Set.range lC)) (1 / 3 : ℝ) *
          Real.rpow (∑ x, lC x) (2 / 3 : ℝ) ≤
        Cw * Real.rpow Lmax (1 / 3 : ℝ) * Real.rpow Ltotal (2 / 3 : ℝ) := by
    calc
      _ ≤ Cw * Real.rpow Lmax (1 / 3 : ℝ) * Real.rpow (∑ x, lC x) (2 / 3 : ℝ) := by
        have hfirst : Cw * Real.rpow (sSup (Set.range lC)) (1 / 3 : ℝ) ≤
            Cw * Real.rpow Lmax (1 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_left hsup_pow (le_of_lt hCw)
        exact mul_le_mul_of_nonneg_right hfirst (Real.rpow_nonneg hsum_nonneg _)
      _ ≤ Cw * Real.rpow Lmax (1 / 3 : ℝ) * Real.rpow Ltotal (2 / 3 : ℝ) := by
        apply mul_le_mul_of_nonneg_left hsum_pow
        exact mul_nonneg (le_of_lt hCw) (Real.rpow_nonneg hLmax _)
  have hweightedCube :
      (∑ x, lC x * ‖vC x - μC‖ ^ 2) ≤
        Cw * Real.rpow Lmax (1 / 3 : ℝ) * Real.rpow Ltotal (2 / 3 : ℝ) *
          cubeGradient d m Q v := by
    calc
      (∑ x, lC x * ‖vC x - μC‖ ^ 2) ≤
          Cw * Real.rpow (sSup (Set.range lC)) (1 / 3 : ℝ) *
            Real.rpow (∑ x, lC x) (2 / 3 : ℝ) * coordCubeEnergy vC := hcube.2
      _ ≤ Cw * Real.rpow Lmax (1 / 3 : ℝ) *
          Real.rpow Ltotal (2 / 3 : ℝ) * coordCubeEnergy vC :=
        mul_le_mul_of_nonneg_right hscaledCube hcoord_nonneg
      _ ≤ Cw * Real.rpow Lmax (1 / 3 : ℝ) *
          Real.rpow Ltotal (2 / 3 : ℝ) * cubeGradient d m Q v :=
        mul_le_mul_of_nonneg_left hcoord_energy hcoef_nonneg
  have hmean : μC = (AndersonAC.SolS78.localCubeMean d m z R v : ℂ) := by
    dsimp [μC, vC]
    exact coordCubeMean_eq_localCubeMean d m z R hR hside v
  have hweightedReindex :
      (∑ i, l i * (v i - AndersonAC.SolS78.localCubeMean d m z R v) ^ 2) =
        ∑ x, lC x * ‖vC x - μC‖ ^ 2 := by
    let f : Torus d m → ℝ := fun i =>
      l i * (v i - AndersonAC.SolS78.localCubeMean d m z R v) ^ 2
    have hglobal : (∑ i, f i) = ∑ i ∈ Q, f i := by
      symm
      apply Finset.sum_subset (s₁ := Q) (s₂ := Finset.univ)
      · exact Finset.subset_univ _
      · intro i hiQ hiNot
        simp [f, hzeroQ i hiNot]
    have hdomain :
        (∑ x : localCubeDomain z R, f x.val) = ∑ i ∈ Q, f i := by
      simpa [Q] using localCubeDomain_sum z R f
    have hcoord :
        (∑ x, lC x * ‖vC x - μC‖ ^ 2) =
          ∑ x : localCubeDomain z R, f x.val := by
      calc
        (∑ x, lC x * ‖vC x - μC‖ ^ 2) = ∑ x, f (e x).val := by
          apply Finset.sum_congr rfl
          intro x hx
          have hnorm : ‖vC x - μC‖ ^ 2 =
              (v (localCubeToTorus z R x) -
                AndersonAC.SolS78.localCubeMean d m z R v) ^ 2 := by
            rw [hmean]
            have hcast :
                ((v (localCubeToTorus z R x) -
                  AndersonAC.SolS78.localCubeMean d m z R v : ℝ) : ℂ) =
                vC x - (AndersonAC.SolS78.localCubeMean d m z R v : ℂ) := by
              simp [vC]
            rw [← hcast, Complex.norm_real, Real.norm_eq_abs, sq_abs]
          simp only [f, lC, heval]
          rw [hnorm]
        _ = ∑ x : localCubeDomain z R, f x.val :=
          Equiv.sum_comp e (fun x : localCubeDomain z R => f x.val)
    exact hglobal.trans (hdomain.symm.trans hcoord.symm)
  have hgrad_nonneg : 0 ≤ cubeGradient d m Q v := by
    unfold cubeGradient
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    split_ifs <;> positivity
  have hCw_le : Cw ≤ 25 * (Cw + 1) := by linarith
  have hweightedFinal :
      (∑ i, l i * (v i - AndersonAC.SolS78.localCubeMean d m z R v) ^ 2) ≤
        25 * (Cw + 1) * Lmax ^ (1 / 3 : ℝ) * Ltotal ^ (2 / 3 : ℝ) *
          cubeGradient d m Q v := by
    rw [hweightedReindex]
    calc
      _ ≤ Cw * Real.rpow Lmax (1 / 3 : ℝ) *
          Real.rpow Ltotal (2 / 3 : ℝ) * cubeGradient d m Q v := hweightedCube
      _ ≤ 25 * (Cw + 1) * Real.rpow Lmax (1 / 3 : ℝ) *
          Real.rpow Ltotal (2 / 3 : ℝ) * cubeGradient d m Q v := by
        apply mul_le_mul_of_nonneg_right
        · have hmul : Cw * (Real.rpow Lmax (1 / 3 : ℝ) *
              Real.rpow Ltotal (2 / 3 : ℝ)) ≤
              25 * (Cw + 1) * (Real.rpow Lmax (1 / 3 : ℝ) *
                Real.rpow Ltotal (2 / 3 : ℝ)) :=
            mul_le_mul_of_nonneg_right hCw_le hscale_nonneg
          calc
            Cw * Real.rpow Lmax (1 / 3 : ℝ) * Real.rpow Ltotal (2 / 3 : ℝ) =
                Cw * (Real.rpow Lmax (1 / 3 : ℝ) * Real.rpow Ltotal (2 / 3 : ℝ)) := by ring
            _ ≤ 25 * (Cw + 1) * (Real.rpow Lmax (1 / 3 : ℝ) *
                  Real.rpow Ltotal (2 / 3 : ℝ)) := hmul
            _ = 25 * (Cw + 1) * Real.rpow Lmax (1 / 3 : ℝ) *
                  Real.rpow Ltotal (2 / 3 : ℝ) := by ring
        · exact hgrad_nonneg
      _ = 25 * (Cw + 1) * Lmax ^ (1 / 3 : ℝ) *
          Ltotal ^ (2 / 3 : ℝ) * cubeGradient d m Q v := by rfl
  have hzQ : z ∈ Q := by
    simp only [Q, cube, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    simp
    linarith [hR]
  let x₀ : CoordCube d (localCubeLength R) := e.symm ⟨z, hzQ⟩
  have hx₀ : localCubeToTorus z R x₀ = z := by
    have h := congrArg Subtype.val (e.apply_symm_apply ⟨z, hzQ⟩)
    calc
      localCubeToTorus z R x₀ = (e x₀).val := (heval x₀).symm
      _ = z := h
  have hpoint_le : ‖vC x₀ - μC‖ ^ 2 ≤ coordCubeNormSq (fun x => vC x - μC) := by
    unfold coordCubeNormSq
    exact Finset.single_le_sum (fun x hx => sq_nonneg ‖vC x - μC‖)
      (Finset.mem_univ x₀)
  have hlen_real : (localCubeLength R : ℝ) ≤ 5 * R := by
    have hr := localCubeRadius_le R hR
    unfold localCubeLength
    push_cast
    nlinarith [hr, hR]
  have hlen_sq : (localCubeLength R : ℝ) ^ 2 ≤ 25 * R ^ 2 := by
    nlinarith [sq_nonneg ((localCubeLength R : ℝ) - 5 * R)]
  have hpoint :
      (v z - AndersonAC.SolS78.localCubeMean d m z R v) ^ 2 ≤
        Cw * (localCubeLength R : ℝ) ^ 2 * coordCubeEnergy vC := by
    have hcenter : ‖vC x₀ - μC‖ ^ 2 =
        (v z - AndersonAC.SolS78.localCubeMean d m z R v) ^ 2 := by
      rw [hmean]
      change ‖(v (localCubeToTorus z R x₀) : ℂ) -
          (AndersonAC.SolS78.localCubeMean d m z R v : ℂ)‖ ^ 2 = _
      rw [hx₀]
      have hcast :
          ((v z - AndersonAC.SolS78.localCubeMean d m z R v : ℝ) : ℂ) =
            (v z : ℂ) - (AndersonAC.SolS78.localCubeMean d m z R v : ℂ) := by
        push_cast
        rfl
      rw [← hcast, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [← hcenter]
    calc
      ‖vC x₀ - μC‖ ^ 2 ≤ coordCubeNormSq (fun x => vC x - μC) := hpoint_le
      _ ≤ Cw * (localCubeLength R : ℝ) ^ 2 * coordCubeEnergy vC := hcube.1
  have hpointFinal :
      (v z - AndersonAC.SolS78.localCubeMean d m z R v) ^ 2 ≤
        25 * (Cw + 1) * R ^ 2 * cubeGradient d m Q v := by
    calc
      _ ≤ Cw * (localCubeLength R : ℝ) ^ 2 * coordCubeEnergy vC := hpoint
      _ ≤ Cw * (25 * R ^ 2) * coordCubeEnergy vC := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hlen_sq (le_of_lt hCw)
        · exact hcoord_nonneg
      _ ≤ Cw * (25 * R ^ 2) * cubeGradient d m Q v := by
        apply mul_le_mul_of_nonneg_left hcoord_energy
        positivity
      _ ≤ 25 * (Cw + 1) * R ^ 2 * cubeGradient d m Q v := by
        apply mul_le_mul_of_nonneg_right
        · nlinarith [sq_nonneg R]
        · exact hgrad_nonneg
  exact ⟨by simpa using hweightedFinal, by simpa using hpointFinal⟩

end AndersonAC.SolS78Deviation

#print axioms AndersonAC.SolS78Deviation.localDeviationInput_of_weightedCube
