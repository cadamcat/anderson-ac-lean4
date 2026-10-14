import AndersonAC.S78Local.Algebra
import AndersonAC.S78Local.Coordinates

open scoped BigOperators

noncomputable section

namespace AndersonAC.SolS78Local

open AndersonAC.S78

def coordCubeMean {d l : ℕ} (v : CoordCube d l → ℂ) : ℂ :=
  (Fintype.card (CoordCube d l) : ℂ)⁻¹ * ∑ i, v i

def coordCubeNormSq {d l : ℕ} (v : CoordCube d l → ℂ) : ℝ :=
  ∑ i, ‖v i‖ ^ 2

/-- Raw type of `AndersonAC.S3.weighted_cube`, including its unweighted
Poincare conjunct. The aliases above unfold to S3's concrete cube definitions. -/
def S3WeightedCubeStatement (d : ℕ) : Prop :=
  ∃ Cw : ℝ, 0 < Cw ∧ ∀ (l : ℕ), 1 ≤ l →
    ∀ (v : CoordCube d l → ℂ) (a : CoordCube d l → ℝ),
      (∀ i, 0 ≤ a i) →
      coordCubeNormSq (fun i => v i - coordCubeMean v) ≤ Cw * (l : ℝ) ^ 2 * coordCubeEnergy v ∧
      (∑ i, a i * ‖v i - coordCubeMean v‖ ^ 2) ≤
        Cw * Real.rpow (sSup (Set.range a)) (1 / 3 : ℝ) *
          Real.rpow (∑ i, a i) (2 / 3 : ℝ) * coordCubeEnergy v

theorem weighted_local_energy_of_cube_endpoint (d : ℕ) (_hd : 3 ≤ d)
    (hCube : S3WeightedCubeStatement d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (z : Torus d m) (R b Lmax Ltotal : ℝ)
      (A : Finset (Torus d m)) (w : Matrix (Torus d m) (Torus d m) ℝ)
      (α v : Torus d m → ℝ),
      1 ≤ R → 4 * R < (OAI.Anderson.sideLength m : ℝ) → 0 < b → 0 ≤ Lmax → 0 ≤ Ltotal →
      (∀ i j, 0 ≤ w i j ∧ w i j = w j i) →
      (∀ i j, i ∉ cube d m z R ∩ A ∨ j ∉ cube d m z R ∩ A → w i j = 0) →
      (∀ i, (∑ j, w i j) ≤ Lmax) → (∑ i, ∑ j, w i j) ≤ Ltotal →
      (∑ i, ∑ j, w i j * ((α i + v i) - (α j + v j)) ^ 2) ≤
        C * (Lmax + b * Lmax ^ (1 / 3 : ℝ) * Ltotal ^ (2 / 3 : ℝ)) *
          ((∑ i ∈ cube d m z (2 * R) ∩ A, (α i) ^ 2) +
            b⁻¹ * cubeGradient d m (cube d m z (2 * R)) v) := by
  classical
  rcases hCube with ⟨Cw, hCw, hCubeBounds⟩
  have hCubeBound : ∀ (l : ℕ), 1 ≤ l →
      ∀ (v : CoordCube d l → ℂ) (a : CoordCube d l → ℝ),
        (∀ i, 0 ≤ a i) →
        (∑ i, a i * ‖v i - coordCubeMean v‖ ^ 2) ≤
          Cw * Real.rpow (sSup (Set.range a)) (1 / 3 : ℝ) *
            Real.rpow (∑ i, a i) (2 / 3 : ℝ) * coordCubeEnergy v := by
    intro l hl v a ha
    exact (hCubeBounds l hl v a ha).2
  refine ⟨8 * (Cw + 1), by positivity, ?_⟩
  intro m z R b Lmax Ltotal A w α v hR hside hb hLmax hLtotal hweight hsupport hrow htotal
  let S : Finset (Torus d m) := cube d m z R ∩ A
  let Q : Finset (Torus d m) := cube d m z (2 * R)
  let ρ : Torus d m → ℝ := fun i => ∑ j, w i j
  have hnonneg : ∀ i j, 0 ≤ w i j := fun i j => (hweight i j).1
  have hsymm : ∀ i j, w i j = w j i := fun i j => (hweight i j).2
  have hSQ : S ⊆ Q := by
    intro i hi
    have hiCube : i ∈ cube d m z R := (Finset.mem_inter.mp hi).1
    simp only [Q, cube, Finset.mem_filter, Finset.mem_univ, true_and] at hiCube ⊢
    intro j
    have hh := hiCube j
    linarith
  have hSQA : S ⊆ Q ∩ A := by
    intro i hi
    exact Finset.mem_inter.mpr ⟨hSQ hi, (Finset.mem_inter.mp hi).2⟩
  have hrow_nonneg (i : Torus d m) : 0 ≤ ρ i := by
    exact rowSum_nonneg w hnonneg i
  have hrow_zero (i : Torus d m) (hi : i ∉ S) : ρ i = 0 := by
    exact rowSum_eq_zero_of_supported w hsupport i hi
  have hrow_zero_outside_Q (i : Torus d m) (hi : i ∉ Q) : ρ i = 0 :=
    hrow_zero i (by
      intro hiS
      exact hi (hSQ hiS))
  have hrow_sum_Q : (∑ i ∈ Q, ρ i) = ∑ i, ρ i := by
    apply Finset.sum_subset (s₁ := Q) (s₂ := Finset.univ)
    · exact Finset.subset_univ _
    · intro i hiQ hiNot
      simp [hrow_zero_outside_Q i hiNot]
  have hrow_total : (∑ i, ρ i) ≤ Ltotal := by
    simpa [ρ] using htotal
  let e := localCubeEquiv z R hR hside
  let vC : CoordCube d (localCubeLength R) → ℂ :=
    fun x => (v (localCubeToTorus z R x) : ℂ)
  let ρC : CoordCube d (localCubeLength R) → ℝ :=
    fun x => ρ (localCubeToTorus z R x)
  let μC : ℂ := coordCubeMean vC
  have heval (x : CoordCube d (localCubeLength R)) :
      (e x).val = localCubeToTorus z R x := rfl
  have hlen : 1 ≤ localCubeLength R := by
    unfold localCubeLength localCubeRadius
    omega
  have hρC_nonneg : ∀ x, 0 ≤ ρC x := fun x => hrow_nonneg _
  have hρC_sum : (∑ x, ρC x) ≤ Ltotal := by
    calc
      (∑ x, ρC x) = ∑ x, ρ (e x).val := by
        apply Finset.sum_congr rfl
        intro x _
        simp [ρC, heval]
      _ = ∑ x : localCubeDomain z R, ρ x.val :=
        Equiv.sum_comp e (fun x : localCubeDomain z R => ρ x.val)
      _ = ∑ x ∈ Q, ρ x := by
        simpa [Q] using localCubeDomain_sum z R ρ
      _ = ∑ x, ρ x := hrow_sum_Q
      _ ≤ Ltotal := hrow_total
  have hqrange_ne : (Set.range ρC).Nonempty := ⟨ρC (fun _ => ⟨0, by omega⟩),
    ⟨fun _ => ⟨0, by omega⟩, rfl⟩⟩
  have hqrange_bdd : BddAbove (Set.range ρC) := (Set.finite_range ρC).bddAbove
  have hsup_le : sSup (Set.range ρC) ≤ Lmax := by
    apply csSup_le hqrange_ne
    rintro y ⟨x, rfl⟩
    exact hrow (localCubeToTorus z R x)
  have hqrange_nonneg : 0 ≤ sSup (Set.range ρC) := by
    rcases hqrange_ne with ⟨a, ha⟩
    have hle := le_csSup hqrange_bdd ha
    rcases ha with ⟨x, rfl⟩
    exact le_trans (hρC_nonneg x) hle
  have hsum_nonneg : 0 ≤ ∑ x, ρC x := Finset.sum_nonneg fun x hx => hρC_nonneg x
  have hsup_pow : Real.rpow (sSup (Set.range ρC)) (1 / 3 : ℝ) ≤
      Real.rpow Lmax (1 / 3 : ℝ) :=
    Real.rpow_le_rpow hqrange_nonneg hsup_le (by norm_num)
  have hsum_pow : Real.rpow (∑ x, ρC x) (2 / 3 : ℝ) ≤
      Real.rpow Ltotal (2 / 3 : ℝ) :=
    Real.rpow_le_rpow hsum_nonneg hρC_sum (by norm_num)
  have hcube_local := hCubeBound (localCubeLength R) hlen vC ρC hρC_nonneg
  have hcoord_energy_nonneg : 0 ≤ coordCubeEnergy vC := by
    unfold coordCubeEnergy
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro x hx
    apply Finset.sum_nonneg
    intro y hy
    split_ifs <;> positivity
  have hcoord_energy := coordCubeEnergy_le_cubeGradient z R hR hside v
  have hcoef_nonneg : 0 ≤ Cw * Real.rpow Lmax (1 / 3 : ℝ) *
      Real.rpow Ltotal (2 / 3 : ℝ) := by
    exact mul_nonneg
      (mul_nonneg (le_of_lt hCw) (Real.rpow_nonneg hLmax _))
      (Real.rpow_nonneg hLtotal _)
  have hvariance_cube :
      (∑ x, ρC x * ‖vC x - μC‖ ^ 2) ≤
        Cw * Real.rpow Lmax (1 / 3 : ℝ) * Real.rpow Ltotal (2 / 3 : ℝ) *
          cubeGradient d m Q v := by
    calc
      (∑ x, ρC x * ‖vC x - μC‖ ^ 2) ≤
          Cw * Real.rpow (sSup (Set.range ρC)) (1 / 3 : ℝ) *
            Real.rpow (∑ x, ρC x) (2 / 3 : ℝ) * coordCubeEnergy vC := hcube_local
      _ ≤ Cw * Real.rpow Lmax (1 / 3 : ℝ) * Real.rpow Ltotal (2 / 3 : ℝ) *
          coordCubeEnergy vC := by
            have hA :
                Cw * Real.rpow (sSup (Set.range ρC)) (1 / 3 : ℝ) *
                  Real.rpow (∑ x, ρC x) (2 / 3 : ℝ) ≤
                Cw * Real.rpow Lmax (1 / 3 : ℝ) * Real.rpow Ltotal (2 / 3 : ℝ) := by
              calc
                _ ≤ Cw * Real.rpow Lmax (1 / 3 : ℝ) *
                    Real.rpow (∑ x, ρC x) (2 / 3 : ℝ) := by
                      apply mul_le_mul_of_nonneg_right
                      · exact mul_le_mul_of_nonneg_left hsup_pow (le_of_lt hCw)
                      · exact Real.rpow_nonneg hsum_nonneg _
                _ ≤ Cw * Real.rpow Lmax (1 / 3 : ℝ) * Real.rpow Ltotal (2 / 3 : ℝ) := by
                      apply mul_le_mul_of_nonneg_left hsum_pow
                      exact mul_nonneg (le_of_lt hCw) (Real.rpow_nonneg hLmax _)
            exact mul_le_mul_of_nonneg_right hA hcoord_energy_nonneg
      _ ≤ Cw * Real.rpow Lmax (1 / 3 : ℝ) * Real.rpow Ltotal (2 / 3 : ℝ) *
          cubeGradient d m Q v := by
            exact mul_le_mul_of_nonneg_left hcoord_energy hcoef_nonneg
  have hvariance_global :
      (∑ i, ρ i * ‖(v i : ℂ) - μC‖ ^ 2) =
        ∑ x, ρC x * ‖vC x - μC‖ ^ 2 := by
    let f : Torus d m → ℝ := fun i => ρ i * ‖(v i : ℂ) - μC‖ ^ 2
    have hglobalQ : (∑ i, f i) = ∑ i ∈ Q, f i := by
      symm
      apply Finset.sum_subset (s₁ := Q) (s₂ := Finset.univ)
      · exact Finset.subset_univ _
      · intro i hiQ hiNot
        simp [f, hrow_zero_outside_Q i hiNot]
    have hdomain : (∑ x : localCubeDomain z R, f x.val) = ∑ i ∈ Q, f i :=
      localCubeDomain_sum z R f
    have hcoord : (∑ x, ρC x * ‖vC x - μC‖ ^ 2) =
        ∑ x : localCubeDomain z R, f x.val := by
      calc
        (∑ x, ρC x * ‖vC x - μC‖ ^ 2) =
            ∑ x, f (e x).val := by
              apply Finset.sum_congr rfl
              intro x _
              simp [f, ρC, vC, heval]
        _ = ∑ x : localCubeDomain z R, f x.val :=
              Equiv.sum_comp e (fun x : localCubeDomain z R => f x.val)
    exact hglobalQ.trans (hdomain.symm.trans hcoord.symm)
  have hvar := hvariance_global ▸ hvariance_cube
  have halpha := pairEnergy_le_local_terms w α Lmax hnonneg hsymm hsupport hrow
  have hsplit : pairEnergy w (fun i => α i + v i) ≤
      2 * pairEnergy w α + 2 * pairEnergy w v :=
    pairEnergy_add_le_two w α v hnonneg
  have hreal_complex : pairEnergy w v = complexPairEnergy w (fun i => (v i : ℂ)) := by
    unfold pairEnergy complexPairEnergy
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hcast : ((v i - v j : ℝ) : ℂ) = (v i : ℂ) - (v j : ℂ) := by
      push_cast
      rfl
    rw [← hcast, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hvpair := complexPairEnergy_le_four_rowVariance w
    (fun i => (v i : ℂ)) μC hnonneg hsymm
  have hvbound : pairEnergy w v ≤
      4 * Cw * Real.rpow Lmax (1 / 3 : ℝ) * Real.rpow Ltotal (2 / 3 : ℝ) *
        cubeGradient d m Q v := by
    rw [hreal_complex]
    calc
      complexPairEnergy w (fun i => (v i : ℂ)) ≤
          4 * ∑ i, ρ i * ‖(v i : ℂ) - μC‖ ^ 2 := hvpair
      _ ≤ 4 * (Cw * Real.rpow Lmax (1 / 3 : ℝ) *
          Real.rpow Ltotal (2 / 3 : ℝ) * cubeGradient d m Q v) := by
            gcongr
      _ = 4 * Cw * Real.rpow Lmax (1 / 3 : ℝ) * Real.rpow Ltotal (2 / 3 : ℝ) *
          cubeGradient d m Q v := by ring
  let αsq : ℝ := ∑ i ∈ Q ∩ A, (α i) ^ 2
  let grad : ℝ := cubeGradient d m Q v
  let scale : ℝ := Real.rpow Lmax (1 / 3 : ℝ) * Real.rpow Ltotal (2 / 3 : ℝ)
  have hα_nonneg : 0 ≤ αsq := by
    dsimp [αsq]
    exact Finset.sum_nonneg fun i hi => sq_nonneg (α i)
  have hgrad_nonneg : 0 ≤ grad := by
    dsimp [grad, cubeGradient]
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    split_ifs <;> positivity
  have hscale_nonneg : 0 ≤ scale := by
    dsimp [scale]
    exact mul_nonneg (Real.rpow_nonneg hLmax _) (Real.rpow_nonneg hLtotal _)
  have halpha_local :
      pairEnergy w α ≤ 4 * Lmax * αsq := by
    have hsubset := hSQA
    calc
      pairEnergy w α ≤ 4 * Lmax * ∑ i ∈ S, (α i) ^ 2 := halpha
      _ ≤ 4 * Lmax * ∑ i ∈ Q ∩ A, (α i) ^ 2 := by
        gcongr
      _ = 4 * Lmax * αsq := by rfl
  have hlocal : pairEnergy w (fun i => α i + v i) ≤
      8 * Lmax * αsq + 8 * Cw * scale * grad := by
    have hvscaled : pairEnergy w v ≤ 4 * Cw * scale * grad := by
      calc
        pairEnergy w v ≤ 4 * Cw * Real.rpow Lmax (1 / 3 : ℝ) *
            Real.rpow Ltotal (2 / 3 : ℝ) * cubeGradient d m Q v := hvbound
        _ = 4 * Cw * (Real.rpow Lmax (1 / 3 : ℝ) *
            Real.rpow Ltotal (2 / 3 : ℝ)) * cubeGradient d m Q v := by ring
        _ = 4 * Cw * scale * grad := by rfl
    calc
      pairEnergy w (fun i => α i + v i) ≤ 2 * pairEnergy w α + 2 * pairEnergy w v := hsplit
      _ ≤ 2 * (4 * Lmax * αsq) +
          2 * (4 * Cw * scale * grad) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left halpha_local (by norm_num))
              (mul_le_mul_of_nonneg_left hvscaled (by norm_num))
      _ = 8 * Lmax * αsq + 8 * Cw * scale * grad := by ring
  let C : ℝ := 8 * (Cw + 1)
  have hC₁ : 8 ≤ C := by dsimp [C]; linarith
  have hC₂ : 8 * Cw ≤ C := by dsimp [C]; linarith
  have htarget_lower : C * Lmax * αsq + C * scale * grad ≤
      C * (Lmax + b * scale) * (αsq + b⁻¹ * grad) := by
    have hbInv : b * b⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hb)
    have hExpand :
        C * (Lmax + b * scale) * (αsq + b⁻¹ * grad) =
          C * Lmax * αsq + C * Lmax * b⁻¹ * grad +
            C * b * scale * αsq + C * scale * grad := by
      calc
        _ = C * Lmax * αsq + C * Lmax * b⁻¹ * grad +
            C * b * scale * αsq + C * b * scale * b⁻¹ * grad := by ring
        _ = C * Lmax * αsq + C * Lmax * b⁻¹ * grad +
            C * b * scale * αsq + C * scale * grad := by
              congr 1
              calc
                C * b * scale * b⁻¹ * grad = C * scale * (b * b⁻¹) * grad := by ring
                _ = C * scale * grad := by rw [hbInv, mul_one]
    rw [hExpand]
    have hcross₁ : 0 ≤ C * Lmax * b⁻¹ * grad := by positivity
    have hcross₂ : 0 ≤ C * b * scale * αsq := by positivity
    linarith
  have hfinal_local : pairEnergy w (fun i => α i + v i) ≤
      C * Lmax * αsq + C * scale * grad := by
    have hterms₁ : 8 * Lmax * αsq ≤ C * Lmax * αsq := by
      calc
        8 * Lmax * αsq = 8 * (Lmax * αsq) := by ring
        _ ≤ C * (Lmax * αsq) := mul_le_mul_of_nonneg_right hC₁ (mul_nonneg hLmax hα_nonneg)
        _ = C * Lmax * αsq := by ring
    have hterms₂ : 8 * Cw * scale * grad ≤ C * scale * grad := by
      calc
        8 * Cw * scale * grad = 8 * Cw * (scale * grad) := by ring
        _ ≤ C * (scale * grad) :=
          mul_le_mul_of_nonneg_right hC₂ (mul_nonneg hscale_nonneg hgrad_nonneg)
        _ = C * scale * grad := by ring
    linarith [hlocal]
  calc
    pairEnergy w (fun i => α i + v i) ≤ C * Lmax * αsq + C * scale * grad := hfinal_local
    _ ≤ C * (Lmax + b * scale) * (αsq + b⁻¹ * grad) := htarget_lower
    _ = 8 * (Cw + 1) *
        (Lmax + b * Lmax ^ (1 / 3 : ℝ) * Ltotal ^ (2 / 3 : ℝ)) *
          ((∑ i ∈ cube d m z (2 * R) ∩ A, (α i) ^ 2) +
            b⁻¹ * cubeGradient d m (cube d m z (2 * R)) v) := by
          dsimp [C, scale, αsq, grad, Q]
          ring

end AndersonAC.SolS78Local
