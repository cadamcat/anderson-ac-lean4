import AndersonAC.S3H.Lattice
import AndersonAC.S78AnchorTail.Proof

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.SolS78

open AndersonAC.S78

private theorem torusDistance_le_graphDistance (d m : ℕ) (x y : Torus d m) :
    (AndersonAC.S3.torusDistance x y : ℝ) ≤
      (d : ℝ) * physicalDistance d m x y := by
  calc
    (AndersonAC.S3.torusDistance x y : ℝ) =
        ∑ q : Fin d, ((AndersonAC.S3.coordMin x y q : ℕ) : ℝ) := by
          rw [AndersonAC.S3.torusDistance_eq_sum]
          simp
    _ ≤ ∑ q : Fin d, physicalDistance d m x y := by
      apply Finset.sum_le_sum
      intro q hq
      have hq' := AndersonAC.SolS78AnchorTail.coordNat_le_physicalDistance q x y
      simpa [AndersonAC.S3.coordMin] using hq'
    _ = (d : ℝ) * physicalDistance d m x y := by simp

/-- The S3 torus moment controls the graph-distance exponential sum used for
the far assembly increments. The estimate is uniform in the torus size. -/
theorem graph_exponential_moment (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : 0 < γ) :
    ∃ M t₀ : ℝ, 0 < M ∧ 0 < t₀ ∧
      ∀ (m : ℕ), 4 ≤ OAI.Anderson.sideLength m →
        ∀ x : Torus d m, ∀ t : ℝ, 0 < t → t < t₀ →
          (∑ y, Real.exp (-γ * t * physicalDistance d m x y)) ≤
            M * t ^ (-(d : ℝ)) := by
  have hdReal : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨cL, CL, hcL, hCL, hcount⟩ :=
    AndersonAC.S3.lattice_counting_proof (d := d) hd
  let α : ℝ := γ / (d : ℝ)
  let t₀ : ℝ := min 1 ((d : ℝ) / γ)
  let M : ℝ := CL * α ^ (-(d : ℝ))
  have hα : 0 < α := by
    dsimp [α]
    exact div_pos hγ hdReal
  have ht₀ : 0 < t₀ := by
    dsimp [t₀]
    exact lt_min (by norm_num) (div_pos hdReal hγ)
  have hM : 0 < M := by
    dsimp [M]
    exact mul_pos hCL (Real.rpow_pos_of_pos hα _)
  refine ⟨M, t₀, hM, ht₀, ?_⟩
  intro m hm x t ht ht₀small
  let u : ℝ := α * t
  have ht1 : t ≤ 1 := le_of_lt (lt_of_lt_of_le ht₀small (min_le_left _ _))
  have htd : t < (d : ℝ) / γ := lt_of_lt_of_le ht₀small (min_le_right _ _)
  have huPos : 0 < u := mul_pos hα ht
  have huLe : u ≤ 1 := by
    calc
      u = γ * t / (d : ℝ) := by dsimp [u, α]; ring
      _ ≤ 1 := (div_le_iff₀ hdReal).2 (by
        have hmul := (lt_div_iff₀ hγ).1 htd
        nlinarith [hmul])
  have huEq : u = (α * t) := rfl
  have hL : NeZero (OAI.Anderson.sideLength m) := inferInstance
  have hmoment := (hcount (OAI.Anderson.sideLength m) hm).2.2 x u 0 huPos huLe (by norm_num)
  have hmoment' :
      (∑ y, Real.exp (-u * (AndersonAC.S3.torusDistance x y : ℝ))) ≤
        CL * u ^ (-(d : ℤ)) := by
    simpa [AndersonAC.S3.exponentialMoment] using hmoment
  have hpow : u ^ (-(d : ℤ)) = α ^ (-(d : ℝ)) * t ^ (-(d : ℝ)) := by
    calc
      u ^ (-(d : ℤ)) = u ^ (-(d : ℝ)) :=
        by simpa only [Int.cast_neg, Int.cast_natCast] using
          (Real.rpow_intCast u (-(d : ℤ))).symm
      _ = (α * t) ^ (-(d : ℝ)) := by rw [huEq]
      _ = α ^ (-(d : ℝ)) * t ^ (-(d : ℝ)) :=
        Real.mul_rpow hα.le ht.le
  have hdist (y : Torus d m) :
      -γ * t * physicalDistance d m x y ≤
        -u * (AndersonAC.S3.torusDistance x y : ℝ) := by
    have hbase := torusDistance_le_graphDistance d m x y
    have hbase' : (AndersonAC.S3.torusDistance x y : ℝ) / (d : ℝ) ≤
        physicalDistance d m x y := by
      apply (div_le_iff₀ hdReal).2
      nlinarith [hbase]
    have hmul := mul_le_mul_of_nonneg_left hbase' (mul_nonneg hγ.le ht.le)
    have hcoeff : u * (AndersonAC.S3.torusDistance x y : ℝ) =
        γ * t * ((AndersonAC.S3.torusDistance x y : ℝ) / (d : ℝ)) := by
      dsimp [u, α]
      field_simp [hdReal.ne']
    nlinarith [hmul]
  have hsum :
      (∑ y : Torus d m, Real.exp (-γ * t * physicalDistance d m x y)) ≤
        ∑ y : Torus d m, Real.exp (-u * (AndersonAC.S3.torusDistance x y : ℝ)) :=
    Finset.sum_le_sum (s := Finset.univ) (fun y hy => Real.exp_le_exp.mpr (hdist y))
  have hgraph :
      (∑ y, Real.exp (-γ * t * physicalDistance d m x y)) ≤
        CL * u ^ (-(d : ℤ)) := by
    calc
      _ ≤ ∑ y, Real.exp (-u * (AndersonAC.S3.torusDistance x y : ℝ)) := hsum
      _ ≤ CL * u ^ (-(d : ℤ)) := hmoment'
  calc
    (∑ y, Real.exp (-γ * t * physicalDistance d m x y)) ≤
        CL * u ^ (-(d : ℤ)) := hgraph
    _ = M * t ^ (-(d : ℝ)) := by
      rw [hpow]
      dsimp [M]
      ring

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.graph_exponential_moment
