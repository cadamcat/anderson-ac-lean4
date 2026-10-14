import AndersonAC.S78.Definitions
import AndersonAC.S78.VariationalInputs

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.SolS78
open AndersonAC.S78

namespace SpatialForm

def cost {ι : Type} [Fintype ι] (G : SimpleGraph ι) (A : Finset ι) (b : ℝ)
    (α v : ι → ℝ) : ℝ :=
  (∑ i ∈ A, (α i) ^ 2) + b⁻¹ * gradientEnergy G v

def candidates {ι : Type} [Fintype ι] (G : SimpleGraph ι) (A : Finset ι)
    (b : ℝ) (f : ι → ℝ) : Set ℝ :=
  {e | ∃ α v : ι → ℝ, (∀ i ∈ A, f i = α i + v i) ∧ e = cost G A b α v}

lemma gradientEnergy_nonneg {ι : Type} [Fintype ι] (G : SimpleGraph ι) (v : ι → ℝ) :
    0 ≤ gradientEnergy G v := by
  classical
  unfold gradientEnergy
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  by_cases h : G.Adj i j <;> simp [h, sq_nonneg]

lemma squares_nonneg {ι : Type} (A : Finset ι) (v : ι → ℝ) :
    0 ≤ ∑ i ∈ A, (v i) ^ 2 :=
  Finset.sum_nonneg fun i hi => sq_nonneg _

lemma cost_nonneg {ι : Type} [Fintype ι] (G : SimpleGraph ι) (A : Finset ι)
    (b : ℝ) (hb : 0 < b) (α v : ι → ℝ) : 0 ≤ cost G A b α v := by
  unfold cost
  exact add_nonneg (squares_nonneg A α)
    (mul_nonneg (inv_nonneg.mpr hb.le) (gradientEnergy_nonneg G v))

lemma candidates_nonempty {ι : Type} [Fintype ι] (G : SimpleGraph ι) (A : Finset ι)
    (b : ℝ) (f : ι → ℝ) : (candidates G A b f).Nonempty := by
  refine ⟨cost G A b (fun _ => 0) f, ?_⟩
  refine ⟨fun _ => 0, f, ?_, rfl⟩
  intro i hi
  ring

lemma candidates_nonneg {ι : Type} [Fintype ι] (G : SimpleGraph ι) (A : Finset ι)
    (b : ℝ) (hb : 0 < b) (f : ι → ℝ) : ∀ e ∈ candidates G A b f, 0 ≤ e := by
  rintro e ⟨α, v, hmatch, rfl⟩
  exact cost_nonneg G A b hb α v

lemma candidates_bddBelow {ι : Type} [Fintype ι] (G : SimpleGraph ι) (A : Finset ι)
    (b : ℝ) (hb : 0 < b) (f : ι → ℝ) : BddBelow (candidates G A b f) := by
  refine ⟨0, ?_⟩
  intro e he
  exact candidates_nonneg G A b hb f e he

lemma spatialEnergy_eq_csInf {ι : Type} [Fintype ι] (G : SimpleGraph ι)
    (A : Finset ι) (b : ℝ) (f : ι → ℝ) :
    spatialEnergy G A b f = sInf (candidates G A b f) := by
  rfl

lemma spatialEnergy_nonneg {ι : Type} [Fintype ι] (G : SimpleGraph ι)
    (A : Finset ι) (b : ℝ) (hb : 0 < b) (f : ι → ℝ) :
    0 ≤ spatialEnergy G A b f := by
  rw [spatialEnergy_eq_csInf]
  exact le_csInf (candidates_nonempty G A b f) (candidates_nonneg G A b hb f)

lemma gradientEdge_sq_le {ι : Type} [Fintype ι] (G : SimpleGraph ι)
    (v : ι → ℝ) {i j : ι} (hij : G.Adj i j) :
    (v i - v j) ^ 2 ≤ 2 * gradientEnergy G v := by
  classical
  have hinner :
      (if G.Adj i j then (v i - v j) ^ 2 else 0) ≤
        ∑ j, if G.Adj i j then (v i - v j) ^ 2 else 0 := by
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun k => if G.Adj i k then (v i - v k) ^ 2 else 0)
      (fun k hk => by
        by_cases h : G.Adj i k <;> simp [h, sq_nonneg]) (Finset.mem_univ j)
  have houter :
      (∑ j, if G.Adj i j then (v i - v j) ^ 2 else 0) ≤
        ∑ i, ∑ j, if G.Adj i j then (v i - v j) ^ 2 else 0 := by
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun k => ∑ l, if G.Adj k l then (v k - v l) ^ 2 else 0)
      (fun k hk => Finset.sum_nonneg fun l hl => by
        by_cases h : G.Adj k l <;> simp [h, sq_nonneg]) (Finset.mem_univ i)
  have hsum := le_trans hinner houter
  have hterm : (if G.Adj i j then (v i - v j) ^ 2 else 0) = (v i - v j) ^ 2 := if_pos hij
  calc
    (v i - v j) ^ 2 ≤ ∑ i, ∑ j, if G.Adj i j then (v i - v j) ^ 2 else 0 := by
      simpa [hterm] using hsum
    _ = 2 * gradientEnergy G v := by
      unfold gradientEnergy
      ring

lemma walk_abs_sub_le {ι : Type} {G : SimpleGraph ι} {u v : ι}
    (p : G.Walk u v) (f : ι → ℝ) (ε : ℝ)
    (hedge : ∀ a b, G.Adj a b → |f a - f b| ≤ ε) :
    |f u - f v| ≤ (p.length : ℝ) * ε := by
  induction p with
  | nil => simp
  | @cons u v w huv tail ih =>
      have hstep := hedge u v huv
      have hdecomp : f u - f w = (f u - f v) + (f v - f w) := by ring
      rw [hdecomp, SimpleGraph.Walk.length_cons]
      calc
        |(f u - f v) + (f v - f w)| ≤ |f u - f v| + |f v - f w| := abs_add_le _ _
        _ ≤ ε + (tail.length : ℝ) * ε := add_le_add hstep ih
        _ = ((tail.length : ℝ) + 1) * ε := by ring
        _ = ((tail.length + 1 : ℕ) : ℝ) * ε := by norm_cast

lemma connected_variation_bound {ι : Type} [Fintype ι] (G : SimpleGraph ι)
    (hG : G.Connected) (v : ι → ℝ) (i j : ι) :
    |v i - v j| ≤ (Fintype.card ι : ℝ) * Real.sqrt (2 * gradientEnergy G v) := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist i j
  have hpPath : p.IsPath := p.isPath_of_length_eq_dist hp
  have hlen : (p.length : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Nat.le_of_lt hpPath.length_lt
  have hedge : ∀ a b, G.Adj a b →
      |v a - v b| ≤ Real.sqrt (2 * gradientEnergy G v) := by
    intro a b hab
    have hs := Real.sqrt_le_sqrt (gradientEdge_sq_le G v hab)
    simpa [Real.sqrt_sq_eq_abs] using hs
  calc
    |v i - v j| ≤ (p.length : ℝ) * Real.sqrt (2 * gradientEnergy G v) :=
      walk_abs_sub_le p v _ hedge
    _ ≤ (Fintype.card ι : ℝ) * Real.sqrt (2 * gradientEnergy G v) :=
      mul_le_mul_of_nonneg_right hlen (Real.sqrt_nonneg _)

lemma gradientEnergy_scale {ι : Type} [Fintype ι] (G : SimpleGraph ι)
    (s : ℝ) (v : ι → ℝ) :
    gradientEnergy G (fun i => s * v i) = s ^ 2 * gradientEnergy G v := by
  classical
  have hterm (i j : ι) :
      (if G.Adj i j then (s * v i - s * v j) ^ 2 else 0) =
        s ^ 2 * (if G.Adj i j then (v i - v j) ^ 2 else 0) := by
    by_cases h : G.Adj i j
    · simp [h, ← mul_sub, mul_pow]
    · simp [h]
  have hsum :
      (∑ i, ∑ j, if G.Adj i j then (s * v i - s * v j) ^ 2 else 0) =
        s ^ 2 * ∑ i, ∑ j, if G.Adj i j then (v i - v j) ^ 2 else 0 := by
    calc
      _ = ∑ i, s ^ 2 * ∑ j, if G.Adj i j then (v i - v j) ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          _ = ∑ j, s ^ 2 * (if G.Adj i j then (v i - v j) ^ 2 else 0) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hterm i j
          _ = s ^ 2 * ∑ j, if G.Adj i j then (v i - v j) ^ 2 else 0 := by
            rw [← Finset.mul_sum]
      _ = s ^ 2 * ∑ i, ∑ j, if G.Adj i j then (v i - v j) ^ 2 else 0 := by
        rw [← Finset.mul_sum]
  unfold gradientEnergy
  rw [hsum]
  ring

lemma cost_scale {ι : Type} [Fintype ι] (G : SimpleGraph ι) (A : Finset ι)
    (b s : ℝ) (α v : ι → ℝ) :
    cost G A b (fun i => s * α i) (fun i => s * v i) = s ^ 2 * cost G A b α v := by
  unfold cost
  have hsum : (∑ i ∈ A, (s * α i) ^ 2) = s ^ 2 * ∑ i ∈ A, (α i) ^ 2 := by
    calc
      _ = ∑ i ∈ A, s ^ 2 * (α i) ^ 2 := by congr 2 <;> simp [mul_pow]
      _ = s ^ 2 * ∑ i ∈ A, (α i) ^ 2 := by rw [← Finset.mul_sum]
  rw [hsum, gradientEnergy_scale]
  ring

lemma candidates_scale {ι : Type} [Fintype ι] (G : SimpleGraph ι) (A : Finset ι)
    (b s : ℝ) (hs : s ≠ 0) (f : ι → ℝ) :
    candidates G A b (fun i => s * f i) = Set.image (fun x => s ^ 2 * x) (candidates G A b f) := by
  ext e
  simp only [Set.mem_image]
  constructor
  · rintro ⟨α, v, hmatch, rfl⟩
    let α₀ : ι → ℝ := fun i => α i / s
    let v₀ : ι → ℝ := fun i => v i / s
    have hα : (fun i => s * α₀ i) = α := by
      funext i
      dsimp [α₀]
      field_simp
    have hv : (fun i => s * v₀ i) = v := by
      funext i
      dsimp [v₀]
      field_simp
    have hmatch₀ : ∀ i ∈ A, f i = α₀ i + v₀ i := by
      intro i hi
      have h := hmatch i hi
      dsimp [α₀, v₀]
      calc
        f i = (s * f i) / s := by field_simp
        _ = (α i + v i) / s := by
          have h' : s * f i = α i + v i := by simpa using h
          rw [h']
        _ = α i / s + v i / s := by ring
    refine ⟨cost G A b α₀ v₀, ⟨α₀, v₀, hmatch₀, rfl⟩, ?_⟩
    rw [← hα, ← hv]
    exact (cost_scale G A b s α₀ v₀).symm
  · rintro ⟨e, ⟨α, v, hmatch, rfl⟩, rfl⟩
    refine ⟨fun i => s * α i, fun i => s * v i, ?_, ?_⟩
    · intro i hi
      change s * f i = s * α i + s * v i
      rw [hmatch i hi]
      ring
    · exact (cost_scale G A b s α v).symm

lemma csInf_image_mul_pos (S : Set ℝ) (hne : S.Nonempty) (hbd : BddBelow S)
    (c : ℝ) (hc : 0 < c) :
    sInf (Set.image (fun x => c * x) S) = c * sInf S := by
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · rcases hne with ⟨x, hx⟩
    exact ⟨c * x, ⟨x, hx, rfl⟩⟩
  · intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hInf : sInf S ≤ x := csInf_le hbd hx
    exact mul_le_mul_of_nonneg_left hInf hc.le
  · intro z hz
    have hdiv : sInf S < z / c := by
      rw [lt_div_iff₀ hc]
      simpa [mul_comm] using hz
    obtain ⟨x, hx, hxlt⟩ := exists_lt_of_csInf_lt hne hdiv
    refine ⟨c * x, ⟨x, hx, rfl⟩, ?_⟩
    calc
      c * x < c * (z / c) := mul_lt_mul_of_pos_left hxlt hc
      _ = z := by field_simp [ne_of_gt hc]

lemma spatialEnergy_scale {ι : Type} [Fintype ι] (G : SimpleGraph ι)
    (A : Finset ι) (b : ℝ) (hb : 0 < b) (s : ℝ) (hs : s ≠ 0)
    (f : ι → ℝ) :
    spatialEnergy G A b (fun i => s * f i) = s ^ 2 * spatialEnergy G A b f := by
  rw [spatialEnergy_eq_csInf, spatialEnergy_eq_csInf, candidates_scale G A b s hs f]
  exact csInf_image_mul_pos (candidates G A b f) (candidates_nonempty G A b f)
    (candidates_bddBelow G A b hb f) (s ^ 2) (sq_pos_of_ne_zero hs)

lemma spatialEnergy_zero_of_const {ι : Type} [Fintype ι] (G : SimpleGraph ι)
    (A : Finset ι) (b : ℝ) (hb : 0 < b) (f : ι → ℝ) (c : ℝ)
    (hf : ∀ i ∈ A, f i = c) : spatialEnergy G A b f = 0 := by
  classical
  have hmem : 0 ∈ candidates G A b f := by
    refine ⟨fun _ => 0, fun _ => c, ?_, ?_⟩
    · intro i hi
      rw [hf i hi]
      ring
    · unfold cost gradientEnergy
      simp
  have hle : spatialEnergy G A b f ≤ 0 := by
    rw [spatialEnergy_eq_csInf]
    exact csInf_le (candidates_bddBelow G A b hb f) hmem
  exact le_antisymm hle (spatialEnergy_nonneg G A b hb f)

lemma cost_coordinate_le {ι : Type} [Fintype ι] (G : SimpleGraph ι)
    (A : Finset ι) (b : ℝ) (hb : 0 < b) (α v : ι → ℝ)
    {i : ι} (hi : i ∈ A) : (α i) ^ 2 ≤ cost G A b α v := by
  unfold cost
  calc
    _ ≤ ∑ j ∈ A, (α j) ^ 2 := by
      exact Finset.single_le_sum (s := A) (f := fun j => (α j) ^ 2)
        (fun j hj => sq_nonneg _) hi
    _ ≤ (∑ j ∈ A, (α j) ^ 2) + b⁻¹ * gradientEnergy G v :=
      le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr hb.le) (gradientEnergy_nonneg G v))

lemma cost_gradient_le {ι : Type} [Fintype ι] (G : SimpleGraph ι)
    (A : Finset ι) (b : ℝ) (hb : 0 < b) (α v : ι → ℝ) :
    gradientEnergy G v ≤ b * cost G A b α v := by
  have hsum := squares_nonneg A α
  have hgrad : b⁻¹ * gradientEnergy G v ≤ cost G A b α v := by
    unfold cost
    linarith
  calc
    gradientEnergy G v = b * (b⁻¹ * gradientEnergy G v) := by
      field_simp [ne_of_gt hb]
    _ ≤ b * cost G A b α v := mul_le_mul_of_nonneg_left hgrad hb.le

lemma cost_pair_sq_le {ι : Type} [Fintype ι] (G : SimpleGraph ι)
    (hG : G.Connected) (A : Finset ι) (b : ℝ) (hb : 0 < b)
    (α v f : ι → ℝ) (hmatch : ∀ i ∈ A, f i = α i + v i)
    {i j : ι} (hi : i ∈ A) (hj : j ∈ A) :
    (f i - f j) ^ 2 ≤ (2 + (Fintype.card ι : ℝ) * Real.sqrt (2 * b)) ^ 2 *
      cost G A b α v := by
  let e := cost G A b α v
  have he : 0 ≤ e := cost_nonneg G A b hb α v
  have heαi := cost_coordinate_le G A b hb α v hi
  have heαj := cost_coordinate_le G A b hb α v hj
  have hgrad := cost_gradient_le G A b hb α v
  have hαi : |α i| ≤ Real.sqrt e := by
    calc
      |α i| = Real.sqrt ((α i) ^ 2) := by rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt e := Real.sqrt_le_sqrt heαi
  have hαj : |α j| ≤ Real.sqrt e := by
    calc
      |α j| = Real.sqrt ((α j) ^ 2) := by rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt e := Real.sqrt_le_sqrt heαj
  have hvar₀ := connected_variation_bound G hG v i j
  have hvar₁ :
      |v i - v j| ≤ (Fintype.card ι : ℝ) * Real.sqrt (2 * b * e) := by
    apply le_trans hvar₀
    apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    apply Real.sqrt_le_sqrt
    nlinarith [hgrad, he, mul_nonneg hb.le he]
  have hvar :
      |v i - v j| ≤ (Fintype.card ι : ℝ) * Real.sqrt (2 * b) * Real.sqrt e := by
    have hsqrt : Real.sqrt (2 * b * e) = Real.sqrt (2 * b) * Real.sqrt e :=
      Real.sqrt_mul (by positivity) e
    calc
      |v i - v j| ≤ (Fintype.card ι : ℝ) * Real.sqrt (2 * b * e) := hvar₁
      _ = (Fintype.card ι : ℝ) * (Real.sqrt (2 * b) * Real.sqrt e) := by rw [hsqrt]
      _ = (Fintype.card ι : ℝ) * Real.sqrt (2 * b) * Real.sqrt e := by ring
  have hdiff : f i - f j = (α i - α j) + (v i - v j) := by
    rw [hmatch i hi, hmatch j hj]
    ring
  have hbound :
      |f i - f j| ≤ (2 + (Fintype.card ι : ℝ) * Real.sqrt (2 * b)) * Real.sqrt e := by
    rw [hdiff]
    have hαdiff : |α i - α j| ≤ |α i| + |α j| := by
      calc
        |α i - α j| = |α i + -α j| := by congr 1 <;> ring
        _ ≤ |α i| + |-α j| := abs_add_le _ _
        _ = |α i| + |α j| := by simp
    calc
      |(α i - α j) + (v i - v j)| ≤ |α i - α j| + |v i - v j| := abs_add_le _ _
      _ ≤ (|α i| + |α j|) + |v i - v j| := add_le_add hαdiff le_rfl
      _ ≤ (2 + (Fintype.card ι : ℝ) * Real.sqrt (2 * b)) * Real.sqrt e := by
        calc
          (|α i| + |α j|) + |v i - v j| ≤
              2 * Real.sqrt e + (Fintype.card ι : ℝ) * Real.sqrt (2 * b) * Real.sqrt e :=
            add_le_add (by linarith [hαi, hαj]) hvar
          _ = (2 + (Fintype.card ι : ℝ) * Real.sqrt (2 * b)) * Real.sqrt e := by ring
  have hmul := mul_le_mul hbound hbound (abs_nonneg _) (by
    positivity : 0 ≤ (2 + (Fintype.card ι : ℝ) * Real.sqrt (2 * b)) * Real.sqrt e)
  have hmul' : (f i - f j) ^ 2 ≤
      ((2 + (Fintype.card ι : ℝ) * Real.sqrt (2 * b)) * Real.sqrt e) ^ 2 := by
    simp only [← pow_two, sq_abs] at hmul
    exact hmul
  calc
    (f i - f j) ^ 2 ≤
        ((2 + (Fintype.card ι : ℝ) * Real.sqrt (2 * b)) * Real.sqrt e) ^ 2 := hmul'
    _ = (2 + (Fintype.card ι : ℝ) * Real.sqrt (2 * b)) ^ 2 * e := by
      rw [mul_pow, Real.sq_sqrt he]

lemma spatialEnergy_pair_sq_lower {ι : Type} [Fintype ι] (G : SimpleGraph ι)
    (hG : G.Connected) (A : Finset ι) (b : ℝ) (hb : 0 < b) (f : ι → ℝ)
    {i j : ι} (hi : i ∈ A) (hj : j ∈ A) :
    (f i - f j) ^ 2 / (2 + (Fintype.card ι : ℝ) * Real.sqrt (2 * b)) ^ 2 ≤
      spatialEnergy G A b f := by
  rw [spatialEnergy_eq_csInf]
  apply le_csInf (candidates_nonempty G A b f)
  rintro e ⟨α, v, hmatch, rfl⟩
  have h := cost_pair_sq_le G hG A b hb α v f hmatch hi hj
  have hK : 0 < (2 + (Fintype.card ι : ℝ) * Real.sqrt (2 * b)) ^ 2 := by
    positivity
  exact (div_le_iff₀ hK).2 (by simpa [mul_comm] using h)

end SpatialForm

theorem spatialEnergy_homogeneous {ι : Type} [Fintype ι] (G : SimpleGraph ι)
    (A : Finset ι) (b : ℝ) (hb : 0 < b) (s : ℝ) (f : ι → ℝ) :
    spatialEnergy G A b (fun i => s * f i) = s ^ 2 * spatialEnergy G A b f := by
  by_cases hs : s = 0
  · subst s
    have h0 : spatialEnergy G A b (fun _ : ι => 0) = 0 :=
      SpatialForm.spatialEnergy_zero_of_const G A b hb (fun _ => 0) 0 (by simp)
    simpa using h0
  · exact SpatialForm.spatialEnergy_scale G A b hb s hs f

theorem spatialEnergy_constantKernel {ι : Type} [Fintype ι] (G : SimpleGraph ι)
    (hG : G.Connected) (A : Finset ι) (b : ℝ) (hb : 0 < b) :
    constantKernel A (spatialEnergy G A b) := by
  intro f
  constructor
  · intro hzero
    by_cases hA : A.Nonempty
    · obtain ⟨a, ha⟩ := hA
      refine ⟨f a, ?_⟩
      intro i hi
      have hK : 0 < 2 + (Fintype.card ι : ℝ) * Real.sqrt (2 * b) := by positivity
      have hpair := SpatialForm.spatialEnergy_pair_sq_lower G hG A b hb f hi ha
      have hqle :
          (f i - f a) ^ 2 / (2 + (Fintype.card ι : ℝ) * Real.sqrt (2 * b)) ^ 2 ≤ 0 := by
        simpa [hzero] using hpair
      have hqnonneg :
          0 ≤ (f i - f a) ^ 2 / (2 + (Fintype.card ι : ℝ) * Real.sqrt (2 * b)) ^ 2 :=
        div_nonneg (sq_nonneg _) (by positivity)
      have hqzero := le_antisymm hqle hqnonneg
      have hmul :
          ((f i - f a) ^ 2 / (2 + (Fintype.card ι : ℝ) * Real.sqrt (2 * b)) ^ 2) *
            (2 + (Fintype.card ι : ℝ) * Real.sqrt (2 * b)) ^ 2 = 0 := by
        calc
          _ = 0 * (2 + (Fintype.card ι : ℝ) * Real.sqrt (2 * b)) ^ 2 :=
            congrArg (fun x : ℝ => x * (2 + (Fintype.card ι : ℝ) * Real.sqrt (2 * b)) ^ 2) hqzero
          _ = 0 := by ring
      have hsq : (f i - f a) ^ 2 = 0 := by
        field_simp [ne_of_gt hK] at hmul
        simpa using hmul
      have hdiff : f i - f a = 0 := by nlinarith [hsq]
      exact sub_eq_zero.mp hdiff
    · refine ⟨0, ?_⟩
      intro i hi
      exact (hA ⟨i, hi⟩).elim
  · rintro ⟨c, hc⟩
    exact SpatialForm.spatialEnergy_zero_of_const G A b hb f c hc

theorem spatialEnergy_dual_bddAbove {ι : Type} [Fintype ι] (G : SimpleGraph ι)
    (hG : G.Connected) (A : Finset ι) (b : ℝ) (hb : 0 < b)
    (y : ι → ℝ) (hy : neutral A y) :
    BddAbove (Set.range fun f : ι → ℝ =>
      2 * (∑ i ∈ A, y i * f i) - spatialEnergy G A b f) := by
  classical
  by_cases hA : A.Nonempty
  · obtain ⟨a, ha⟩ := hA
    let K : ℝ := 2 + (Fintype.card ι : ℝ) * Real.sqrt (2 * b)
    let Y : ℝ := ∑ i ∈ A, |y i|
    let H : ℝ := 1 + Y * K
    have hK : 0 < K := by dsimp [K]; positivity
    have hY : 0 ≤ Y := by dsimp [Y]; exact Finset.sum_nonneg fun i hi => abs_nonneg _
    have hObj (f : ι → ℝ) :
        2 * (∑ i ∈ A, y i * f i) - spatialEnergy G A b f ≤ H ^ 2 := by
      let E : ℝ := spatialEnergy G A b f
      let L : ℝ := ∑ i ∈ A, y i * f i
      have hE : 0 ≤ E := SpatialForm.spatialEnergy_nonneg G A b hb f
      have hchange :
          (∑ i ∈ A, y i * (f i - f a)) =
            (∑ i ∈ A, y i * f i) - (∑ i ∈ A, y i) * f a := by
        calc
          _ = ∑ i ∈ A, (y i * f i - y i * f a) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = (∑ i ∈ A, y i * f i) - ∑ i ∈ A, y i * f a := by
            rw [Finset.sum_sub_distrib]
          _ = (∑ i ∈ A, y i * f i) - (∑ i ∈ A, y i) * f a := by rw [← Finset.sum_mul]
      have hLrepr : L = ∑ i ∈ A, y i * (f i - f a) := by
        dsimp [L]
        rw [hchange, hy.2]
        simp
      have hLbound : |L| ≤ H * Real.sqrt E := by
        calc
          |L| = |∑ i ∈ A, y i * (f i - f a)| := by rw [hLrepr]
          _ ≤ ∑ i ∈ A, |y i * (f i - f a)| :=
            Finset.abs_sum_le_sum_abs (fun i => y i * (f i - f a)) A
          _ = ∑ i ∈ A, |y i| * |f i - f a| := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [abs_mul]
          _ ≤ ∑ i ∈ A, |y i| * (K * Real.sqrt E) := by
            apply Finset.sum_le_sum
            intro i hi
            have hpair := SpatialForm.spatialEnergy_pair_sq_lower G hG A b hb f hi ha
            have hsq : (f i - f a) ^ 2 ≤ K ^ 2 * E := by
              have hq : (f i - f a) ^ 2 / K ^ 2 ≤ E := by simpa [K, E] using hpair
              have hmul := (div_le_iff₀ (sq_pos_of_pos hK)).mp hq
              simpa [mul_comm] using hmul
            have hroot : |f i - f a| ≤ K * Real.sqrt E := by
              have h := Real.sqrt_le_sqrt hsq
              rw [Real.sqrt_sq_eq_abs] at h
              have hrootEq : Real.sqrt (K ^ 2 * E) = K * Real.sqrt E := by
                rw [Real.sqrt_mul (sq_nonneg K) E, Real.sqrt_sq_eq_abs, abs_of_pos hK]
              rw [hrootEq] at h
              exact h
            exact mul_le_mul_of_nonneg_left hroot (abs_nonneg _)
          _ = Y * (K * Real.sqrt E) := by
            dsimp [Y]
            rw [Finset.sum_mul]
          _ ≤ H * Real.sqrt E := by
            dsimp [H]
            calc
              Y * (K * Real.sqrt E) = (Y * K) * Real.sqrt E := by ring
              _ ≤ (1 + Y * K) * Real.sqrt E :=
                mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg E)
              _ = (1 + Y * K) * Real.sqrt E := rfl
      have hsquare : 0 ≤ (Real.sqrt E - H) ^ 2 := sq_nonneg _
      have hsqrtSq : (Real.sqrt E) ^ 2 = E := Real.sq_sqrt hE
      dsimp [E, L] at hLbound ⊢
      nlinarith [hLbound, le_abs_self L, hsquare, hsqrtSq]
    refine ⟨H ^ 2, ?_⟩
    rintro z ⟨f, rfl⟩
    exact hObj f
  · have hAeq : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    subst A
    refine ⟨0, ?_⟩
    rintro z ⟨f, rfl⟩
    have hzero : spatialEnergy G ∅ b f = 0 :=
      SpatialForm.spatialEnergy_zero_of_const G ∅ b hb f 0 (by simp)
    simp [hzero]

theorem spatialFormInput_proof : SpatialFormInput := by
  intro ι _ _ G hG A b hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f
    exact SpatialForm.spatialEnergy_nonneg G A b hb f
  · intro s f
    exact spatialEnergy_homogeneous G A b hb s f
  · exact spatialEnergy_constantKernel G hG A b hb
  · intro y hy
    exact spatialEnergy_dual_bddAbove G hG A b hb y hy

end AndersonAC.SolS78
