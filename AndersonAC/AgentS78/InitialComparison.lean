import AndersonAC.AgentS78.SweepPrestate
import AndersonAC.AgentS78.InitialStage

/-!
certificate construction: `AssemblyInput.initialComparison` (07-assembly.tex, assembly initial data
`c W ≤ D ≤ C W`) from the inverse-form comparison `c W* ≤ X ≤ C W*` on neutral charges,
by the §3 dual-form order reversal (`S3H.dual_comparison_order_proof`, Lemma 3.1),
with sites as ports (π = inclusion of the active set) at L = sideLength m.
-/

open scoped BigOperators
open Matrix

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

section General

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- The pseudoinverse on constants of a real symmetric matrix has real entries. -/
theorem inverseOnConstants_real (D : Matrix κ κ ℂ) (hDr : ∀ i j, (D i j).im = 0)
    (hDs : ∀ i j, D i j = D j i) (i j : κ) :
    (AndersonAC.S3.inverseOnConstants D i j).im = 0 := by
  set N := (D + AndersonAC.S3.meanProjection κ)⁻¹ with hN
  have hP : ∀ i j, AndersonAC.S3.meanProjection κ i j = ((Fintype.card κ : ℝ)⁻¹ : ℝ) := by
    intro i j; simp [AndersonAC.S3.meanProjection]
  have hH : (D + AndersonAC.S3.meanProjection κ).conjTranspose = D + AndersonAC.S3.meanProjection κ := by
    ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.add_apply, hP, star_add]
    rw [hDs b a, Complex.star_def, Complex.conj_eq_iff_im.mpr (hDr a b), Complex.conj_ofReal]
  have hT : (D + AndersonAC.S3.meanProjection κ).transpose = D + AndersonAC.S3.meanProjection κ := by
    ext a b
    simp only [Matrix.transpose_apply, Matrix.add_apply, hP]
    rw [hDs b a]
  have hNH : N.conjTranspose = N := by rw [hN, Matrix.conjTranspose_nonsing_inv, hH]
  have hNT : N.transpose = N := by rw [hN, Matrix.transpose_nonsing_inv, hT]
  have hNr : (N i j).im = 0 := by
    have h1 := congrFun (congrFun hNH i) j
    have h2 := congrFun (congrFun hNT j) i
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply] at h1 h2
    rw [h2] at h1 ⊢
    exact Complex.conj_eq_iff_im.mp h1
  unfold AndersonAC.S3.inverseOnConstants
  rw [Matrix.sub_apply, Complex.sub_im, hNr, hP]
  simp

/-- A real symmetric matrix whose real form is nonnegative with constant kernel is a
connected Laplacian in the §3 (complex) sense. -/
theorem connected_of_real (D : Matrix κ κ ℂ) (hDr : ∀ i j, (D i j).im = 0)
    (hDs : ∀ i j, D i j = D j i)
    (hnn : ∀ g : κ → ℝ, 0 ≤ AndersonAC.S3.form D (cx g))
    (hker : ∀ g : κ → ℝ, AndersonAC.S3.form D (cx g) = 0 ↔ ∃ c : ℝ, ∀ i, g i = c) :
    AndersonAC.S3.connectedLaplacian D := by
  refine ⟨?_, fun f => ?_⟩
  · ext a b
    simp only [Matrix.conjTranspose_apply]
    rw [hDs b a, Complex.star_def, Complex.conj_eq_iff_im.mpr (hDr a b)]
  · rw [form_real_split D hDr f]
    have h1 := hnn (fun i => (f i).re)
    have h2 := hnn (fun i => (f i).im)
    refine ⟨by linarith, ⟨fun h => ?_, fun ⟨c, hc⟩ => ?_⟩⟩
    · have e1 : AndersonAC.S3.form D (cx fun i => (f i).re) = 0 := by linarith
      have e2 : AndersonAC.S3.form D (cx fun i => (f i).im) = 0 := by linarith
      obtain ⟨a, ha⟩ := (hker _).mp e1
      obtain ⟨b, hb⟩ := (hker _).mp e2
      refine ⟨⟨a, b⟩, funext fun i => Complex.ext (ha i) (hb i)⟩
    · subst hc
      have e1 := (hker (fun _ => c.re)).mpr ⟨c.re, fun _ => rfl⟩
      have e2 := (hker (fun _ => c.im)).mpr ⟨c.im, fun _ => rfl⟩
      rw [e1, e2, add_zero]

end General

section Torus

variable {d m : ℕ}

/-- The §3 gradient energy of a real torus function is the S78 graph energy. -/
theorem s3_gradient_cx (hm : 0 < m) (w : Torus d m → ℝ) :
    AndersonAC.S3.gradientEnergy (d := d) (L := OAI.Anderson.sideLength m) (cx w) =
      gradientEnergy (nnGraph d m) w := by
  rw [AndersonAC.S3H.gradientEnergy_eq_form, ← gradientEnergy_eq_laplacian_form hm]

theorem s3_gradient_split (v : Torus d m → ℂ) :
    AndersonAC.S3.gradientEnergy (d := d) (L := OAI.Anderson.sideLength m) v =
      AndersonAC.S3.gradientEnergy (d := d) (L := OAI.Anderson.sideLength m) (cx fun x => (v x).re) +
      AndersonAC.S3.gradientEnergy (d := d) (L := OAI.Anderson.sideLength m) (cx fun x => (v x).im) := by
  unfold AndersonAC.S3.gradientEnergy cx
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.ofReal_sub, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, AndersonAC.S3H.norm_sq_eq_re_im]
  simp

/-- The S78 spatial energy is the §3 comparison form with sites as ports. -/
theorem spatialEnergy_eq_comparisonW (hm : 0 < m) (A : Finset (Torus d m)) (b : ℝ) (hb : 0 < b)
    (f : Torus d m → ℝ) :
    spatialEnergy (nnGraph d m) A b f =
      AndersonAC.S3.comparisonW (d := d) (L := OAI.Anderson.sideLength m) (fun a : A => a.val) b
        (cx fun a : A => f a.val) := by
  set S := {e : ℝ | ∃ α v : Torus d m → ℝ, (∀ i ∈ A, f i = α i + v i) ∧
    e = (∑ i ∈ A, (α i) ^ 2) + b⁻¹ * gradientEnergy (nnGraph d m) v} with hS
  have hgrad0 : ∀ v : Torus d m → ℝ, 0 ≤ gradientEnergy (nnGraph d m) v := by
    intro v
    unfold gradientEnergy
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_)
    split_ifs <;> positivity
  have hbdd : BddBelow S := ⟨0, by
    rintro e ⟨α, v, -, rfl⟩
    have := hgrad0 v
    have : 0 ≤ ∑ i ∈ A, (α i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    positivity⟩
  -- cost of a real profile
  have hcost : ∀ v : Torus d m → ℝ, AndersonAC.S3.comparisonCost (d := d) (L := OAI.Anderson.sideLength m)
      (fun a : A => a.val) b (cx fun a : A => f a.val) (cx v) =
      (∑ i ∈ A, (f i - v i) ^ 2) + b⁻¹ * gradientEnergy (nnGraph d m) v := by
    intro v
    unfold AndersonAC.S3.comparisonCost AndersonAC.S3.normSq
    rw [s3_gradient_cx hm, ← Finset.sum_coe_sort A]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [cx]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  unfold spatialEnergy
  rw [← hS]
  apply le_antisymm
  · obtain ⟨v, hv⟩ := (AndersonAC.S3.dual_comparison_forms_proof (d := d)
      (L := OAI.Anderson.sideLength m) (by
        have := AndersonAC.SolS78.sideLength_gt_two hm
        unfold OAI.Anderson.sideLength at this ⊢
        have : 4 ≤ 4 ^ (20 * m) := by
          calc 4 = 4 ^ 1 := by norm_num
            _ ≤ 4 ^ (20 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact this) (fun a : A => a.val) b hb).1 (cx fun a : A => f a.val)
    rw [hv]
    refine csInf_le_of_le hbdd ⟨fun i => f i - (v i).re, fun i => (v i).re, fun i _ => by ring, rfl⟩ ?_
    have hsplit : AndersonAC.S3.comparisonCost (d := d) (L := OAI.Anderson.sideLength m)
        (fun a : A => a.val) b (cx fun a : A => f a.val) v =
        AndersonAC.S3.comparisonCost (d := d) (L := OAI.Anderson.sideLength m)
          (fun a : A => a.val) b (cx fun a : A => f a.val) (cx fun x => (v x).re) +
        ((∑ a : A, (v a.val).im ^ 2) + b⁻¹ *
          AndersonAC.S3.gradientEnergy (d := d) (L := OAI.Anderson.sideLength m) (cx fun x => (v x).im)) := by
      unfold AndersonAC.S3.comparisonCost AndersonAC.S3.normSq
      rw [s3_gradient_split v]
      have : ∀ a : A, ‖(cx fun a : A => f a.val) a - v a.val‖ ^ 2 =
          ‖(cx fun a : A => f a.val) a - (cx fun x => (v x).re) a.val‖ ^ 2 + (v a.val).im ^ 2 := by
        intro a
        simp only [cx]
        rw [AndersonAC.S3H.norm_sq_eq_re_im, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          sq_abs]
        simp
      simp_rw [this, Finset.sum_add_distrib]
      ring
    rw [hsplit, hcost]
    have h1 : 0 ≤ ∑ a : A, (v a.val).im ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
    have h2 : 0 ≤ AndersonAC.S3.gradientEnergy (d := d) (L := OAI.Anderson.sideLength m)
        (cx fun x => (v x).im) := AndersonAC.S3H.gradientEnergy_nonneg _
    have h3 : 0 ≤ b⁻¹ := inv_nonneg.mpr hb.le
    have : (∑ i ∈ A, (f i - (v i).re) ^ 2) = ∑ i ∈ A, ((fun i => f i - (v i).re) i) ^ 2 := rfl
    nlinarith [mul_nonneg h3 h2]
  · refine le_csInf ?_ ?_
    · exact ⟨_, f, 0, fun i _ => by simp, rfl⟩
    rintro e ⟨α, v, hfv, rfl⟩
    refine (AndersonAC.S3H.comparisonW_le_cost _ b hb _ (cx v)).trans (le_of_eq ?_)
    rw [hcost]
    congr 1
    exact Finset.sum_congr rfl fun i hi => by rw [hfv i hi]; ring

theorem sideLength_ge_four {m : ℕ} (hm : 0 < m) : 4 ≤ OAI.Anderson.sideLength m := by
  unfold OAI.Anderson.sideLength
  calc 4 = 4 ^ 1 := by norm_num
    _ ≤ 4 ^ (20 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem laplacian_symm (x y : AndersonAC.S3.Torus d (OAI.Anderson.sideLength m)) :
    AndersonAC.S3.laplacian (d := d) (L := OAI.Anderson.sideLength m) x y =
      AndersonAC.S3.laplacian (d := d) (L := OAI.Anderson.sideLength m) y x := by
  unfold AndersonAC.S3.laplacian
  rw [Matrix.add_apply, Matrix.add_apply, AndersonAC.S3H.freeHopping_symm]
  by_cases h : x = y
  · rw [h]
  · simp [Matrix.one_apply, h, Ne.symm h]

/-- `Λ⁺` of a real neutral torus charge is the §3 `laplacianPlus` form. -/
theorem lambda_eq_laplacianPlus (hm : 0 < m) (y : Torus d m → ℝ) (hy : ∑ i, y i = 0) :
    inverseEnergy Finset.univ (gradientEnergy (nnGraph d m)) y =
      AndersonAC.S3.form (AndersonAC.S3.laplacianPlus (d := d) (L := OAI.Anderson.sideLength m)) (cx y) := by
  rw [inverseEnergy_eq_form _ _ (laplacian_im _) AndersonAC.S3H.laplacian_connected
    (gradientEnergy_eq_laplacian_form hm) y hy]
  unfold AndersonAC.S3.laplacianPlus
  exact congrArg (fun X => AndersonAC.S3.form X (cx y)) (inverseOnConstants_inst _ _ _)

theorem siteSum_val_cx (A : Finset (Torus d m)) (y : Torus d m → ℝ) (hy : ∀ i ∉ A, y i = 0) :
    AndersonAC.S3.siteSum (d := d) (L := OAI.Anderson.sideLength m) (fun a : A => a.val)
      (cx fun a : A => y a.val) = cx y := by
  funext i
  unfold AndersonAC.S3.siteSum cx
  rw [Finset.sum_filter]
  by_cases hi : i ∈ A
  · rw [Finset.sum_eq_single (⟨i, hi⟩ : A)]
    · simp
    · intro a _ ha
      have : a.val ≠ i := fun h => ha (Subtype.ext h)
      simp [this]
    · simp
  · rw [hy i hi]
    refine Finset.sum_eq_zero fun a _ => ?_
    have : a.val ≠ i := fun h => hi (h ▸ a.property)
    simp [this]

/-- `W*` of a real neutral active charge, in S78 terms. -/
theorem comparisonWStar_real (hm : 0 < m) (A : Finset (Torus d m)) (b : ℝ) (y : Torus d m → ℝ)
    (hy : neutral A y) :
    AndersonAC.S3.comparisonWStar (d := d) (L := OAI.Anderson.sideLength m) (fun a : A => a.val) b
        (cx fun a : A => y a.val) =
      (∑ i ∈ A, y i ^ 2) + b * inverseEnergy Finset.univ (gradientEnergy (nnGraph d m)) y := by
  have hy0 : ∑ i, y i = 0 := by
    rw [← Finset.sum_subset (Finset.subset_univ A) (fun i _ hi => hy.1 i hi)]; exact hy.2
  unfold AndersonAC.S3.comparisonWStar
  rw [siteSum_val_cx A y hy.1, lambda_eq_laplacianPlus hm y hy0]
  congr 1
  unfold AndersonAC.S3.normSq cx
  rw [← Finset.sum_coe_sort A]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- `W*` splits into real and imaginary parts. -/
theorem comparisonWStar_split {A : Type} [Fintype A] (π : A → AndersonAC.S3.Torus d (OAI.Anderson.sideLength m))
    (b : ℝ) (y : A → ℂ) :
    AndersonAC.S3.comparisonWStar (d := d) (L := OAI.Anderson.sideLength m) π b y =
      AndersonAC.S3.comparisonWStar (d := d) (L := OAI.Anderson.sideLength m) π b (cx fun a => (y a).re) +
      AndersonAC.S3.comparisonWStar (d := d) (L := OAI.Anderson.sideLength m) π b (cx fun a => (y a).im) := by
  have hreal : ∀ i j, (AndersonAC.S3.laplacianPlus (d := d) (L := OAI.Anderson.sideLength m) i j).im = 0 :=
    inverseOnConstants_real _ (laplacian_im _) laplacian_symm
  have hre : (cx fun i => (AndersonAC.S3.siteSum π y i).re) = AndersonAC.S3.siteSum π (cx fun a => (y a).re) := by
    funext i; simp [AndersonAC.S3.siteSum, cx, Complex.re_sum]
  have him : (cx fun i => (AndersonAC.S3.siteSum π y i).im) = AndersonAC.S3.siteSum π (cx fun a => (y a).im) := by
    funext i; simp [AndersonAC.S3.siteSum, cx, Complex.im_sum]
  unfold AndersonAC.S3.comparisonWStar
  rw [form_real_split _ hreal (AndersonAC.S3.siteSum π y), hre, him]
  have hn : AndersonAC.S3.normSq y = AndersonAC.S3.normSq (cx fun a => (y a).re) +
      AndersonAC.S3.normSq (cx fun a => (y a).im) := by
    unfold AndersonAC.S3.normSq cx
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [AndersonAC.S3H.norm_sq_eq_re_im, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, sq_abs, sq_abs]
  rw [hn]; ring

/-- **Assembly initial comparison.** For a damped endpoint with nonnegative damping and
constant kernel, the inverse-form comparison `c W* ≤ X ≤ C W*` on neutral active charges
gives `C⁻¹ W ≤ D ≤ c⁻¹ W` for the endpoint energy and the S78 spatial energy — the form of
`AssemblyInput.initialComparison`. -/
theorem initial_comparison (hm : 0 < m) (s : Endpoint (Torus d m)) (r : Torus d m → ℂ) (t : ℝ)
    (ht : 0 < t) (hD : IsDampedEndpoint s r t) (hne : s.active.Nonempty)
    (hp : ∀ i ∈ s.active, 0 ≤ (r i).im)
    (hker : constantKernel s.active (endpointEnergy s r t)) (b c C : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hC : 0 < C)
    (hcomp : ∀ y, neutral s.active y →
      c * ((∑ i ∈ s.active, y i ^ 2) + b * inverseEnergy Finset.univ (gradientEnergy (nnGraph d m)) y) ≤
        inverseEnergy s.active (endpointEnergy s r t) y ∧
      inverseEnergy s.active (endpointEnergy s r t) y ≤
        C * ((∑ i ∈ s.active, y i ^ 2) + b * inverseEnergy Finset.univ (gradientEnergy (nnGraph d m)) y)) :
    ∀ f, C⁻¹ * spatialEnergy (nnGraph d m) s.active b f ≤ endpointEnergy s r t f ∧
      endpointEnergy s r t f ≤ c⁻¹ * spatialEnergy (nnGraph d m) s.active b f := by
  classical
  haveI : Nonempty s.active := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  set e : s.active ≃ s.active := Equiv.refl _ with he
  set st := toS45 s r e with hst
  obtain ⟨hsym, hward⟩ := ward_of_damped s r t ht.le hD e
  set D := st.D t with hDdef
  set DA : Matrix s.active s.active ℂ := D.map (fun x : ℝ => (x : ℂ)) with hDA
  have hform : ∀ g : s.active → ℝ, AndersonAC.S3.form DA (cx g) = AndersonAC.S45.qform D g := by
    intro g
    unfold AndersonAC.S3.form AndersonAC.S3.pairing AndersonAC.S45.qform cx
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mulVec, dotProduct, hDA, Matrix.map_apply]
    rw [show (∑ x, (D i x : ℂ) * (g x : ℂ)) = ((∑ x, D i x * g x : ℝ) : ℂ) by push_cast; rfl,
      Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hE : ∀ f, endpointEnergy s r t f = AndersonAC.S3.form DA (cx fun a : s.active => f a.val) := by
    intro f
    rw [endpointEnergy_eq_S45 s r t e hsym hward f, hform]
    rfl
  have hDr : ∀ i j, (DA i j).im = 0 := by intro i j; simp [hDA]
  have hgsym : ∀ a b, st.g b a = st.g a b := by
    intro a b; have := congrFun (congrFun hsym a) b; simpa [Matrix.transpose_apply] using this
  have hDs : ∀ i j, DA i j = DA j i := by
    intro i j
    simp only [hDA, Matrix.map_apply, hDdef, AndersonAC.S45.State.D, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.diagonal_apply, AndersonAC.S45.State.F, AndersonAC.S45.entryAbsSquare,
      AndersonAC.S45.State.h, Matrix.smul_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij; rfl
    · simp [hij, Ne.symm hij, hgsym i j]
      ring_nf
  have hext : ∀ g : s.active → ℝ, AndersonAC.S3.form DA (cx g) = endpointEnergy s r t (extendFun e g) := by
    intro g
    rw [hE]
    congr 2
    exact (extendFun_comp e g).symm
  have hnn : ∀ g : s.active → ℝ, 0 ≤ AndersonAC.S3.form DA (cx g) := by
    intro g
    rw [hext]
    unfold endpointEnergy
    exact wardEnergy_nonneg _ _ hp _ _
  have hkerA : ∀ g : s.active → ℝ, AndersonAC.S3.form DA (cx g) = 0 ↔ ∃ c : ℝ, ∀ i, g i = c := by
    intro g
    rw [hext]
    constructor
    · intro h0
      obtain ⟨c0, hc0⟩ := (hker _).mp h0
      refine ⟨c0, fun i => ?_⟩
      have := hc0 (e i).val (e i).property
      rwa [show extendFun e g (e i).val = g i from congrFun (extendFun_comp e g) i] at this
    · rintro ⟨c0, hc0⟩
      refine (hker _).mpr ⟨c0, fun x hx => ?_⟩
      simp [extendFun, hx, hc0]
  have hconn := connected_of_real DA hDr hDs hnn hkerA
  -- inverse-form identification
  have hX : ∀ y, neutral s.active y → inverseEnergy s.active (endpointEnergy s r t) y =
      AndersonAC.S3.form (AndersonAC.S3.inverseOnConstants DA) (cx fun a : s.active => y a.val) := by
    intro y hy
    have hy0 : ∑ a : s.active, y a.val = 0 := by rw [Finset.sum_coe_sort s.active y]; exact hy.2
    rw [← inverseEnergy_eq_form (fun g => AndersonAC.S3.form DA (cx g)) DA hDr hconn (fun g => rfl) _ hy0]
    unfold inverseEnergy
    congr 1
    ext a
    simp only [Set.mem_range]
    constructor
    · rintro ⟨f, rfl⟩
      refine ⟨fun i => f i.val, ?_⟩
      rw [hE f, Finset.sum_coe_sort s.active (fun x => y x * f x)]
    · rintro ⟨g, rfl⟩
      refine ⟨extendFun e g, ?_⟩
      rw [hE, show (fun a : s.active => extendFun e g a.val) = g from extendFun_comp e g,
        ← Finset.sum_coe_sort s.active (fun x => y x * extendFun e g x)]
      congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show extendFun e g i.val = g i from congrFun (extendFun_comp e g) i]
  -- complex comparators
  have hXr := inverseOnConstants_real DA hDr hDs
  have hcompC : ∀ y : s.active → ℂ, AndersonAC.S3.neutral y →
      c * AndersonAC.S3.comparisonWStar (d := d) (L := OAI.Anderson.sideLength m) (fun a : s.active => a.val) b y ≤
        AndersonAC.S3.form (AndersonAC.S3.inverseOnConstants DA) y ∧
      AndersonAC.S3.form (AndersonAC.S3.inverseOnConstants DA) y ≤
        C * AndersonAC.S3.comparisonWStar (d := d) (L := OAI.Anderson.sideLength m) (fun a : s.active => a.val) b y := by
    intro y hy
    have hpart : ∀ g : s.active → ℝ, ∑ a, g a = 0 →
        c * AndersonAC.S3.comparisonWStar (d := d) (L := OAI.Anderson.sideLength m) (fun a : s.active => a.val) b (cx g) ≤
          AndersonAC.S3.form (AndersonAC.S3.inverseOnConstants DA) (cx g) ∧
        AndersonAC.S3.form (AndersonAC.S3.inverseOnConstants DA) (cx g) ≤
          C * AndersonAC.S3.comparisonWStar (d := d) (L := OAI.Anderson.sideLength m) (fun a : s.active => a.val) b (cx g) := by
      intro g hg
      have hn : neutral s.active (extendFun e g) := by
        refine ⟨fun i hi => by simp [extendFun, hi], ?_⟩
        rw [← Finset.sum_coe_sort s.active, show (fun i : s.active => extendFun e g i.val) = g from
          extendFun_comp e g]
        exact hg
      have h1 := hcomp _ hn
      rw [hX _ hn, ← comparisonWStar_real hm s.active b _ hn,
        show (fun a : s.active => extendFun e g a.val) = g from extendFun_comp e g] at h1
      exact h1
    have hre : ∑ a, (y a).re = 0 := by
      have := congrArg Complex.re hy; simpa [Complex.re_sum] using this
    have him : ∑ a, (y a).im = 0 := by
      have := congrArg Complex.im hy; simpa [Complex.im_sum] using this
    obtain ⟨a1, a2⟩ := hpart _ hre
    obtain ⟨b1, b2⟩ := hpart _ him
    rw [comparisonWStar_split, form_real_split _ hXr y]
    constructor <;> nlinarith
  have hord := (AndersonAC.S3.dual_comparison_order_proof (d := d) (L := OAI.Anderson.sideLength m)
    (sideLength_ge_four hm) (fun a : s.active => a.val) b c C hb hc hC DA hconn).mp hcompC
  intro f
  obtain ⟨o1, o2⟩ := hord (cx fun a : s.active => f a.val)
  rw [← spatialEnergy_eq_comparisonW hm s.active b hb f, ← hE f] at o1 o2
  exact ⟨o1, o2⟩

end Torus

end AndersonAC.AgentS78
