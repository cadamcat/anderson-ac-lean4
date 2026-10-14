import OAI.MathematicalPhysics.Anderson.Certificates

open MeasureTheory Measure Set
open scoped ENNReal symmDiff

namespace AndersonAC
namespace Prob

noncomputable section

open OAI.Anderson

variable {d : ℕ}

/-- Lattice translation on configurations: `(T_a ω) x = ω (x + a)`. -/
def shiftConfig (a : Site d) (ω : Configuration d) : Configuration d :=
  fun x => ω (x + a)

lemma shiftConfig_measurable (a : Site d) : Measurable (shiftConfig (d := d) a) := by
  rw [measurable_pi_iff]
  intro x
  exact measurable_pi_apply (x + a)

/-- Translation preserves the i.i.d. uniform disorder law. -/
lemma shiftConfig_measurePreserving (a : Site d) :
    MeasurePreserving (shiftConfig (d := d) a) (disorderLaw d) (disorderLaw d) := by
  refine ⟨shiftConfig_measurable a, ?_⟩
  unfold disorderLaw
  apply Measure.eq_infinitePi
  intro s t ht
  classical
  have hinj : Function.Injective (fun x : Site d => x + a) := fun x y h => by
    have h2 : x + a - a = y + a - a := congrArg (· - a) h
    simpa [add_sub_cancel_right] using h2
  have hmem_img : ∀ i : Site d, i ∈ s →
      ((i + a : Site d) ∈ ((s.image (fun x => x + a) : Finset (Site d)) : Set (Site d))) := by
    intro i hi
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  have hpre : shiftConfig (d := d) a ⁻¹' (↑s : Set (Site d)).pi t
      = ((s.image (fun x => x + a) : Finset (Site d)) : Set (Site d)).pi
        (fun j => if j ∈ ((s.image (fun x => x + a) : Finset (Site d)) : Set (Site d))
          then t (j - a) else Set.univ) := by
    ext ω
    simp only [mem_preimage, mem_pi, shiftConfig]
    constructor
    · intro h j hj
      have hjmem : j ∈ ((s.image (fun x => x + a) : Finset (Site d)) : Set (Site d)) := hj
      simp only [hjmem, ite_true]
      obtain ⟨i, hi, hij⟩ := Finset.mem_coe.mp hj |> Finset.mem_image.mp
      have hja : j - a = i := by
        rw [← hij, add_sub_cancel_right]
      rw [hja, ← hij]
      exact h i (Finset.mem_coe.mp (by simpa using hi : i ∈ (↑s : Set (Site d))))
    · intro h i hi
      have his : i ∈ (↑s : Set (Site d)) := Finset.mem_coe.mpr hi
      have hj : (i + a : Site d) ∈ ((s.image (fun x => x + a) : Finset (Site d)) : Set (Site d)) :=
        hmem_img i hi
      have h1 := h (i + a) hj
      simp only [hj, ite_true] at h1
      have hja : i + a - a = i := add_sub_cancel_right i a
      rw [hja] at h1
      exact h1
  rw [Measure.map_apply (shiftConfig_measurable a) (.pi s.countable_toSet fun i _ => ht i)]
  rw [hpre]
  have ht' : ∀ j ∈ s.image (fun x : Site d => x + a),
      MeasurableSet (if j ∈ ((s.image (fun x => x + a) : Finset (Site d)) : Set (Site d))
        then t (j - a) else Set.univ) := by
    intro j hj
    simp only [Finset.mem_coe.mpr hj, ite_true]
    obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hj
    have hja : j - a = i := by
      rw [← hij, add_sub_cancel_right]
    rw [hja]
    exact ht i
  rw [Measure.infinitePi_pi _ ht']
  have hprod : ∏ j ∈ s.image (fun x : Site d => x + a),
        (uniformSite : Measure SingleSite)
        (if j ∈ ((s.image (fun x => x + a) : Finset (Site d)) : Set (Site d))
          then t (j - a) else Set.univ)
      = ∏ i ∈ s, uniformSite (t i) := by
    rw [Finset.prod_image (fun x _ y _ h => hinj h)]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [hmem_img i hi, ite_true]
    have hja : i + a - a = i := add_sub_cancel_right i a
    rw [hja]
  exact hprod

/-- Finite-coordinate cylinders form an algebra of sets. -/
lemma isSetAlgebra_measurableCylinders :
    MeasureTheory.IsSetAlgebra (MeasureTheory.measurableCylinders (fun _ : Site d => SingleSite)) where
  empty_mem := MeasureTheory.empty_mem_measurableCylinders _
  compl_mem _ hs := MeasureTheory.compl_mem_measurableCylinders hs
  union_mem _ _ hs ht := MeasureTheory.union_mem_measurableCylinders hs ht

/-- Cylinders are dense for the disorder law: any measurable event is approximable. -/
lemma measureDense_cylinders :
    (disorderLaw d).MeasureDense
      (MeasureTheory.measurableCylinders (fun _ : Site d => SingleSite)) := by
  apply Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite (disorderLaw d)
    isSetAlgebra_measurableCylinders
  exact (MeasureTheory.generateFrom_measurableCylinders).symm

/-- Approximation of any measurable event by a finite-coordinate cylinder. -/
lemma exists_cylinder_approx {E : Set (Configuration d)} (hE : MeasurableSet E)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C ∈ MeasureTheory.measurableCylinders (fun _ : Site d => SingleSite),
      disorderLaw d (E ∆ C) < ENNReal.ofReal ε := by
  have hfin : disorderLaw d E ≠ ∞ := measure_ne_top _ _
  exact (measureDense_cylinders (d := d)).approx E hE hfin ε hε

/-- Multiples of a nonzero lattice vector are distinct. -/
lemma nsmul_injective_of_ne_zero {a : Site d} (ha : a ≠ 0) :
    Function.Injective (fun n : ℕ => n • a) := by
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := Function.ne_iff.mp ha
  intro n m hnm
  have hj2 : (n • a) j = (m • a) j := congrArg (· j) hnm
  simp only [Pi.smul_apply, nsmul_eq_mul] at hj2
  have hcast : (n : ℤ) = (m : ℤ) := mul_right_cancel₀ hj hj2
  exact Nat.cast_inj.mp hcast

/-- Any finite set of sites can be translated to a disjoint copy along a nonzero direction. -/
lemma exists_disjoint_translate (s : Finset (Site d)) {a : Site d} (ha : a ≠ 0) :
    ∃ n : ℕ, Disjoint s (s.image (fun x => x + n • a)) := by
  classical
  by_contra hcon
  push Not at hcon
  -- differences covered by multiples
  let D : Finset (Site d) := (s.product s).image (fun p : Site d × Site d => p.1 - p.2)
  have hmemD : ∀ n : ℕ, n • a ∈ D := by
    intro n
    have hnd := hcon n
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨x, hxs, hximg⟩ := hnd
    obtain ⟨y, hys, hyx⟩ := Finset.mem_image.mp hximg
    have hdiff : n • a = x - y := by
      rw [← hyx]
      abel
    rw [hdiff]
    apply Finset.mem_image.mpr
    exact ⟨(x, y), Finset.mem_product.mpr ⟨hxs, hys⟩, rfl⟩
  have hcard : (Finset.range (D.card + 1)).image (fun n : ℕ => n • a) ⊆ D := by
    intro z hz
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
    exact hmemD n
  have hinj := nsmul_injective_of_ne_zero (d := d) ha
  have himg_card : ((Finset.range (D.card + 1)).image (fun n : ℕ => n • a)).card
      = D.card + 1 := by
    rw [Finset.card_image_of_injective _ hinj]
    exact Finset.card_range _
  have hle := Finset.card_le_card hcard
  rw [himg_card] at hle
  exact Nat.not_succ_le_self _ hle

/-- A nonzero lattice direction exists when `0 < d`. -/
lemma exists_ne_zero_site {d : ℕ} (hd : 0 < d) : ∃ a : Site d, a ≠ 0 := by
  refine ⟨Pi.single ⟨0, hd⟩ 1, ?_⟩
  intro h
  have := congrArg (· ⟨0, hd⟩) h
  simp [Pi.single_eq_same] at this

/-- Coordinate projections are independent under the disorder law. -/
lemma iIndepFun_config :
    ProbabilityTheory.iIndepFun (fun (i : Site d) (ω : Configuration d) => ω i)
      (disorderLaw d) := by
  unfold disorderLaw
  exact ProbabilityTheory.iIndepFun_infinitePi (fun _ => measurable_id)

/-- Cylinders on disjoint finite coordinate sets are independent. -/
lemma disjoint_cylinders_indep {s t : Finset (Site d)} (hdisj : Disjoint s t)
    {S : Set (∀ i : (s : Finset (Site d)), SingleSite)}
    {T : Set (∀ i : (t : Finset (Site d)), SingleSite)}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    disorderLaw d (MeasureTheory.cylinder s S ∩ MeasureTheory.cylinder t T)
      = disorderLaw d (MeasureTheory.cylinder s S)
        * disorderLaw d (MeasureTheory.cylinder t T) := by
  classical
  have hIndep := iIndepFun_config (d := d)
  have hfin : ProbabilityTheory.IndepFun
      (fun (ω : Configuration d) (i : (s : Finset (Site d))) => ω (i : Site d))
      (fun (ω : Configuration d) (i : (t : Finset (Site d))) => ω (i : Site d))
      (disorderLaw d) :=
    hIndep.indepFun_finset s t hdisj (fun i => measurable_pi_apply i)
  -- identify `cylinder` with preimages under the restriction maps
  have hC : MeasureTheory.cylinder s S
      = (fun (ω : Configuration d) (i : (s : Finset (Site d))) => ω (i : Site d)) ⁻¹' S := rfl
  have hD : MeasureTheory.cylinder t T
      = (fun (ω : Configuration d) (i : (t : Finset (Site d))) => ω (i : Site d)) ⁻¹' T := rfl
  rw [hC, hD]
  exact hfin.measure_inter_preimage_eq_mul _ _ hS hT

/-- Translate a cylinder along `b`: get a cylinder over the translated finset. -/
lemma translated_cylinder {s : Finset (Site d)}
    {S : Set (∀ i : (s : Finset (Site d)), SingleSite)}
    (hS : MeasurableSet S) (b : Site d) :
    ∃ (S' : Set (∀ i : ((s.image (fun x => x + b) : Finset (Site d)) : Finset (Site d)),
        SingleSite)),
      MeasurableSet S' ∧
      shiftConfig (d := d) b ⁻¹' MeasureTheory.cylinder s S
        = MeasureTheory.cylinder (s.image (fun x => x + b)) S' := by
  classical
  let ψ : (∀ i : ((s.image (fun x : Site d => x + b) : Finset (Site d)) : Finset (Site d)),
      SingleSite) → (∀ i : (s : Finset (Site d)), SingleSite) :=
    fun f i => f ⟨(i : Site d) + b, Finset.mem_image.mpr ⟨i, i.property, rfl⟩⟩
  have hψ : Measurable ψ := by
    rw [measurable_pi_iff]
    intro i
    exact measurable_pi_apply _
  refine ⟨ψ ⁻¹' S, hS.preimage hψ, ?_⟩
  have heq : ∀ ω : Configuration d,
      ψ ((s.image (fun x : Site d => x + b)).restrict ω)
        = s.restrict (shiftConfig (d := d) b ω) := fun ω => rfl
  ext ω
  show shiftConfig (d := d) b ω ∈ MeasureTheory.cylinder s S ↔
    ω ∈ MeasureTheory.cylinder _ _
  rw [MeasureTheory.mem_cylinder, MeasureTheory.mem_cylinder]
  show s.restrict (shiftConfig (d := d) b ω) ∈ S ↔
    (s.image (fun x : Site d => x + b)).restrict ω ∈ ψ ⁻¹' S
  rw [Set.mem_preimage, heq]

/-- Real-valued bound from the cylinder approximation. -/
lemma real_symmDiff_lt_of_approx {E C : Set (Configuration d)}
    (hE : MeasurableSet E) (hC : MeasurableSet C)
    {ε : ℝ} (hε : 0 < ε) (h : disorderLaw d (E ∆ C) < ENNReal.ofReal ε) :
    (disorderLaw d).real (E ∆ C) < ε := by
  have hne1 : disorderLaw d (E ∆ C) ≠ ∞ := measure_ne_top _ _
  have hne2 : ENNReal.ofReal ε ≠ ∞ := ENNReal.ofReal_ne_top
  have hlt := (ENNReal.toReal_lt_toReal hne1 hne2).mpr h
  rwa [ENNReal.toReal_ofReal (le_of_lt hε)] at hlt

/-- The disorder law gives mass at most one to any set (real-valued). -/
lemma real_le_one (A : Set (Configuration d)) : (disorderLaw d).real A ≤ 1 := by
  calc (disorderLaw d).real A ≤ (disorderLaw d).real Set.univ :=
        measureReal_mono (Set.subset_univ _)
    _ = 1 := by rw [measureReal_def, measure_univ, ENNReal.toReal_one]

/-- Intersections of approximating sets are close on the symmetric difference. -/
lemma inter_symmDiff_subset (A B C D : Set (Configuration d)) :
    (A ∩ B) ∆ (C ∩ D) ⊆ (A ∆ C) ∪ (B ∆ D) := by
  intro x hx
  simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_union] at hx ⊢
  tauto

/-- Zero–one law for lattice-translation-invariant events (§9 ergodicity).
An event invariant under every lattice translation has probability `0` or `1`.
Paper reference: §9, "Ergodicity of the iid translation action makes its probability one";
the proof approximates by a finite cylinder, translates to disjointness, and lets the
error tend to zero. -/
theorem disorderLaw_zero_one {d : ℕ} (hd : 0 < d)
    {E : Set (Configuration d)} (hE : MeasurableSet E)
    (hinv : ∀ a : Site d, shiftConfig (d := d) a ⁻¹' E = E) :
    disorderLaw d E = 0 ∨ disorderLaw d E = 1 := by
  classical
  set p : ℝ := (disorderLaw d).real E with hpdef
  have hp_nonneg : 0 ≤ p := measureReal_nonneg
  have hp_le_one : p ≤ 1 := real_le_one (d := d) E
  -- it suffices to show p = p ^ 2
  have hsq : p = p ^ 2 := by
    -- |p - p^2| vanishes: bound by 4ε for every ε > 0
    have hbound : ∀ ε : ℝ, 0 < ε → |p - p ^ 2| ≤ 4 * ε := by
      intro ε hε
      have hε2 : (0 : ℝ) < ε / 2 := by linarith
      obtain ⟨C, hCmem, hCapprox⟩ := exists_cylinder_approx (d := d) hE hε2
      obtain ⟨s, S, hS, rfl⟩ := (MeasureTheory.mem_measurableCylinders _).mp hCmem
      have hCmeas : MeasurableSet (MeasureTheory.cylinder s S) :=
        MeasurableSet.cylinder (α := fun _ : Site d => SingleSite) s hS
      -- real approximation bound
      have hreal : (disorderLaw d).real (E ∆ MeasureTheory.cylinder s S) < ε / 2 :=
        real_symmDiff_lt_of_approx (d := d) hE hCmeas hε2 hCapprox
      set q : ℝ := (disorderLaw d).real (MeasureTheory.cylinder s S) with hqdef
      have hq_nonneg : 0 ≤ q := measureReal_nonneg
      have hq_le_one : q ≤ 1 := real_le_one (d := d) _
      have hpq : |p - q| ≤ (disorderLaw d).real (E ∆ MeasureTheory.cylinder s S) := by
        rw [hpdef, hqdef]
        exact abs_measureReal_sub_le_measureReal_symmDiff hE.nullMeasurableSet
          hCmeas.nullMeasurableSet
      have hpq_lt : |p - q| < ε / 2 := lt_of_le_of_lt hpq hreal
      -- disjoint translate
      obtain ⟨a0, ha0⟩ := exists_ne_zero_site (d := d) hd
      obtain ⟨n, hdisj⟩ := exists_disjoint_translate s ha0
      set b : Site d := n • a0 with hbdef
      obtain ⟨S', hS', hC'trans⟩ := translated_cylinder (d := d) hS b
      -- C' is the translated cylinder
      set C' : Set (Configuration d) :=
        MeasureTheory.cylinder (s.image (fun x => x + b)) S' with hC'def
      have hC'meas : MeasurableSet C' :=
        MeasurableSet.cylinder (α := fun _ : Site d => SingleSite) _ hS'
      have hC'eq : shiftConfig (d := d) b ⁻¹' MeasureTheory.cylinder s S = C' := hC'trans
      have hdisj' : Disjoint s (s.image (fun x => x + b)) := hdisj
      -- measures of C and C' agree
      have hpres := shiftConfig_measurePreserving (d := d) b
      have hCC' : disorderLaw d C'
          = disorderLaw d (MeasureTheory.cylinder s S) := by
        have hmap : (disorderLaw d).map (shiftConfig (d := d) b) = disorderLaw d :=
          hpres.map_eq
        have hmeas : disorderLaw d (shiftConfig (d := d) b ⁻¹' MeasureTheory.cylinder s S)
            = disorderLaw d (MeasureTheory.cylinder s S) := by
          rw [← Measure.map_apply (shiftConfig_measurable (d := d) b) hCmeas, hmap]
        rw [← hmeas, hC'eq]
      have hq' : (disorderLaw d).real C' = q := by
        rw [hqdef]
        exact congrArg ENNReal.toReal hCC'
      -- E Δ C' has the same mass as E Δ C
      have hEC' : disorderLaw d (E ∆ C')
          = disorderLaw d (E ∆ MeasureTheory.cylinder s S) := by
        have hpre : shiftConfig (d := d) b ⁻¹' (E ∆ MeasureTheory.cylinder s S)
            = E ∆ C' := by
          rw [Set.preimage_symmDiff, hinv b, hC'eq]
        have hmeas : disorderLaw d
              (shiftConfig (d := d) b ⁻¹' (E ∆ MeasureTheory.cylinder s S))
            = disorderLaw d (E ∆ MeasureTheory.cylinder s S) := by
          rw [← Measure.map_apply (shiftConfig_measurable (d := d) b)
            (hE.symmDiff hCmeas), hpres.map_eq]
        rw [← hmeas, hpre]
      have hreal' : (disorderLaw d).real (E ∆ C') < ε / 2 := by
        have heq : (disorderLaw d).real (E ∆ C')
            = (disorderLaw d).real (E ∆ MeasureTheory.cylinder s S) :=
          congrArg ENNReal.toReal hEC'
        rw [heq]
        exact hreal
      -- independence of the two cylinders
      have hindep : disorderLaw d (MeasureTheory.cylinder s S ∩ C')
          = disorderLaw d (MeasureTheory.cylinder s S) * disorderLaw d C' := by
        rw [hC'def]
        exact disjoint_cylinders_indep (d := d) hdisj' hS hS'
      have hreal_cap : (disorderLaw d).real (MeasureTheory.cylinder s S ∩ C') = q ^ 2 := by
        have h1 : (disorderLaw d).real (MeasureTheory.cylinder s S ∩ C')
            = (disorderLaw d (MeasureTheory.cylinder s S ∩ C')).toReal := rfl
        rw [h1, hindep, ENNReal.toReal_mul]
        have e1 : (disorderLaw d (MeasureTheory.cylinder s S)).toReal = q :=
          hqdef.symm
        have e2 : (disorderLaw d C').toReal = q := by
          rw [hCC']
          exact e1
        rw [e1, e2]
        ring
      -- E is invariant, so E = E ∩ T⁻¹E; compare with C ∩ C'
      have hEinter : E ∩ shiftConfig (d := d) b ⁻¹' E = E := by
        rw [hinv b, Set.inter_self]
      have hsub : (E ∩ shiftConfig (d := d) b ⁻¹' E)
          ∆ (MeasureTheory.cylinder s S ∩ C')
          ⊆ ((E ∆ MeasureTheory.cylinder s S) ∪ (E ∆ C')) := by
        intro x hx
        simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_union] at hx ⊢
        have h2 : shiftConfig (d := d) b ⁻¹' E = E := hinv b
        rw [h2] at hx
        tauto
      have hmono : (disorderLaw d).real ((E ∩ shiftConfig (d := d) b ⁻¹' E)
          ∆ (MeasureTheory.cylinder s S ∩ C'))
          ≤ (disorderLaw d).real
            ((E ∆ MeasureTheory.cylinder s S) ∪ (E ∆ C')) :=
        measureReal_mono hsub
      have hunion : (disorderLaw d).real
            ((E ∆ MeasureTheory.cylinder s S) ∪ (E ∆ C'))
          ≤ (disorderLaw d).real (E ∆ MeasureTheory.cylinder s S)
            + (disorderLaw d).real (E ∆ C') :=
        measureReal_union_le _ _
      have hcap_close : |p - q ^ 2| < ε := by
        have hEq : (disorderLaw d).real (E ∩ shiftConfig (d := d) b ⁻¹' E) = p := by
          rw [hEinter, hpdef]
        have hclose : |(disorderLaw d).real (E ∩ shiftConfig (d := d) b ⁻¹' E)
            - (disorderLaw d).real (MeasureTheory.cylinder s S ∩ C')|
            ≤ (disorderLaw d).real ((E ∩ shiftConfig (d := d) b ⁻¹' E)
              ∆ (MeasureTheory.cylinder s S ∩ C')) :=
          abs_measureReal_sub_le_measureReal_symmDiff
            (hE.inter ((shiftConfig_measurable (d := d) b) hE)).nullMeasurableSet
            (hCmeas.inter hC'meas).nullMeasurableSet
        rw [hEq, hreal_cap] at hclose
        calc |p - q ^ 2| ≤ (disorderLaw d).real ((E ∩ shiftConfig (d := d) b ⁻¹' E)
                ∆ (MeasureTheory.cylinder s S ∩ C')) := hclose
          _ ≤ (disorderLaw d).real
              ((E ∆ MeasureTheory.cylinder s S) ∪ (E ∆ C')) := hmono
          _ ≤ (disorderLaw d).real (E ∆ MeasureTheory.cylinder s S)
              + (disorderLaw d).real (E ∆ C') := hunion
          _ < ε / 2 + ε / 2 := add_lt_add hreal hreal'
          _ = ε := add_halves _
      -- combine: |p - p^2| ≤ |p - q^2| + |q - p| * |q + p|
      have hfactor : |q ^ 2 - p ^ 2| = |q - p| * |q + p| := by
        rw [sq_sub_sq, abs_mul, mul_comm]
      have hqp_le : |q + p| ≤ 2 := by
        calc |q + p| ≤ |q| + |p| := abs_add_le _ _
          _ = q + p := by rw [abs_of_nonneg hq_nonneg, abs_of_nonneg hp_nonneg]
          _ ≤ 2 := by linarith
      have hpq_lt' : |q - p| < ε / 2 := by rwa [abs_sub_comm]
      calc |p - p ^ 2| = |(p - q ^ 2) + (q ^ 2 - p ^ 2)| := by ring_nf
        _ ≤ |p - q ^ 2| + |q ^ 2 - p ^ 2| := abs_add_le _ _
        _ = |p - q ^ 2| + |q - p| * |q + p| := by rw [hfactor]
        _ ≤ ε + (ε / 2) * 2 := by
          apply add_le_add hcap_close.le
          calc |q - p| * |q + p| ≤ (ε / 2) * 2 :=
                mul_le_mul hpq_lt'.le hqp_le (abs_nonneg _) (by linarith)
            _ = (ε / 2) * 2 := rfl
        _ ≤ 4 * ε := by linarith
    -- from the uniform bound, p = p^2 via distance vanishing
    have hdist : ∀ δ : ℝ, 0 < δ → dist p (p ^ 2) ≤ δ := by
      intro δ hδ
      rw [dist_eq_norm, Real.norm_eq_abs]
      have h := hbound (δ / 4) (by linarith)
      linarith
    have hpp : p = p ^ 2 := eq_of_forall_dist_le hdist
    exact hpp
  -- convert to ENNReal 0/1 via the real mass
  have hfact : p * (1 - p) = 0 := by nlinarith [hsq]
  rcases mul_eq_zero.mp hfact with h0 | h1
  · left
    have hreal0 : (disorderLaw d).real E = 0 := by rw [← hpdef]; exact h0
    exact (measureReal_eq_zero_iff).mp hreal0
  · right
    have hp1 : p = 1 := by linarith
    have hreal1 : (disorderLaw d).real E = 1 := by rw [← hpdef]; exact hp1
    have hto : ((disorderLaw d E).toReal) = 1 := by
      rwa [measureReal_def] at hreal1
    exact (ENNReal.toReal_eq_one_iff _).mp hto

/-- §9 form: a translation-invariant event of positive probability has probability one. -/
theorem disorderLaw_eq_one_of_pos {d : ℕ} (hd : 0 < d)
    {E : Set (Configuration d)} (hE : MeasurableSet E)
    (hinv : ∀ a : Site d, shiftConfig (d := d) a ⁻¹' E = E)
    (hpos : disorderLaw d E ≠ 0) :
    disorderLaw d E = 1 := by
  rcases disorderLaw_zero_one (d := d) hd hE hinv with h0 | h1
  · exact absurd h0 hpos
  · exact h1

end

end Prob
end AndersonAC
