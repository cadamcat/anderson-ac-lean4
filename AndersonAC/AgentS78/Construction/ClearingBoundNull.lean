import AndersonAC.AgentS78.Construction.ClearingTrial
import AndersonAC.AgentS78.Construction.TrueSpace
import AndersonAC.S2.PrincipalInvertibility
import AndersonAC.S2.BinaryProduct
import AndersonAC.S2.SignBlocks

/-!
# Clearing first-failure bound (agent-s78clrbound): the null set of singular trial pivots

For a fixed record `x`, the §6 clearing trial on the active sites needs every principal block
of `M₀ + diag ξ(ω)` to be invertible (`S6.construct_stopped_trial`, `hterminal`), where
`M₀` is the real active block of `x.endpoint.M` and `ξ_i(ω)` is the `λ`-coupled true residual
of site `i` from its prefix height. This holds only almost surely (02-state.tex:220–229):

* `binaryValue_eq_mul`: `binaryValue c a = c · binaryValue 1 a`;
* `shiftedValues_law`: the shifted digit values `ω ↦ (binaryValue 1 (digits of i from h i))_i`
  have the law of the true configuration (`S2.binary_true_product_law`, the shift is an
  injective reindexing of the independent signs);
* `clrTerminal_ae`: for any real matrix `M₀` on the active sites and any heights, almost surely
  every principal block of `M₀ + diag (trueResidual λ ω i (h i))` is invertible (`λ ≠ 0`), via
  the diffuse-diagonal lemma `SolS2.principal_diagonal_invertible` after the rescaling
  `M₀ + diag(c v) = diag c · (diag c⁻¹ M₀ + diag v)`.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources sourcesLaw binaryValue binarySuffix)

variable {d m : ℕ}

theorem binaryValue_eq_mul (c : ℝ) (a : ℕ → Bool) :
    binaryValue c a = c * binaryValue 1 a := by
  unfold binaryValue
  rw [← tsum_mul_left]
  congr 1
  funext k
  ring

/-- The true residual is the rescaled shifted digit value. -/
theorem trueResidual_eq_mul {M : ℕ → ℕ} (lam : ℝ) (ω : RandomSources (Torus d m) M)
    (y : Torus d m) (h : ℕ) :
    trueResidual lam ω y h = lam / (2 : ℝ) ^ h * binaryValue 1 (fun k => ω.1 (Sum.inl (y, h + k))) := by
  unfold trueResidual
  rw [AndersonAC.S2.binarySuffix_eq_scaled, binaryValue_eq_mul]
  rfl

/-- The shifted digit values of all sites. -/
def shiftedValues {M : ℕ → ℕ} (h : Torus d m → ℕ) (ω : RandomSources (Torus d m) M) :
    Torus d m → ℝ :=
  fun i => binaryValue 1 (fun k => ω.1 (Sum.inl (i, h i + k)))

theorem shiftedValues_measurable (M : ℕ → ℕ) (h : Torus d m → ℕ) :
    Measurable (shiftedValues (M := M) h) := by
  apply Measurable.of_eval; intro i
  exact (AndersonAC.S2.binaryValue_measurable 1).comp
    (Measurable.of_eval fun k => (measurable_pi_apply (Sum.inl (i, h i + k))).comp measurable_fst)

/-- **The shifted digit values have the law of the true configuration.** -/
theorem shiftedValues_law (M : ℕ → ℕ) (h : Torus d m → ℕ) :
    (sourcesLaw (Torus d m) M).map (shiftedValues h) =
      (OAI.Anderson.torusLaw d m).map (fun ω i => (ω i : ℝ)) := by
  let V := fun a : (Torus d m × ℕ) → Bool => fun i => binaryValue 1 (fun k => a (i, k))
  have hV : Measurable V := Measurable.of_eval fun i =>
    (AndersonAC.S2.binaryValue_measurable 1).comp (Measurable.of_eval fun k => measurable_pi_apply (i, k))
  let e : Torus d m × ℕ → AndersonAC.S2.SignIndex (Torus d m) := fun x => Sum.inl (x.1, h x.1 + x.2)
  have he : Function.Injective e := by
    rintro ⟨i, k⟩ ⟨i', k'⟩ hx
    simp only [e, Sum.inl.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, hk⟩ := hx
    simp only [Prod.mk.injEq, true_and]
    omega
  let X := fun ω : RandomSources (Torus d m) M => fun x : Torus d m × ℕ => ω.1 (e x)
  have hX : Measurable X := Measurable.of_eval fun x =>
    (measurable_pi_apply (e x)).comp measurable_fst
  let X0 := fun ω : RandomSources (Torus d m) M => fun x : Torus d m × ℕ => ω.1 (Sum.inl x)
  have hX0 : Measurable X0 := Measurable.of_eval fun x =>
    (measurable_pi_apply (Sum.inl x)).comp measurable_fst
  have h1 : (sourcesLaw (Torus d m) M).map (shiftedValues h) =
      (Measure.infinitePi (fun _ : Torus d m × ℕ => (PMF.uniformOfFintype Bool).toMeasure)).map V := by
    change (sourcesLaw (Torus d m) M).map (V ∘ X) = _
    rw [← Measure.map_map hV hX, AndersonAC.SolS2.sources_signs_map (Torus d m) e he]
  have h0 : (sourcesLaw (Torus d m) M).map (fun ω i =>
      binaryValue 1 (fun k => ω.1 (Sum.inl (i, k)))) =
      (Measure.infinitePi (fun _ : Torus d m × ℕ => (PMF.uniformOfFintype Bool).toMeasure)).map V := by
    change (sourcesLaw (Torus d m) M).map (V ∘ X0) = _
    rw [← Measure.map_map hV hX0, AndersonAC.SolS2.sources_signs_map (Torus d m) Sum.inl
      Sum.inl_injective]
  rw [h1, ← h0, AndersonAC.S2.binary_true_product_law]

/-- The real principal block `(M₀ + diag ξ)_T` of the clearing trial. -/
def clrPrincipal {ι : Type} [DecidableEq ι] (M0 : Matrix ι ι ℝ) (ξ : ι → ℝ) (T : Finset ι) :
    Matrix {i // i ∈ T} {i // i ∈ T} ℝ :=
  (M0 + Matrix.diagonal ξ).submatrix (fun i : {i // i ∈ T} => (i : ι))
    (fun i : {i // i ∈ T} => (i : ι))

/-- Rescaling: if `c` has no zero entry and every principal block of `diag c⁻¹ M₀ + diag v` is
invertible, so is every principal block of `M₀ + diag (c v)`. -/
theorem clrPrincipal_isUnit_of_scaled {ι : Type} [Fintype ι] [DecidableEq ι]
    (M0 : Matrix ι ι ℝ) (c v : ι → ℝ) (hc : ∀ i, c i ≠ 0)
    (hK : ∀ U : Finset ι, IsUnit
      (((Matrix.diagonal (fun i => ((c i)⁻¹ : ℂ)) * M0.map (fun a : ℝ => (a : ℂ))) +
        (1 : ℂ) • Matrix.diagonal (fun i => ((v i : ℝ) : ℂ))).submatrix
          (fun i : U => (i : ι)) (fun i : U => (i : ι))))
    (T : Finset ι) :
    IsUnit (clrPrincipal M0 (fun i => c i * v i) T).det := by
  have hU := hK T
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hU
  rw [isUnit_iff_ne_zero]
  intro h0
  have hmap : (clrPrincipal M0 (fun i => c i * v i) T).map (fun a : ℝ => (a : ℂ)) =
      Matrix.diagonal (fun i : {i // i ∈ T} => ((c i : ℝ) : ℂ)) *
        (((Matrix.diagonal (fun i => ((c i)⁻¹ : ℂ)) * M0.map (fun a : ℝ => (a : ℂ))) +
          (1 : ℂ) • Matrix.diagonal (fun i => ((v i : ℝ) : ℂ))).submatrix
            (fun i : {i // i ∈ T} => (i : ι)) (fun i : {i // i ∈ T} => (i : ι))) := by
    ext a b
    rw [Matrix.diagonal_mul]
    simp only [clrPrincipal, Matrix.map_apply, Matrix.submatrix_apply, Matrix.add_apply,
      Matrix.diagonal_mul, Matrix.diagonal_apply, one_smul]
    have hca : ((c a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc a
    by_cases hab : a = b
    · subst hab
      simp only [ite_true]
      push_cast
      field_simp
    · have hab' : (a : ι) ≠ (b : ι) := fun h => hab (Subtype.ext h)
      simp only [hab', ite_false, add_zero]
      field_simp
  have hdet := congrArg Matrix.det hmap
  have hdm : ((clrPrincipal M0 (fun i => c i * v i) T).map (fun a : ℝ => (a : ℂ))).det =
      (((clrPrincipal M0 (fun i => c i * v i) T).det : ℝ) : ℂ) := by
    have := RingHom.map_det Complex.ofRealHom (clrPrincipal M0 (fun i => c i * v i) T)
    rw [RingHom.mapMatrix_apply] at this
    exact this.symm
  rw [hdm, Matrix.det_mul, Matrix.det_diagonal, h0, Complex.ofReal_zero] at hdet
  have hprod : (∏ i : {i // i ∈ T}, ((c i : ℝ) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast hc i
  exact hU ((mul_eq_zero.mp hdet.symm).resolve_left hprod)

/-- **Almost surely every principal block of the clearing trial is invertible.** -/
theorem clrTerminal_ae (M : ℕ → ℕ) (A : Finset (Torus d m))
    (M0 : Matrix {i // i ∈ A} {i // i ∈ A} ℝ) (lam : ℝ) (hlam : lam ≠ 0) (h : Torus d m → ℕ) :
    ∀ᵐ ω ∂sourcesLaw (Torus d m) M, ∀ T : Finset {i // i ∈ A},
      IsUnit (clrPrincipal M0 (fun i => trueResidual lam ω i.val (h i.val)) T).det := by
  classical
  set c : {i // i ∈ A} → ℝ := fun i => lam / (2 : ℝ) ^ h i.val with hc_def
  have hc : ∀ i, c i ≠ 0 := fun i => div_ne_zero hlam (pow_ne_zero _ (by norm_num))
  let K : Matrix {i // i ∈ A} {i // i ∈ A} ℂ :=
    Matrix.diagonal (fun i => ((c i)⁻¹ : ℂ)) * M0.map (fun a : ℝ => (a : ℂ))
  -- the diffuse diagonal lemma on the active coordinates
  have hdiff := AndersonAC.SolS2.principal_diagonal_invertible {i // i ∈ A} K 1 one_ne_zero
  have hres := AndersonAC.SolS2.uniform_principal_restriction_preserving (Torus d m) A
  have hpull : ∀ᵐ w : OAI.Anderson.TorusConfiguration d m ∂OAI.Anderson.torusLaw d m,
      ∀ U : Finset {i // i ∈ A}, IsUnit
        ((K + ((1 : ℝ) : ℂ) • Matrix.diagonal (fun i : {i // i ∈ A} => ((w i.val : ℝ) : ℂ))).submatrix
          (fun i : U => (i : {i // i ∈ A})) (fun i : U => (i : {i // i ∈ A}))) :=
    hres.quasiMeasurePreserving.ae hdiff
  -- transport to the values `v = (w i : ℝ)`
  have hemb := singleSite_val_embedding (Torus d m)
  have hv : ∀ᵐ v ∂(OAI.Anderson.torusLaw d m).map (fun (w : OAI.Anderson.TorusConfiguration d m) i =>
      (w i : ℝ)), ∀ U : Finset {i // i ∈ A}, IsUnit
        ((K + ((1 : ℝ) : ℂ) • Matrix.diagonal (fun i : {i // i ∈ A} => ((v i.val : ℝ) : ℂ))).submatrix
          (fun i : U => (i : {i // i ∈ A})) (fun i : U => (i : {i // i ∈ A}))) := by
    rw [hemb.ae_map_iff]
    exact hpull
  rw [← shiftedValues_law M h] at hv
  have hω := ae_of_ae_map (shiftedValues_measurable M h).aemeasurable hv
  filter_upwards [hω] with ω hω T
  have heq : (fun i : {i // i ∈ A} => trueResidual lam ω i.val (h i.val)) =
      fun i => c i * shiftedValues h ω i.val := by
    funext i
    rw [trueResidual_eq_mul]
    rfl
  rw [heq]
  refine clrPrincipal_isUnit_of_scaled M0 c (fun i => shiftedValues h ω i.val) hc ?_ T
  intro U
  simpa [K] using hω U

end AndersonAC.AgentS78
