import AndersonAC.S9Inf.Algebra
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-! The conditional singleton argument in `09-spectral.tex:428–454`.
The boundary identities and PSD condition are explicit hypotheses here. -/

noncomputable section

open MeasureTheory Matrix

namespace AndersonAC.SolS9Inf

theorem rank_one_zero_boundary_forces_no_change (g a k₁ k₂ : ℂ) (h : ℝ)
    (hg : 0 < g.im) (ha : a ≠ 0) (hk₁ : k₁.im = 0) (hk₂ : k₂.im = 0)
    (hpsd : (Matrix.of (fun i j : Fin 2 =>
      if i = 0 then (if j = 0 then g.im else a.im)
      else (if j = 0 then a.im else k₁.im))).PosSemidef)
    (hrank : k₂ = k₁ - (h : ℂ) * a ^ 2 / (1 + (h : ℂ) * g)) : h = 0 := by
  by_contra hh
  have haim := AndersonAC.SolS9.boundary_psd_zero_diagonal_proof g a k₁ hk₁ hpsd
  have hareal : a = (a.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using haim
  have hane : a.re ≠ 0 := by
    intro hazero
    apply ha
    rw [hareal, hazero]
    simp
  have hpos := AndersonAC.SolS9.rank_one_imaginary_part_proof g a.re h hg hane hh
  rw [← hareal] at hpos
  have heq : k₂ = k₁ + (-(h : ℂ) * a ^ 2 / (1 + (h : ℂ) * g)) := by
    rw [hrank]
    ring
  have hkpos : 0 < k₂.im := by
    rw [heq, Complex.add_im, hk₁, zero_add]
    exact hpos
  rw [hk₂] at hkpos
  exact lt_irrefl 0 hkpos

/-- Admissible own-site values giving the positivity mismatch contain at
most one point, provided their rank-one comparison formula holds. -/
theorem mismatch_section_subsingleton {Own : Type*} (V : Own → ℝ)
    (hV : Function.Injective V) (g a k : Own → ℂ) (S : Set Own)
    (hgood : ∀ s ∈ S, 0 < (g s).im ∧ a s ≠ 0 ∧ (k s).im = 0 ∧
      (Matrix.of (fun i j : Fin 2 =>
        if i = 0 then (if j = 0 then (g s).im else (a s).im)
        else (if j = 0 then (a s).im else (k s).im))).PosSemidef)
    (hrank : ∀ s ∈ S, ∀ t ∈ S,
      k t = k s - ((V t - V s : ℝ) : ℂ) * a s ^ 2 /
        (1 + ((V t - V s : ℝ) : ℂ) * g s)) : S.Subsingleton := by
  intro s hs t ht
  apply hV
  have hh := rank_one_zero_boundary_forces_no_change (g s) (a s) (k s) (k t)
    (V t - V s) (hgood s hs).1 (hgood s hs).2.1
    (hgood s hs).2.2.1 (hgood t ht).2.2.1 (hgood s hs).2.2.2 (hrank s hs t ht)
  exact (sub_eq_zero.mp hh).symm

/-- Fubini removes a measurable bad event when its admissible own-site
sections are singletons and the own-site law has no atoms. -/
theorem null_of_subsingleton_admissible_sections {Ξ Own : Type*}
    [MeasurableSpace Ξ] [MeasurableSpace Own]
    (ν : Measure Ξ) [SFinite ν] (κ : Measure Own) [SFinite κ]
    [NullSingletonClass κ] (bad good : Set (Ξ × Own))
    (hbad : MeasurableSet bad) (hadmissible : ∀ᵐ p ∂ν.prod κ, p ∈ good)
    (hsmall : ∀ ξ, {s | (ξ, s) ∈ good ∧ (ξ, s) ∈ bad}.Subsingleton) :
    ν.prod κ bad = 0 := by
  suffices h : ∀ᵐ p ∂ν.prod κ, p ∉ bad by
    simpa only [ae_iff, not_not, Set.setOf_mem_eq] using h
  apply (Measure.ae_prod_iff_ae_ae hbad.compl).mpr
  filter_upwards [Measure.ae_ae_of_ae_prod hadmissible] with ξ hξ
  have hnot : ∀ᵐ s ∂κ, ¬ ((ξ, s) ∈ good ∧ (ξ, s) ∈ bad) := by
    simpa only [ae_iff, not_not] using (hsmall ξ).measure_zero κ
  filter_upwards [hξ, hnot] with s hs hnot
  intro hbad
  exact hnot ⟨hs, hbad⟩

end AndersonAC.SolS9Inf
