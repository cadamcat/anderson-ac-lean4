import AndersonAC.S9.Core

/-! Own-site law and complementary configurations for conditional §9
arguments. The original potential is uniformly distributed on [-1,1]. -/

noncomputable section

open MeasureTheory OAI.Anderson
open scoped ENNReal

namespace AndersonAC.SolS9

abbrev ComplementConfiguration (d : ℕ) (x : Site d) :=
  {y : Site d // y ≠ x} → SingleSite

def complementLaw (d : ℕ) (x : Site d) : Measure (ComplementConfiguration d x) :=
  Measure.infinitePi (fun _ => uniformSite)

def restoreSite {d : ℕ} (x : Site d) (ξ : ComplementConfiguration d x)
    (s : SingleSite) : Configuration d := by
  classical
  exact fun y => if h : y = x then s else ξ ⟨y, h⟩

def restoreSiteEquiv (d : ℕ) (x : Site d) :
    (ComplementConfiguration d x × SingleSite) ≃ᵐ Configuration d := by
  classical
  refine
    { toEquiv :=
        { toFun := fun p => restoreSite x p.1 p.2
          invFun := fun ω => (fun y => ω y, ω x)
          left_inv := ?_
          right_inv := ?_ }
      measurable_toFun := ?_
      measurable_invFun := ?_ }
  · intro p
    apply Prod.ext
    · funext y
      simp [restoreSite, y.property]
    · simp [restoreSite]
  · intro ω
    funext y
    by_cases hy : y = x
    · subst y
      simp [restoreSite]
    · simp [restoreSite, hy]
  · apply measurable_pi_lambda
    intro y
    by_cases hy : y = x
    · subst y
      simpa [restoreSite] using
        (measurable_snd : Measurable (fun p : ComplementConfiguration d x × SingleSite => p.2))
    · simpa [restoreSite, hy, Function.comp_def] using
        ((measurable_pi_apply ⟨y, hy⟩).comp
          (measurable_fst : Measurable (fun p : ComplementConfiguration d x × SingleSite => p.1)))
  · have hcomp : Measurable (fun ω : Configuration d =>
        fun y : {y : Site d // y ≠ x} => ω (y : Site d)) :=
      measurable_pi_lambda fun y => measurable_pi_apply (y : Site d)
    exact hcomp.prodMk (measurable_pi_apply x)

/-- Transport almost-sure statements through the site split without
requiring that the statement itself be a measurable predicate. -/
theorem ae_restoreSite_iff (d : ℕ) (x : Site d)
    (hLaw : MeasurePreserving
      (fun p : ComplementConfiguration d x × SingleSite => restoreSite x p.1 p.2)
      ((complementLaw d x).prod uniformSite) (disorderLaw d))
    (P : Configuration d → Prop) :
    (∀ᵐ p ∂(complementLaw d x).prod uniformSite, P (restoreSite x p.1 p.2)) ↔
      ∀ᵐ ω ∂disorderLaw d, P ω := by
  constructor
  · intro hp
    rw [← hLaw.map_eq, ae_iff]
    have hfn : (restoreSiteEquiv d x : (ComplementConfiguration d x × SingleSite) → Configuration d) =
        (fun p => restoreSite x p.1 p.2) := rfl
    rw [← hfn]
    rw [(restoreSiteEquiv d x).measurableEmbedding.map_apply]
    rw [hfn]
    simpa only [ae_iff, Set.preimage_setOf_eq] using hp
  · intro hP
    exact hLaw.quasiMeasurePreserving.ae hP

theorem uniformOwnSite_no_atoms (coupling : ℝ) (h : coupling ≠ 0) (a : ℝ) :
    uniformSite {s : SingleSite | coupling * (s : ℝ) = a} = 0 := by
  have hset : {s : SingleSite | coupling * (s : ℝ) = a} =
      (fun s : SingleSite => (s : ℝ)) ⁻¹' {a / coupling} := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hs
      apply (eq_div_iff h).mpr
      simpa [mul_comm] using hs
    · intro hs
      simpa [mul_comm] using (eq_div_iff h).mp hs
  rw [hset, ← Measure.map_apply measurable_subtype_coe (measurableSet_singleton _),
    uniformSite_map_val, Measure.smul_apply]
  simp

end AndersonAC.SolS9
