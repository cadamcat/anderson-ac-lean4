import AndersonAC.S9Inf.RootCouplingStatement

/-! A coupling of the finite torus disorder with the infinite disorder that
agrees on the frozen root cube. -/

noncomputable section

open MeasureTheory OAI.Anderson

namespace AndersonAC.SolS9Inf

/-- The centered integer representative of a torus site. -/
def rootRepresentative {d m : ℕ} (q : Torus d m) : Site d :=
  fun j => (q j).valMinAbs

theorem rootRepresentative_injective {d m : ℕ} :
    Function.Injective (@rootRepresentative d m) := by
  intro q q' h
  funext j
  exact ZMod.valMinAbs_inj.mp (congrFun h j)

/-- The centered representative agrees with every site in the root cube. -/
theorem rootRepresentative_torusSite {d m : ℕ} (x : Site d)
    (hx : ∀ j : Fin d, |x j| ≤ ((sideLength m / 4 : ℕ) : ℤ)) :
    rootRepresentative (fun j => (x j : ZMod (sideLength m))) = x := by
  funext j
  apply (ZMod.valMinAbs_spec _ _).2
  constructor
  · rfl
  · have habs := abs_le.mp (hx j)
    have hfour : (sideLength m / 4) * 4 ≤ sideLength m :=
      Nat.div_mul_le_self (sideLength m) 4
    have hside : 0 < sideLength m := Nat.pos_of_ne_zero (sideLength_neZero m).out
    have hhalfNat : 2 * (sideLength m / 4) < sideLength m := by omega
    have hhalf : 2 * ((sideLength m / 4 : ℕ) : ℤ) < (sideLength m : ℤ) := by
      exact_mod_cast hhalfNat
    constructor
    · have hlow : -(sideLength m : ℤ) < 2 * x j := by nlinarith
      simpa only [mul_comm] using hlow
    · have hupp : 2 * x j < (sideLength m : ℤ) := by nlinarith
      simpa only [mul_comm] using hupp.le

theorem rootCouplingLaw_proof : RootCouplingLawStatement := by
  intro d m
  let ρ : Torus d m → Site d := rootRepresentative
  let joint : Configuration d → TorusConfiguration d m × Configuration d :=
    fun ω => (fun q => ω (ρ q), ω)
  have hρ : Function.Injective ρ := rootRepresentative_injective
  have hjoint : Measurable joint := by
    dsimp [joint]
    fun_prop
  let μ : Measure (TorusConfiguration d m × Configuration d) :=
    (disorderLaw d).map joint
  have hmatchMeas : MeasurableSet {p : TorusConfiguration d m × Configuration d |
      ∀ x : Site d, (∀ j : Fin d, |x j| ≤ ((sideLength m / 4 : ℕ) : ℤ)) →
        (p.1 (fun j => (x j : ZMod (sideLength m))) : ℝ) = potential p.2 x} := by
    classical
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun x => ?_
    have hcond : Measurable (fun _ : TorusConfiguration d m × Configuration d =>
        ∀ j : Fin d, |x j| ≤ ((sideLength m / 4 : ℕ) : ℤ)) := measurable_const
    have hleft : Measurable (fun p : TorusConfiguration d m × Configuration d =>
        (p.1 (fun j => (x j : ZMod (sideLength m))) : ℝ)) := by fun_prop
    have hright : Measurable (fun p : TorusConfiguration d m × Configuration d =>
        potential p.2 x) := by
      change Measurable (fun p : TorusConfiguration d m × Configuration d =>
        ((p.2 x : SingleSite) : ℝ))
      fun_prop
    exact (hcond.imp (hleft.eq hright)).setOf
  refine ⟨μ, ?_, ?_, ?_, ?_⟩
  · dsimp [μ]
    infer_instance
  · change ((disorderLaw d).map joint).map Prod.fst = torusLaw d m
    rw [Measure.map_map measurable_fst hjoint]
    change (disorderLaw d).map (fun ω : Configuration d => fun q : Torus d m => ω (ρ q)) = _
    change (Measure.infinitePi (fun _ : Site d => uniformSite)).map
      (fun ω : Configuration d => fun q : Torus d m => ω (ρ q)) = _
    rw [Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : Site d => uniformSite) hρ]
    rw [Measure.infinitePi_eq_pi]
    rfl
  · change ((disorderLaw d).map joint).map Prod.snd = disorderLaw d
    rw [Measure.map_map measurable_snd hjoint]
    dsimp [joint]
    change (disorderLaw d).map (fun ω : Configuration d => ω) = disorderLaw d
    exact Measure.map_id
  · dsimp only [μ]
    rw [ae_map_iff hjoint.aemeasurable hmatchMeas]
    filter_upwards with ω
    intro x hx
    have hsite : ρ (fun j => (x j : ZMod (sideLength m))) = x := by
      exact rootRepresentative_torusSite x hx
    simp only [joint, potential]
    exact congrArg (fun z : SingleSite => (z : ℝ)) (congrArg ω hsite)

end AndersonAC.SolS9Inf
