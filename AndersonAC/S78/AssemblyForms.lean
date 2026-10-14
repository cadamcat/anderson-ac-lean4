import AndersonAC.S78.AssemblyInduction
import AndersonAC.S78.QuadraticRepresentation

open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78
open AndersonAC.S78

def assemblyError {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin (k + 1)) (f : Torus d m → ℝ) : ℝ :=
  ∑ q : Fin k with q.val < a.val, operationEnergyError I q f

def assemblyPerturbedEnergy {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin (k + 1)) (f : Torus d m → ℝ) : ℝ :=
  endpointEnergy (I.state 0) r t f + assemblyError I a f

theorem assembly_error_zero {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (f : Torus d m → ℝ) : assemblyError I 0 f = 0 := by
  simp [assemblyError]

theorem assembly_error_succ {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin k) (f : Torus d m → ℝ) :
    assemblyError I a.succ f = assemblyError I a.castSucc f + operationEnergyError I a f := by
  classical
  have hset : (Finset.univ.filter fun q : Fin k => q.val < a.succ.val) =
      insert a (Finset.univ.filter fun q : Fin k => q.val < a.castSucc.val) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.val_succ, Fin.val_castSucc, Fin.ext_iff]
    omega
  unfold assemblyError
  rw [hset, Finset.sum_insert (by simp)]
  ring

theorem assembly_perturbed_energy_succ {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin k) (f : Torus d m → ℝ) :
    assemblyPerturbedEnergy I a.succ f =
      assemblyPerturbedEnergy I a.castSucc f + operationEnergyError I a f := by
  unfold assemblyPerturbedEnergy
  rw [assembly_error_succ]
  ring

theorem assembly_active_subset_initial {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) :
    ∀ a : Fin (k + 1), (I.state a).active ⊆ (I.state 0).active := by
  refine Fin.induction (by exact Finset.Subset.refl _) ?_
  intro a ih
  exact (I.nested a).trans ih

theorem assembly_active_nonempty {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin (k + 1)) : (I.state a).active.Nonempty := by
  have hcard : 0 < Fintype.card (Torus d m) := Fintype.card_pos
  have hcount := I.activeCount a
  apply Finset.card_pos.mp
  omega

theorem assembly_energy_nonneg {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (a : Fin (k + 1)) (f : Torus d m → ℝ) :
    0 ≤ endpointEnergy (I.state a) r t f := by
  have hc := I.positive.2.2.2.2.1
  exact ward_energy_nonneg _ _ _ _ (fun i hi => hc.le.trans (I.damping i).1)

theorem assembly_initial_kernel {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (hsp : SpatialFormInput)
    (hconn : (nnGraph d m).Connected) :
    constantKernel (I.state 0).active (endpointEnergy (I.state 0) r t) := by
  have hW := hsp (Torus d m) (nnGraph d m) hconn (I.state 0).active b I.positive.2.2.1
  have hc := I.positive.2.2.2.2.1
  intro f
  rw [← hW.2.2.1 f]
  constructor
  · intro hf
    have hlow : I.c * spatialEnergy (nnGraph d m) (I.state 0).active b f ≤ 0 := by
      simpa only [hf] using (I.initialComparison f).1
    apply le_antisymm _ (hW.1 f)
    by_contra h
    exact (not_lt_of_ge hlow) (mul_pos hc (lt_of_not_ge h))
  · intro hf
    apply le_antisymm _ (assembly_energy_nonneg I 0 f)
    simpa only [hf, mul_zero] using (I.initialComparison f).2

/-- For actual committed endpoints, a uniform relative error bound supplies
the successive Schur identity, constant kernels, and final reciprocal inverse
bounds. The two finite variational inputs are explicit proof dependencies. -/
theorem assembly_forms_of_error_upto {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (hsp : SpatialFormInput) (hfin : FiniteFormInput)
    (hconn : (nnGraph d m).Connected) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (J : ℕ)
    (herror : ∀ (a : Fin (k + 1)), a.val ≤ J → ∀ f : Torus d m → ℝ,
      |assemblyError I a f| ≤ ε * endpointEnergy (I.state 0) r t f) :
    ∀ a : Fin (k + 1), a.val ≤ J →
      constantKernel (I.state a).active (endpointEnergy (I.state a) r t) ∧
      (∀ f, endpointEnergy (I.state a) r t f =
        schurEnergy (I.state a).active (assemblyPerturbedEnergy I a) f) ∧
      (∀ y, neutral (I.state a).active y →
        (1 + ε)⁻¹ * inverseEnergy (I.state 0).active (endpointEnergy (I.state 0) r t) y ≤
          inverseEnergy (I.state a).active (endpointEnergy (I.state a) r t) y ∧
        inverseEnergy (I.state a).active (endpointEnergy (I.state a) r t) y ≤
          (1 - ε)⁻¹ * inverseEnergy (I.state 0).active (endpointEnergy (I.state 0) r t) y) := by
  let D := fun a : Fin (k + 1) => endpointEnergy (I.state a) r t
  let A := fun a : Fin (k + 1) => (I.state a).active
  have hD : ∀ a f, 0 ≤ D a f := assembly_energy_nonneg I
  have hkernel0 : constantKernel (A 0) (D 0) := assembly_initial_kernel I hsp hconn
  have hFF : ∀ a, FiniteRealForm (A a) (D a) := fun a => finite_real_form_ward _ _ _
  have hperturb : ∀ a, a.val ≤ J →
      (∀ f, 0 ≤ assemblyPerturbedEnergy I a f) ∧
        constantKernel (A 0) (assemblyPerturbedEnergy I a) := fun a ha =>
    constant_kernel_of_absolute_error (A 0) (D 0) (assemblyError I a) ε hε1
      (hD 0) hkernel0 (herror a ha)
  have hEzero : assemblyPerturbedEnergy I 0 = D 0 := by
    funext f
    dsimp only [assemblyPerturbedEnergy]
    rw [assembly_error_zero, add_zero]
  have hstate : ∀ a : Fin (k + 1), a.val ≤ J →
      FiniteRealForm (A 0) (assemblyPerturbedEnergy I a) ∧
        (∀ f, D a f = schurEnergy (A a) (assemblyPerturbedEnergy I a) f) ∧
          constantKernel (A a) (D a) := by
    refine Fin.induction ?_ ?_
    · intro _
      refine ⟨?_, ?_, hkernel0⟩
      · rw [hEzero]
        exact hFF 0
      · intro f
        rw [hEzero]
        exact (schur_energy_of_supported (A 0) (D 0) f (fun F hF =>
          ward_energy_supported _ _ _ f F hF)).symm
    · intro a ih ha
      have hprev : a.castSucc.val ≤ J := by
        have hsucc : a.val + 1 ≤ J := ha
        simpa only [Fin.val_castSucc] using Nat.le_of_succ_le hsucc
      have ih := ih hprev
      have hOldSchur := (hfin (Torus d m) (A a.castSucc) (D a.castSucc)
        (hFF a.castSucc) (hD a.castSucc) ih.2.2).2
        (A a.succ) (I.nested a) (assembly_active_nonempty I a.succ)
      have hL : FiniteRealForm (A a.succ) (operationEnergyError I a) :=
        finite_real_form_sub (A a.succ) (D a.succ)
          (schurEnergy (A a.succ) (D a.castSucc)) (hFF a.succ) hOldSchur.2.1
      have hLpad := finite_real_form_pad (A a.succ) (A 0)
        (assembly_active_subset_initial I a.succ) (operationEnergyError I a) hL
      have hE : FiniteRealForm (A 0) (assemblyPerturbedEnergy I a.succ) := by
        have h := finite_real_form_add (A 0) (assemblyPerturbedEnergy I a.castSucc)
          (operationEnergyError I a) ih.1 hLpad
        have heq : (fun f => assemblyPerturbedEnergy I a.castSucc f +
            operationEnergyError I a f) = assemblyPerturbedEnergy I a.succ :=
          funext (fun f => (assembly_perturbed_energy_succ I a f).symm)
        rw [heq] at h
        exact h
      have hidentity := assembly_schur_step (A a.succ) (A a.castSucc) (I.nested a)
        (assemblyPerturbedEnergy I a.castSucc) (operationEnergyError I a)
        (D a.castSucc) (D a.succ) (hperturb a.castSucc hprev).1
        (operation_energy_error_supported I a) ih.2.1
        (fun f => by dsimp [D, operationEnergyError]; ring)
      have heq : (fun f => assemblyPerturbedEnergy I a.castSucc f + operationEnergyError I a f) =
          assemblyPerturbedEnergy I a.succ :=
        funext (fun f => (assembly_perturbed_energy_succ I a f).symm)
      rw [heq] at hidentity
      have hkernel := (hfin (Torus d m) (A 0) (assemblyPerturbedEnergy I a.succ)
        hE (hperturb a.succ ha).1 (hperturb a.succ ha).2).2 (A a.succ)
        (assembly_active_subset_initial I a.succ) (assembly_active_nonempty I a.succ)
      refine ⟨hE, hidentity, ?_⟩
      have hfun : D a.succ = schurEnergy (A a.succ) (assemblyPerturbedEnergy I a.succ) :=
        funext hidentity
      rw [hfun]
      exact hkernel.1
  intro a ha
  refine ⟨(hstate a ha).2.2, (hstate a ha).2.1, ?_⟩
  intro y hy
  have hsubset := assembly_active_subset_initial I a
  have hsum : ∀ f : Torus d m → ℝ, (∑ i ∈ A 0, y i * f i) = ∑ i ∈ A a, y i * f i := by
    intro f
    exact (Finset.sum_subset hsubset (fun i hi hni => by rw [hy.1 i hni, zero_mul])).symm
  have hy0 : neutral (A 0) y := by
    refine ⟨fun i hi => hy.1 i (fun hia => hi (hsubset hia)), ?_⟩
    have hs : (∑ i ∈ A 0, y i) = ∑ i ∈ A a, y i :=
      (Finset.sum_subset hsubset (fun i hi hni => hy.1 i hni)).symm
    rw [hs]
    exact hy.2
  have habove := (hfin (Torus d m) (A 0) (D 0) (hFF 0) (hD 0) hkernel0).1 y hy0
  simp_rw [hsum] at habove
  have hcompare : ∀ f, (1 - ε) * D 0 f ≤ assemblyPerturbedEnergy I a f ∧
      assemblyPerturbedEnergy I a f ≤ (1 + ε) * D 0 f := by
    intro f
    have he := herror a ha f
    dsimp only [assemblyPerturbedEnergy]
    change (1 - ε) * D 0 f ≤ D 0 f + assemblyError I a f ∧
      D 0 f + assemblyError I a f ≤ (1 + ε) * D 0 f
    constructor <;> linarith [neg_abs_le (assemblyError I a f), le_abs_self (assemblyError I a f)]
  have hbound := schur_relative_inverse_comparison (A a) (D 0) (assemblyPerturbedEnergy I a)
    y ε hε0 hε1 (hD 0) (ward_energy_homogeneous _ _ _) habove hcompare
  have hfun : D a = schurEnergy (A a) (assemblyPerturbedEnergy I a) := funext (hstate a ha).2.1
  change (1 + ε)⁻¹ * inverseEnergy (A 0) (D 0) y ≤ inverseEnergy (A a) (D a) y ∧
    inverseEnergy (A a) (D a) y ≤ (1 - ε)⁻¹ * inverseEnergy (A 0) (D 0) y
  rw [inverse_energy_change_active (A a) (A 0) hsubset (D 0) y (fun i hi hni => hy.1 i hni), hfun]
  exact hbound

theorem assembly_forms_of_error {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (hsp : SpatialFormInput) (hfin : FiniteFormInput)
    (hconn : (nnGraph d m).Connected) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (herror : ∀ (a : Fin (k + 1)) (f : Torus d m → ℝ),
      |assemblyError I a f| ≤ ε * endpointEnergy (I.state 0) r t f) :
    ∀ a : Fin (k + 1),
      constantKernel (I.state a).active (endpointEnergy (I.state a) r t) ∧
      (∀ f, endpointEnergy (I.state a) r t f =
        schurEnergy (I.state a).active (assemblyPerturbedEnergy I a) f) ∧
      (∀ y, neutral (I.state a).active y →
        (1 + ε)⁻¹ * inverseEnergy (I.state 0).active (endpointEnergy (I.state 0) r t) y ≤
          inverseEnergy (I.state a).active (endpointEnergy (I.state a) r t) y ∧
        inverseEnergy (I.state a).active (endpointEnergy (I.state a) r t) y ≤
          (1 - ε)⁻¹ * inverseEnergy (I.state 0).active (endpointEnergy (I.state 0) r t) y) := by
  intro a
  exact assembly_forms_of_error_upto I hsp hfin hconn ε hε0 hε1 k
    (fun a ha => herror a) a (by omega)

/-- The old comparison required by the local cutoff argument follows from
earlier-prefix errors, without assuming the current operation succeeds. -/
theorem assembly_pre_comparison_upto {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) (hsp : SpatialFormInput) (hfin : FiniteFormInput)
    (hconn : (nnGraph d m).Connected) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (J : ℕ)
    (herror : ∀ (a : Fin (k + 1)), a.val ≤ J → ∀ f : Torus d m → ℝ,
      |assemblyError I a f| ≤ ε * endpointEnergy (I.state 0) r t f) :
    ∀ (a : Fin (k + 1)), a.val ≤ J → ∀ F : Torus d m → ℝ,
      endpointEnergy (I.state a) r t F ≤
        (1 + ε) * I.C * spatialEnergy (nnGraph d m) (I.state 0).active b F := by
  intro a ha F
  have hforms := assembly_forms_of_error_upto I hsp hfin hconn ε hε0 hε1 J herror a ha
  have hpositive := (constant_kernel_of_absolute_error (I.state 0).active
    (endpointEnergy (I.state 0) r t) (assemblyError I a) ε hε1
    (assembly_energy_nonneg I 0) (assembly_initial_kernel I hsp hconn) (herror a ha)).1
  have hbdd : BddBelow ((assemblyPerturbedEnergy I a) ''
      {H : Torus d m → ℝ | ∀ i ∈ (I.state a).active, H i = F i}) :=
    ⟨0, by rintro e ⟨H, hH, rfl⟩; exact hpositive H⟩
  calc
    _ = schurEnergy (I.state a).active (assemblyPerturbedEnergy I a) F := hforms.2.1 F
    _ ≤ assemblyPerturbedEnergy I a F := csInf_le hbdd ⟨F, (by intro i hi; rfl), rfl⟩
    _ ≤ (1 + ε) * endpointEnergy (I.state 0) r t F := by
      have he := herror a ha F
      dsimp [assemblyPerturbedEnergy]
      linarith [le_abs_self (assemblyError I a F)]
    _ ≤ (1 + ε) * (I.C * spatialEnergy (nnGraph d m) (I.state 0).active b F) :=
      mul_le_mul_of_nonneg_left (I.initialComparison F).2 (by linarith)
    _ = _ := by ring

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.assembly_initial_kernel
#print axioms AndersonAC.SolS78.assembly_forms_of_error
#print axioms AndersonAC.SolS78.assembly_forms_of_error_upto
#print axioms AndersonAC.SolS78.assembly_pre_comparison_upto
