import AndersonAC.S9Inf.TranslationStatement

/-! Translation covariance of the infinite-volume Green kernel. -/

noncomputable section

open OAI.Anderson

namespace AndersonAC.SolS9Inf

private lemma shift_basis {d : ℕ} (a x : Site d) :
    shift a (basis x) = basis (x - a) := by
  apply lp.ext
  funext y
  by_cases h : y = x - a
  · subst y
    simp [basis, shift_apply, lp.single_apply, Pi.single_apply]
  · have h' : y + a ≠ x := by
      intro hya
      apply h
      calc
        y = (y + a) - a := by abel
        _ = x - a := by rw [hya]
    simp [basis, shift_apply, lp.single_apply, Pi.single_apply, h, h']

private lemma hamiltonian_translation_intertwines {d : ℕ}
    (coupling : ℝ) (ω : Configuration d) (a : Site d) :
    hamiltonian coupling (fun u => ω (u + a)) * shift a =
      shift a * hamiltonian coupling ω := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext x
  simp only [ContinuousLinearMap.mul_apply, hamiltonian_apply, shift_apply, potential]
  have hsum :
      (∑ j : Fin d, (f ((x + basisVector j) + a) + f ((x - basisVector j) + a))) =
        ∑ j : Fin d, (f ((x + a) + basisVector j) + f ((x + a) - basisVector j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [show (x + basisVector j) + a = (x + a) + basisVector j by abel,
      show (x - basisVector j) + a = (x + a) - basisVector j by abel]
  rw [hsum]

private lemma resolvent_translation_intertwines {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A B U : K →L[ℂ] K) (hAB : A * U = U * B)
    (hA : IsUnit A) (hB : IsUnit B) (v : K) :
    Ring.inverse A (U v) = U (Ring.inverse B v) := by
  have hInter (w : K) : A (U w) = U (B w) := by
    have h := congrArg (fun T : K →L[ℂ] K => T w) hAB
    simpa [ContinuousLinearMap.mul_apply] using h
  apply unit_injective A hA
  calc
    A (Ring.inverse A (U v)) = U v := unit_inverse_apply_left A hA (U v)
    _ = A (U (Ring.inverse B v)) := by
      rw [hInter, unit_inverse_apply_left B hB]

/-- Translating the configuration and the lattice sites together leaves the
Green kernel unchanged. -/
theorem greenTranslation_proof : GreenTranslationStatement := by
  intro d coupling ω a x y z hz
  let H := hamiltonian coupling ω
  let H' := hamiltonian coupling (fun u => ω (u + a))
  let U := shift a
  let A := H - z • (1 : StateSpace d →L[ℂ] StateSpace d)
  let A' := H' - z • (1 : StateSpace d →L[ℂ] StateSpace d)
  have hH : H' * U = U * H := by
    simpa [H', H, U] using hamiltonian_translation_intertwines coupling ω a
  have hA : A' * U = U * A := by
    apply ContinuousLinearMap.ext
    intro f
    change H' (U f) - z • U f = U (H f - z • f)
    have h := congrArg (fun T : StateSpace d →L[ℂ] StateSpace d => T f) hH
    have hpoint : H' (U f) = U (H f) := by
      simpa [ContinuousLinearMap.mul_apply] using h
    rw [hpoint]
    simp
  have hAunit : IsUnit A := by
    dsimp [A, H]
    exact shifted_isUnit (hamiltonian coupling ω)
      (hamiltonian_isSelfAdjoint coupling ω) z hz.ne'
  have hA'unit : IsUnit A' := by
    dsimp [A', H']
    exact shifted_isUnit (hamiltonian coupling (fun u => ω (u + a)))
      (hamiltonian_isSelfAdjoint coupling (fun u => ω (u + a))) z hz.ne'
  have hgreen (v : StateSpace d) :
      green H' z (U v) = U (green H z v) := by
    simpa [green, A', A, H', H, U] using
      resolvent_translation_intertwines A' A U hA hA'unit hAunit v
  have hUbasis : U (basis (y + a)) = basis y := by
    dsimp [U]
    rw [shift_basis]
    congr 1
    abel
  have hgreenY : green H' z (basis y) = U (green H z (basis (y + a))) := by
    rw [← hUbasis]
    exact hgreen (basis (y + a))
  have hshiftX : shift (-a) (basis x) = basis (x + a) := by
    rw [shift_basis]
    congr 1
    simp
  change inner ℂ (basis x) (green H' z (basis y)) =
    inner ℂ (basis (x + a)) (green H z (basis (y + a)))
  rw [hgreenY]
  have hinner := inner_shift (-a) (basis x) (green H z (basis (y + a)))
  rw [hshiftX, neg_neg] at hinner
  exact hinner.symm

end AndersonAC.SolS9Inf
