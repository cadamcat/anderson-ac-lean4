import AndersonAC.AgentS78.Construction.StagePhaseDone
import AndersonAC.AgentS78Geo.TrialSchur
import AndersonAC.AgentS78Geo.Initial

/-!
# The DONE exit of a clearing attempt: Combes–Thomas decay of the committed endpoint

agent-s78donea. The first conclusion of `ClearingDoneAnalyticStatement`
(07-assembly.tex:390–433; 06-clearing.tex:214–238): a damped endpoint `s` whose real matrix
differs from the direct hops `J` only between active sites at zero terminal distance for the
terminal set `univ \ s.active` obeys the Combes–Thomas bound in that terminal distance
(`endpoint_ct`), hence, through the terminal metric, in the physical distance (`endpoint_ct_phys`).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78.DoneA

open AndersonAC.S78 AndersonAC.AgentS78Geo

variable {d m : ℕ}

/-- **Combes–Thomas in the terminal distance** for a damped endpoint with terminal hop
structure. -/
theorem endpoint_ct (s : Endpoint (Torus d m)) (r : Torus d m → ℂ) (t c : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hc : 0 < c) (hr : ∀ i, c ≤ (r i).im)
    (hD : IsDampedEndpoint s r t)
    (J : Matrix (Torus d m) (Torus d m) ℝ) (hJs : J.IsSymm) (hJ1 : ∀ a b, |J a b| ≤ 1)
    (hJadj : ∀ a b, J a b ≠ 0 → (nnGraph d m).Adj a b)
    (hhop : ∀ a ∈ s.active, ∀ b ∈ s.active, s.M a b ≠ ((J a b : ℝ) : ℂ) →
      terminalDistance (nnGraph d m) (Finset.univ \ s.active) a b = 0)
    (i k : Torus d m) :
    ‖normalizedInverse s t i k‖ ≤ (4 / (3 * c)) / Real.sqrt t *
      Real.exp (-(AndersonAC.SolS6.localizationRate d c) * t *
        terminalDistance (nnGraph d m) (Finset.univ \ s.active) i k) := by
  have hG : (nnGraph d m).Connected := AndersonAC.SolS78.nnGraph_connected_proof
  set E := Finset.univ \ s.active with hE
  set coll := terminalDistance (nnGraph d m) E with hcoll
  have hRHS : 0 ≤ (4 / (3 * c)) / Real.sqrt t *
      Real.exp (-(AndersonAC.SolS6.localizationRate d c) * t * coll i k) := by positivity
  obtain ⟨hMs, hz, hBG, hGB⟩ := hD
  by_cases hik : i ∈ s.active ∧ k ∈ s.active
  swap
  · have h0 : s.g i k = 0 := hz i k (by tauto)
    simp only [normalizedInverse, Matrix.smul_apply, h0, smul_zero, norm_zero]
    exact hRHS
  obtain ⟨hi, hk⟩ := hik
  set A := s.active with hA
  let Mr : Matrix A A ℝ := Matrix.of fun a b => (s.M a b).re
  let JA : Matrix A A ℝ := Matrix.of fun a b => J a b
  let K : Matrix A A ℝ := Mr - JA
  have hMJK : Mr = JA + K := by ext a b; simp [K]
  have hJs' : JA.IsSymm := Matrix.IsSymm.ext fun a b => by
    simp only [JA, Matrix.of_apply]; exact hJs.apply _ _
  have hKs : K.IsSymm := Matrix.IsSymm.ext fun a b => by
    simp only [K, Mr, JA, Matrix.sub_apply, Matrix.of_apply]
    have h1 := (hMs (b : Torus d m) a).1
    have h2 := hJs.apply (a : Torus d m) b
    rw [h1, h2]
  have hdeg : ∀ a, ((Finset.univ.filter (fun b => JA a b ≠ 0)).card : ℝ) ≤ 2 * d :=
    card_filter_le_of_adj d (fun u S hS => nnGraph_degree_le u S hS)
      (fun a : A => a.val) Subtype.val_injective JA
      (fun a b h => hJadj _ _ (by simpa [JA] using h))
  have hnn : ∀ a b, 0 ≤ coll a b := fun a b => AndersonAC.AgentS78Geo.terminalDistance_nonneg _ _ _ _
  have hsymm : ∀ a b, coll a b = coll b a := fun a b => terminalDistance_symm hG _ _ _
  have htri : ∀ a b c, coll a c ≤ coll a b + coll b c := fun a b c =>
    terminalDistance_triangle hG _ _ _ _
  have hJρ : ∀ a b : A, JA a b ≠ 0 → |coll a k - coll b k| ≤ 1 := by
    intro a b hab
    have h1 : coll a b ≤ 1 :=
      terminalDistance_adj_le_one _ _ (hJadj _ _ (by simpa [JA] using hab))
    rw [abs_sub_le_iff]
    constructor
    · linarith [htri a b k]
    · linarith [htri b a k, hsymm a b]
  have hKρ : ∀ a b : A, K a b ≠ 0 → coll a k = coll b k := by
    intro a b hab
    have hne : s.M a b ≠ ((J a b : ℝ) : ℂ) := by
      intro h; apply hab
      simp only [K, Mr, JA, Matrix.sub_apply, Matrix.of_apply, h, Complex.ofReal_re, sub_self]
    have h0' := hhop a.val a.2 b.val b.2 hne
    apply le_antisymm
    · linarith [htri a b k]
    · linarith [htri b a k, hsymm a b]
  have hct := combes_thomas_entry d JA K hJs' hKs (fun a b => hJ1 _ _) hdeg t c ht ht1 hc
    (fun a : A => r a) (fun a => hr a) (fun l => coll l k) hJρ hKρ ⟨i, hi⟩ ⟨k, hk⟩
  have hkk : coll k k = 0 := terminalDistance_self _ _ _
  simp only [hkk, sub_zero] at hct
  have hBeq : s.M.submatrix (fun a : A => a.val) (fun a : A => a.val) -
      (t : ℂ) • Matrix.diagonal (fun a : A => r a.val) =
      AndersonAC.S6.dampedMatrix (JA + K) t (fun a : A => r a) := by
    rw [← hMJK]
    ext a b
    simp only [AndersonAC.S6.dampedMatrix, Mr, Matrix.sub_apply, Matrix.submatrix_apply,
      Matrix.map_apply, Matrix.of_apply]
    congr 1
    apply Complex.ext
    · simp
    · simp [(hMs a.val b.val).2]
  rw [hBeq] at hGB
  have hinv := Matrix.inv_eq_left_inv hGB
  have hgik : s.g i k = (AndersonAC.S6.dampedMatrix (JA + K) t (fun a : A => r a))⁻¹
      ⟨i, hi⟩ ⟨k, hk⟩ := by
    rw [hinv]; rfl
  rw [normalizedInverse, Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), hgik]
  have hsq : Real.sqrt t * (4 / (3 * (t * c))) = (4 / (3 * c)) / Real.sqrt t := by
    have hs := Real.sqrt_pos.mpr ht
    have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
    calc Real.sqrt t * (4 / (3 * (t * c))) =
          Real.sqrt t * ((4 / (3 * c)) / (Real.sqrt t * Real.sqrt t)) := by rw [hss]; ring
      _ = (4 / (3 * c)) / Real.sqrt t := by field_simp
  calc Real.sqrt t * ‖(AndersonAC.S6.dampedMatrix (JA + K) t (fun a : A => r a))⁻¹ ⟨i, hi⟩ ⟨k, hk⟩‖
      ≤ Real.sqrt t * (4 / (3 * (t * c)) *
          Real.exp (-(AndersonAC.SolS6.localizationRate d c * t * coll i k))) :=
        mul_le_mul_of_nonneg_left hct (Real.sqrt_nonneg _)
    _ = _ := by rw [← mul_assoc, hsq, neg_mul, neg_mul]

/-- **Combes–Thomas in the physical distance** through the terminal metric, with any
constants `CA ≥ 4/(3c)` and `0 < cA ≤ localizationRate d c`. -/
theorem endpoint_ct_phys (s : Endpoint (Torus d m)) (r : Torus d m → ℂ) (t c CA cA : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hc : 0 < c) (hr : ∀ i, c ≤ (r i).im)
    (hCA : 4 / (3 * c) ≤ CA) (hcA0 : 0 < cA) (hcA : cA ≤ AndersonAC.SolS6.localizationRate d c)
    (hD : IsDampedEndpoint s r t)
    (hmetric : ∀ v w, physicalDistance d m v w / 2 - t ^ (-1.03 : ℝ) ≤
      terminalDistance (nnGraph d m) (Finset.univ \ s.active) v w)
    (J : Matrix (Torus d m) (Torus d m) ℝ) (hJs : J.IsSymm) (hJ1 : ∀ a b, |J a b| ≤ 1)
    (hJadj : ∀ a b, J a b ≠ 0 → (nnGraph d m).Adj a b)
    (hhop : ∀ a ∈ s.active, ∀ b ∈ s.active, s.M a b ≠ ((J a b : ℝ) : ℂ) →
      terminalDistance (nnGraph d m) (Finset.univ \ s.active) a b = 0)
    (i k : Torus d m) :
    ‖normalizedInverse s t i k‖ ≤
      CA / Real.sqrt t * Real.exp (-cA * t * max (physicalDistance d m i k / 2 - t ^ (-1.03 : ℝ)) 0) := by
  have h := endpoint_ct s r t c ht ht1 hc hr hD J hJs hJ1 hJadj hhop i k
  refine h.trans ?_
  set TD := terminalDistance (nnGraph d m) (Finset.univ \ s.active) i k
  have hTD0 : 0 ≤ TD := AndersonAC.AgentS78Geo.terminalDistance_nonneg _ _ _ _
  have hmax : max (physicalDistance d m i k / 2 - t ^ (-1.03 : ℝ)) 0 ≤ TD :=
    max_le (hmetric i k) hTD0
  have hmax0 : 0 ≤ max (physicalDistance d m i k / 2 - t ^ (-1.03 : ℝ)) 0 := le_max_right _ _
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  apply mul_le_mul (div_le_div_of_nonneg_right hCA hst.le) _ (Real.exp_pos _).le
    (div_nonneg ((by positivity : (0 : ℝ) ≤ 4 / (3 * c)).trans hCA) hst.le)
  apply Real.exp_le_exp.mpr
  have h1 : cA * t * max (physicalDistance d m i k / 2 - t ^ (-1.03 : ℝ)) 0 ≤
      AndersonAC.SolS6.localizationRate d c * t * TD := by
    apply mul_le_mul (mul_le_mul_of_nonneg_right hcA ht.le) hmax hmax0
    exact mul_nonneg (hcA0.le.trans hcA) ht.le
  linarith

end AndersonAC.AgentS78.DoneA
