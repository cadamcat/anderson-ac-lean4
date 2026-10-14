import AndersonAC.S78Extract.Cutoff

open scoped BigOperators
namespace AndersonAC.SolS78

open AndersonAC.S78

private lemma historyPower_mono (d : ℕ) (hd : 3 ≤ d) {s j : ℕ}
    (hsj : s ≤ j) :
    (4 : ℝ) ^ ((8 + nu d) * (s : ℝ)) ≤
      (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
  have hsCast : (s : ℝ) ≤ (j : ℝ) := by exact_mod_cast hsj
  have hnu : 0 < nu d := by
    dsimp [nu, delta]
    positivity
  have hcoef : 0 ≤ 8 + nu d := by linarith
  exact mul_le_mul_of_nonneg_left hsCast hcoef

theorem extract_witness_proof (d : ℕ) (hd : 3 ≤ d) (C : ℝ) (hC : 1 ≤ C) :
    ∃ N : ℕ, ∀ (m n₀ : ℕ) (Ω : Type) (H : PendingHistory d m n₀ Ω),
      N ≤ n₀ → H.C = C →
      ∀ j x ω, n₀ ≤ j → clearingScheduled j m → ω ∈ H.pending j x →
        ∃ L, IsWitness d m n₀ j x L ∧ ∀ a ∈ L, ω ∈ H.birth a := by
  classical
  obtain ⟨N, hNpos, hcut⟩ := exists_history_cutoff d hd C hC
  refine ⟨N, ?_⟩
  intro m n₀ Ω H hNn₀ hHC j x ω hj hclear hp
  have hrec : ∀ q, n₀ ≤ q → clearingScheduled q m → ∀ y ξ,
      ξ ∈ H.pending q y →
        ∃ L, IsWitness d m n₀ q y L ∧ ∀ a ∈ L, ξ ∈ H.birth a := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
        intro hn₀q hscheduled y ξ hpending
        by_cases hbase : q = n₀
        · subst q
          have hempty : H.pending n₀ y = ∅ := H.initial y
          have : False := by simpa [hempty] using hpending
          exact this.elim
        · have hn₀ltq : n₀ < q := by omega
          have hNq : N ≤ q := le_trans hNn₀ hn₀q
          obtain ⟨hrootCut, hpackCut⟩ := hcut q m hNq hscheduled
          have hm : 0 < m := by
            dsimp [clearingScheduled] at hscheduled
            have hNpos' : 1 ≤ N := hNpos
            omega
          let r := historyEarlier d q
          have hrq : r < q := by
            have hqpos : 0 < q := by omega
            dsimp [r, historyEarlier]
            rw [Nat.floor_lt' (Nat.ne_of_gt hqpos)]
            have hα : historyAlpha d < 1 := by
              dsimp [historyAlpha, nu, delta]
              have hdR : 3 ≤ (d : ℝ) := by exact_mod_cast hd
              have hden : 100 * (d : ℝ) > 1 := by nlinarith
              field_simp
              nlinarith
            have hqpos : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
            calc
              historyAlpha d * (q : ℝ) < 1 * (q : ℝ) :=
                mul_lt_mul_of_pos_right hα hqpos
              _ = (q : ℝ) := by ring
          have haOcc := H.latestOccurred q y ξ hpending
          rcases haOcc with ⟨haLower, haUpper, haBirth⟩
          let a := H.latest q y ξ
          have hscaleLower : n₀ < a.scale := haLower
          have hscaleUpper : a.scale ≤ q := haUpper
          by_cases hrecentRoot : r < a.scale
          · have hrootNear : physicalDistance d m y a.anchor ≤ witnessRadius q / 2 := by
              have hnear := H.latestNearby q y ξ hpending
              rw [hHC] at hnear
              have hpow := historyPower_mono d hd hscaleUpper
              have hscaled := mul_le_mul_of_nonneg_left hpow (by linarith : 0 ≤ C)
              calc
                physicalDistance d m y a.anchor ≤ C *
                    (4 : ℝ) ^ ((8 + nu d) * (a.scale : ℝ)) := hnear
                _ ≤ C * (4 : ℝ) ^ ((8 + nu d) * (q : ℝ)) := hscaled
                _ ≤ 2 * C * (4 : ℝ) ^ ((8 + nu d) * (q : ℝ)) := by
                  have hnonneg : 0 ≤ C * (4 : ℝ) ^ ((8 + nu d) * (q : ℝ)) := by positivity
                  nlinarith
                _ ≤ witnessRadius q / 2 := hrootCut
            refine ⟨{a}, IsWitness.leaf q y a hn₀ltq
              ⟨hscaleLower, hscaleUpper, hrecentRoot⟩ hrootNear, ?_⟩
            intro b hb
            have hbEq : b = a := Finset.mem_singleton.mp hb
            simpa [hbEq] using haBirth
          · have hscaleLeR : a.scale ≤ r := le_of_not_gt hrecentRoot
            rcases H.dichotomy q y ξ hn₀ltq hscheduled hpending with hnewAtQ | hcluster
            · have hnewAtQ' : a.scale = q := by simpa [a] using hnewAtQ
              exact False.elim (by omega)
            · rcases hcluster with ⟨S, hyS, hSsize, hSborn, hSnear⟩
              by_cases hrecentCluster : ∃ z ∈ S, r < (H.latest q z ξ).scale
              · obtain ⟨z, hzS, hzRecent⟩ := hrecentCluster
                have hzPending := hSborn z hzS
                rcases H.latestOccurred q z ξ hzPending with
                  ⟨hzLower, hzUpper, hzBirth⟩
                let az := H.latest q z ξ
                have htriNat : (nnGraph d m).dist y az.anchor ≤
                    (nnGraph d m).dist y z + (nnGraph d m).dist z az.anchor :=
                  (nnGraph_connected_of_pos hm).dist_triangle
                have htri : physicalDistance d m y az.anchor ≤
                    physicalDistance d m y z + physicalDistance d m z az.anchor := by
                  change ((nnGraph d m).dist y az.anchor : ℝ) ≤
                    ((nnGraph d m).dist y z : ℝ) + ((nnGraph d m).dist z az.anchor : ℝ)
                  exact_mod_cast htriNat
                have hzClose := hSnear z hzS
                rw [hHC] at hzClose
                have hzNear := H.latestNearby q z ξ hzPending
                rw [hHC] at hzNear
                have hzPow := historyPower_mono d hd hzUpper
                have hzScaled := mul_le_mul_of_nonneg_left hzPow (by linarith : 0 ≤ C)
                have hleafNear : physicalDistance d m y az.anchor ≤ witnessRadius q / 2 := by
                  calc
                    physicalDistance d m y az.anchor ≤
                        physicalDistance d m y z + physicalDistance d m z az.anchor := htri
                    _ ≤ C * (4 : ℝ) ^ ((8 + nu d) * (q : ℝ)) +
                          C * (4 : ℝ) ^ ((8 + nu d) * (q : ℝ)) :=
                        add_le_add hzClose (hzNear.trans hzScaled)
                    _ ≤ witnessRadius q / 2 := by nlinarith [hrootCut]
                refine ⟨{az}, IsWitness.leaf q y az hn₀ltq
                  ⟨hzLower, hzUpper, hzRecent⟩ hleafNear, ?_⟩
                intro b hb
                have hbEq : b = az := Finset.mem_singleton.mp hb
                simpa [hbEq] using hzBirth
              · have hallOld : ∀ z ∈ S, (H.latest q z ξ).scale ≤ r := by
                  intro z hz
                  by_contra hnot
                  exact hrecentCluster ⟨z, hz, by omega⟩
                have hn₀r : n₀ ≤ r := by
                  have hrootOld := le_trans hscaleLower.le hscaleLeR
                  omega
                have hpr : ∀ z ∈ S, ξ ∈ H.pending r z := by
                  intro z hz
                  exact H.persistence q r z ξ hn₀r hrq (hSborn z hz) (hallOld z hz)
                let R := Nat.ceil (3 * witnessRadius r)
                have hρR : 3 * witnessRadius r ≤ (R : ℝ) := by
                  exact Nat.le_ceil _
                have hpackCount : (historyChildren d q : ℝ) *
                    ((2 * R + 1) ^ d : ℕ) < (S.card : ℝ) := by
                  exact lt_trans (by simpa [R, r] using hpackCut) hSsize
                obtain ⟨centers, hcentersS, hcentersSep⟩ :=
                  exists_separated_centers hm S (3 * witnessRadius r)
                    (by
                      have hW : 0 ≤ witnessRadius r := by
                        dsimp [witnessRadius]
                        positivity
                      positivity) R (historyChildren d q) hρR hpackCount
                have hclearR : clearingScheduled r m := by
                  dsimp [clearingScheduled] at hscheduled ⊢
                  omega
                have hchildrenEx : ∀ i : Fin (historyChildren d q), ∃ L,
                    IsWitness d m n₀ r (centers i) L ∧
                    ∀ b ∈ L, ξ ∈ H.birth b := by
                  intro i
                  exact ih r hrq hn₀r hclearR (centers i) ξ (hpr (centers i) (hcentersS i))
                let leaves : Fin (historyChildren d q) → Finset (BirthLabel (Torus d m)) :=
                  fun i => Classical.choose (hchildrenEx i)
                have hchildren : ∀ i, IsWitness d m n₀ r (centers i) (leaves i) ∧
                    ∀ b ∈ leaves i, ξ ∈ H.birth b := by
                  intro i
                  exact Classical.choose_spec (hchildrenEx i)
                have hcentersNear : ∀ i,
                    physicalDistance d m y (centers i) ≤ witnessRadius q / 2 := by
                  intro i
                  have hclose := hSnear (centers i) (hcentersS i)
                  rw [hHC] at hclose
                  calc
                    physicalDistance d m y (centers i) ≤
                        C * (4 : ℝ) ^ ((8 + nu d) * (q : ℝ)) := hclose
                    _ ≤ 2 * C * (4 : ℝ) ^ ((8 + nu d) * (q : ℝ)) := by
                      have hnonneg : 0 ≤ C * (4 : ℝ) ^ ((8 + nu d) * (q : ℝ)) := by positivity
                      nlinarith
                    _ ≤ witnessRadius q / 2 := hrootCut
                let L := Finset.univ.biUnion leaves
                refine ⟨L, ?_, ?_⟩
                · exact IsWitness.branch q y hn₀ltq hn₀r hrq centers leaves
                    hcentersNear hcentersSep (fun i => (hchildren i).1)
                · intro b hb
                  rcases Finset.mem_biUnion.mp hb with ⟨i, _, hbi⟩
                  exact (hchildren i).2 b hbi
  exact hrec j hj hclear x ω hp

end AndersonAC.SolS78
