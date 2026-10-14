import AndersonAC.S9Inf.CubeShellStatement
import Mathlib.Data.Fintype.BigOperators

noncomputable section

open OAI.Anderson

namespace AndersonAC.SolS9Inf

private def cubeBox (d R : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun _ : Fin d => Finset.Icc (-((R : ℤ) + 1)) ((R : ℤ) + 1)

private def shellFaceValue (R : ℕ) (a : Fin 4) : ℤ :=
  match a.val with
  | 0 => -((R : ℤ) + 1)
  | 1 => -(R : ℤ)
  | 2 => (R : ℤ)
  | _ => (R : ℤ) + 1

private def shellFace (d R : ℕ) (j : Fin d) (a : Fin 4) : Finset (Site d) :=
  (cubeBox d R).filter fun x => x j = shellFaceValue R a

private def allShellFaces (d R : ℕ) : Finset (Site d) :=
  Finset.univ.biUnion fun p : Fin d × Fin 4 => shellFace d R p.1 p.2

private lemma shellBox_mem_iff {d R : ℕ} (x : Site d) :
    x ∈ cubeBox d R ↔ ∀ j : Fin d, |x j| ≤ (R : ℤ) + 1 := by
  simp [cubeBox, Finset.mem_Icc, abs_le]

private lemma shellFaceValue_mem (R : ℕ) (a : Fin 4) :
    shellFaceValue R a ∈ Finset.Icc (-((R : ℤ) + 1)) ((R : ℤ) + 1) := by
  fin_cases a <;> simp [shellFaceValue, Finset.mem_Icc] <;> omega

private lemma shellFace_card {d R : ℕ} (j : Fin d) (a : Fin 4) :
    (shellFace d R j a).card = (2 * R + 3) ^ (d - 1) := by
  have hcard : (Finset.Icc (-((R : ℤ) + 1)) ((R : ℤ) + 1)).card = 2 * R + 3 := by
    have hle : -((R : ℤ) + 1) ≤ ((R : ℤ) + 1) + 1 := by omega
    have h := Int.card_Icc_of_le (-((R : ℤ) + 1)) ((R : ℤ) + 1) hle
    have hz : ((2 * R + 3 : ℕ) : ℤ) = 2 * (R : ℤ) + 3 := by norm_num
    omega
  unfold shellFace cubeBox
  rw [Fintype.card_filter_piFinset_const_eq_of_mem _ _ (shellFaceValue_mem R a)]
  rw [hcard, Fintype.card_fin]

private lemma shellFaces_card_le {d R : ℕ} :
    (allShellFaces d R).card ≤ 4 * d * (2 * R + 3) ^ (d - 1) := by
  calc
    (allShellFaces d R).card ≤
        ∑ p ∈ (Finset.univ : Finset (Fin d × Fin 4)), (shellFace d R p.1 p.2).card :=
      Finset.card_biUnion_le
    _ = 4 * d * (2 * R + 3) ^ (d - 1) := by
      simp [shellFace_card, Fintype.card_fin]
      ring

private lemma shell_point_in_faces {d R : ℕ} {x : Site d}
    (hxbox : x ∈ cubeBox d R) (hxshell : ∃ j : Fin d, (R : ℤ) ≤ |x j|) :
    x ∈ allShellFaces d R := by
  obtain ⟨j, hj⟩ := hxshell
  have hbound := (shellBox_mem_iff x).mp hxbox j
  have hval : ∃ a : Fin 4, x j = shellFaceValue R a := by
    rcases le_total 0 (x j) with hnonneg | hnonpos
    · have hlow : (R : ℤ) ≤ x j := by simpa [abs_of_nonneg hnonneg] using hj
      by_cases heq : x j = (R : ℤ)
      · exact ⟨2, by simpa [shellFaceValue] using heq⟩
      · have hupper : x j ≤ (R : ℤ) + 1 := (abs_le.mp hbound).2
        have hnext : x j = (R : ℤ) + 1 := by omega
        exact ⟨3, by simpa [shellFaceValue] using hnext⟩
    · have hupper : x j ≤ -(R : ℤ) := by
        have hlow : (R : ℤ) ≤ -(x j) := by simpa [abs_of_nonpos hnonpos] using hj
        linarith
      have hlower : -((R : ℤ) + 1) ≤ x j := (abs_le.mp hbound).1
      by_cases heq : x j = -(R : ℤ)
      · exact ⟨1, by simpa [shellFaceValue] using heq⟩
      · have hnext : x j = -((R : ℤ) + 1) := by omega
        exact ⟨0, by simpa [shellFaceValue] using hnext⟩
  obtain ⟨a, hja⟩ := hval
  apply Finset.mem_biUnion.mpr
  refine ⟨(j, a), Finset.mem_univ _, ?_⟩
  simp [shellFace, hxbox, hja]

private lemma latticeDistance_zero_ge_coordinate {d R : ℕ} (x : Site d) (j : Fin d)
    (hj : (R : ℤ) ≤ |x j|) : R ≤ latticeDistance 0 x := by
  have hnat : R ≤ Int.natAbs (x j) := by
    have hcast : (R : ℤ) ≤ (Int.natAbs (x j) : ℤ) := by
      simpa only [Int.natCast_natAbs] using hj
    exact_mod_cast hcast
  unfold latticeDistance
  calc
    R ≤ Int.natAbs (x j) := hnat
    _ ≤ ∑ k : Fin d, Int.natAbs (x k) :=
      Finset.single_le_sum (s := Finset.univ)
        (f := fun k : Fin d => Int.natAbs (x k))
        (fun k hk => Nat.zero_le _) (Finset.mem_univ j)
    _ = ∑ k : Fin d, Int.natAbs ((0 : Site d) k - x k) := by
      simp only [Pi.zero_apply, zero_sub, Int.natAbs_neg]

theorem latticeCubeShell_proof : LatticeCubeShellStatement := by
  classical
  intro d _hd R
  let S : Finset (Site d) :=
    (cubeBox d R).filter fun x => ∃ j : Fin d, (R : ℤ) ≤ |x j|
  refine ⟨S, ?_, ?_, ?_⟩
  · intro x
    simp only [S, Finset.mem_filter]
    rw [shellBox_mem_iff]
  · apply le_trans (Finset.card_le_card ?_)
    · exact shellFaces_card_le
    · intro x hx
      exact shell_point_in_faces (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
  · intro x hx
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hx).2
    exact latticeDistance_zero_ge_coordinate x j hj

end AndersonAC.SolS9Inf
