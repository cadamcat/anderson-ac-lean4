import AndersonAC.AgentS78.Construction.TileCoverStatement

/-!
# a `TilePlan` from the tile-cover statement. From `TileCoverStatement d`: for every box (`n₀ ≥ 1`,
`u ∈ (1/4, 1]`) a `TilePlan` whose stage covers are the restrictions along `id` (all ports,
energy `Λ`, distance `pullDist id`, `b = t_{n₀} t`), with the cover clauses of `TileGoodCore`
(`cover_b`, `cover_C`, `shell`, `tile_card`, `inner_card`), the tile diameters of
`blockRun_of_runOps` (`hdiam`, constant `Ch = 4⁶ C`), and, for every injective port family
`ι : P → Port d m` (e.g. the active ports at a stage start), a restricted `S45.TileCover` on
`P` with the same tiles (`ι x ∈ tile`), so both cover-domain designs are served.
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

variable {d m : ℕ}

theorem siteAt_some_cover (S : Finset (Torus d m)) (v : ℕ) (hv : v < S.card) :
    ∃ i ∈ S, siteAt S v = some i := by
  unfold siteAt
  set L := (S.map (siteRank d m).toEmbedding).sort (· ≤ ·) with hL
  have hlen : L.length = S.card := by rw [hL, Finset.length_sort, Finset.card_map]
  have hv' : v < L.length := hlen ▸ hv
  rw [List.getElem?_eq_getElem hv']
  have hmem : L[v] ∈ S.map (siteRank d m).toEmbedding :=
    (Finset.mem_sort _).mp (List.getElem_mem hv')
  obtain ⟨a, ha, hae⟩ := Finset.mem_map.mp hmem
  refine ⟨a, ha, ?_⟩
  simp only [Option.map_some, Option.some.injEq]
  rw [← hae]; simp

/-- The anchor of a nonempty tile lies in the tile. -/
theorem tileAnchor_mem {t : ℝ} (C : StageCover d m t) (T : Fin C.cover.count)
    (h : (tileSites C T).Nonempty) : tileAnchor C T ∈ tileSites C T := by
  obtain ⟨i, hi, hs⟩ := siteAt_some_cover (tileSites C T) 0 (Finset.card_pos.mpr h)
  unfold tileAnchor
  rw [hs]
  exact hi

theorem stageScale_pos (u : ℝ) (hu : 0 < u) (a m : ℕ) : 0 < stageScale u a m := by
  unfold stageScale; positivity

theorem stageScale_le_two (u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) (a m : ℕ) :
    stageScale u a m ≤ 2 := by
  unfold stageScale
  have h1 : u / (4 : ℝ) ^ a ≤ u := div_le_self hu.le (one_le_pow₀ (by norm_num))
  have h2 : u / (4 : ℝ) ^ m ≤ u := div_le_self hu.le (one_le_pow₀ (by norm_num))
  linarith

theorem sweepScale_pos_cover (u : ℝ) (hu : 0 < u) (m j : ℕ) : 0 < sweepScale u m j := by
  unfold sweepScale; split_ifs <;> exact stageScale_pos u hu _ _

theorem sweepScale_le_two (u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) (m j : ℕ) :
    sweepScale u m j ≤ 2 := by
  unfold sweepScale; split_ifs <;> exact stageScale_le_two u hu hu1 _ _

/-- `t ≥ u 4^{-j}` for the sweep with post-sweep index `j`. -/
theorem sweepScale_ge (u : ℝ) (hu : 0 < u) (m j : ℕ) : u / (4 : ℝ) ^ j ≤ sweepScale u m j := by
  unfold sweepScale stageScale
  have h4 : ∀ a b : ℕ, a ≤ b → u / (4 : ℝ) ^ b ≤ u / (4 : ℝ) ^ a := fun a b hab =>
    div_le_div_of_nonneg_left hu.le (by positivity) (pow_le_pow_right₀ (by norm_num) hab)
  split_ifs with h
  · have := h4 m j (by unfold IsFinalSweep at h; omega)
    have : 0 ≤ u / (4 : ℝ) ^ m := by positivity
    linarith
  · have := h4 (j - 1) j (Nat.sub_le j 1)
    have : 0 ≤ u / (4 : ℝ) ^ m := by positivity
    linarith

/-- `t^{-6} ≤ 4⁶ 4^{(8+ν)j}` for `u > 1/4`. -/
theorem power_sweepScale_le (u : ℝ) (hu : 1 / 4 < u) (m j : ℕ) :
    S45.power (sweepScale u m j) (-6) ≤ (4 : ℝ) ^ 6 * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)) := by
  have hu0 : 0 < u := by linarith
  have ht := sweepScale_ge u hu0 m j
  have hlow : (4 : ℝ)⁻¹ ^ (j + 1) ≤ sweepScale u m j := by
    have : (4 : ℝ)⁻¹ ^ (j + 1) ≤ u / (4 : ℝ) ^ j := by
      rw [inv_pow, pow_succ, div_eq_mul_inv]
      rw [mul_inv, mul_comm]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hpos : (0 : ℝ) < (4 : ℝ)⁻¹ ^ (j + 1) := by positivity
  have h1 : S45.power (sweepScale u m j) (-6) ≤ ((4 : ℝ)⁻¹ ^ (j + 1)) ^ (-6 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hpos hlow (by norm_num)
  have h2 : ((4 : ℝ)⁻¹ ^ (j + 1)) ^ (-6 : ℝ) = (4 : ℝ) ^ 6 * (4 : ℝ) ^ (6 * (j : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.inv_rpow (by norm_num),
      ← Real.rpow_neg (by norm_num)]
    rw [show -((((j + 1 : ℕ) : ℝ)) * (-6 : ℝ)) = 6 + 6 * (j : ℝ) by push_cast; ring,
      Real.rpow_add (by norm_num)]
    norm_num
  have hnu : 0 ≤ nu d := by unfold nu delta; positivity
  have h3 : (4 : ℝ) ^ (6 * (j : ℝ)) ≤ (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  rw [h2] at h1
  nlinarith [show (0 : ℝ) < 4 ^ 6 by norm_num]


/-- Shell bounds are monotone in the constant. -/
theorem shellBounds_mono {P : Type*} [Fintype P] {dist : P → P → ℝ} {C C' : ℝ}
    (h : S45.ShellBounds d C dist) (hC : C ≤ C') : S45.ShellBounds d C' dist where
  nonneg := h.nonneg
  symmetric := h.symmetric
  triangle := h.triangle
  self := h.self
  count := fun u hu hu1 i => (h.count u hu hu1 i).trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hu.le _))
  second := fun u hu hu1 i => (h.second u hu hu1 i).trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hu.le _))

/-- The cover facts of one stage cover (the `TileGoodCore` cover clauses, the tile diameters of
`blockRun_of_runOps`, and the restrictions to injective port families with the same tiles). -/
structure StageCoverFacts (C Ch u : ℝ) (n₀ j : ℕ) (S : StageCover d m (sweepScale u m j)) :
    Prop where
  b_eq : S.b = stageScale u n₀ m * sweepScale u m j
  b_pos : 0 < S.b
  b_le : S.b ≤ sweepScale u m j
  C_eq : S.C = C
  dist_eq : S.dist = pullDist (id : Port d m → Port d m)
  site_eq : S.cover.site = Prod.fst
  energy_eq : S.cover.energy = torusEnergy d m
  shell : S45.ShellBounds d C S.dist
  tile_card : ∀ T, ((tileSites S T).card : ℝ) ≤ C * S45.power (sweepScale u m j) (-6 * (d : ℝ))
  inner_card : ∀ T, ((S.cover.inner T).card : ℝ) ≤
    C * S45.power (sweepScale u m j) (-6 * (d : ℝ))
  diam : ∀ T, ∀ y ∈ tileSites S T,
    physicalDistance d m y (tileAnchor S T) ≤ Ch * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ))
  restrict : ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (ι : Q → Port d m),
    Function.Injective ι →
      S45.ShellBounds d C (pullDist ι) ∧
      ∃ cov : S45.TileCover (P := Q) (I := Torus d m) d (sweepScale u m j) S.b C (pullDist ι),
        cov.site = (fun x => (ι x).1) ∧ cov.energy = torusEnergy d m ∧
        ∃ e : Fin cov.count ≃ Fin S.cover.count,
          (∀ T x, x ∈ cov.tile T ↔ ι x ∈ S.cover.tile (e T)) ∧
          (∀ T x, x ∈ cov.inner T ↔ ι x ∈ S.cover.inner (e T)) ∧
          (∀ T, ((cov.inner T).card : ℝ) ≤ C * S45.power (sweepScale u m j) (-6 * (d : ℝ)))

/-- A tile plan for every box. `restrict` gives the corresponding cover on an
embedded port family. -/
theorem exists_tilePlan (hTC : TileCoverStatement d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (m n₀ : ℕ) (u : ℝ), 1 ≤ n₀ → n₀ ≤ m → 1 / 4 < u → u ≤ 1 →
      ∃ P : TilePlan d m, P.n₀ = n₀ ∧ P.u = u ∧
        ∀ j, StageCoverFacts C ((4 : ℝ) ^ 6 * C) P.u P.n₀ j (P.cover j) := by
  obtain ⟨C, hC1, hTC⟩ := hTC
  refine ⟨C, hC1, fun m n₀ u hn₀ hn₀m hu hu1 => ?_⟩
  have hu0 : 0 < u := by linarith
  have hj : ∀ j, ∃ S : StageCover d m (sweepScale u m j),
      StageCoverFacts C ((4 : ℝ) ^ 6 * C) u n₀ j S := by
    intro j
    set t := sweepScale u m j with ht
    have ht0 : 0 < t := sweepScale_pos_cover u hu0 m j
    obtain ⟨τ, -, htile, -, hdiam, hall⟩ := hTC m t ht0 (sweepScale_le_two u hu0 hu1 m j)
    set b := stageScale u n₀ m * t with hb
    have hb0 : 0 < b := mul_pos (stageScale_pos u hu0 n₀ m) ht0
    have hs1 : stageScale u n₀ m ≤ 1 := by
      unfold stageScale
      have h1 : u / (4 : ℝ) ^ n₀ ≤ u / 4 := by
        apply div_le_div_of_nonneg_left hu0.le (by norm_num)
        calc (4 : ℝ) = 4 ^ 1 := by norm_num
          _ ≤ 4 ^ n₀ := pow_le_pow_right₀ (by norm_num) hn₀
      have h2 : u / (4 : ℝ) ^ m ≤ u / 4 := by
        apply div_le_div_of_nonneg_left hu0.le (by norm_num)
        calc (4 : ℝ) = 4 ^ 1 := by norm_num
          _ ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    obtain ⟨hshell, hcov⟩ := hall (Port d m) id Function.injective_id
    obtain ⟨cov, hsite, hen, e, htileiff, hinneriff, hinnercard⟩ := hcov b hb0
    refine ⟨⟨b, C, pullDist id, cov⟩, ?_⟩
    have hts : ∀ T, tileSites (⟨b, C, pullDist id, cov⟩ : StageCover d m t) T ⊆ τ.tile (e T) := by
      intro T i hi
      simp only [tileSites, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact (htileiff T _).1 hi
    have hpw := power_sweepScale_le (d := d) u hu m j
    refine
      { b_eq := rfl
        b_pos := hb0
        b_le := by
          show b ≤ t
          rw [hb]
          calc stageScale u n₀ m * t ≤ 1 * t := mul_le_mul_of_nonneg_right hs1 ht0.le
            _ = t := one_mul t
        C_eq := rfl
        dist_eq := rfl
        site_eq := hsite
        energy_eq := hen
        shell := hshell
        tile_card := fun T => le_trans (by exact_mod_cast Finset.card_le_card (hts T)) (htile _)
        inner_card := hinnercard
        diam := fun T y hy => ?_
        restrict := fun Q _ _ ι hι => ?_ }
    · have ha := tileAnchor_mem (⟨b, C, pullDist id, cov⟩ : StageCover d m t) T ⟨y, hy⟩
      have h1 := hdiam (e T) y (hts T hy) _ (hts T ha)
      have hC0 : (0 : ℝ) ≤ C := by linarith
      calc physicalDistance d m y _ ≤ C * S45.power t (-6) := h1
        _ ≤ C * ((4 : ℝ) ^ 6 * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ))) :=
          mul_le_mul_of_nonneg_left hpw hC0
        _ = (4 : ℝ) ^ 6 * C * (4 : ℝ) ^ ((8 + nu d) * (j : ℝ)) := by ring
    · obtain ⟨hsh', hcov'⟩ := hall Q ι hι
      obtain ⟨cov', h1, h2, e', h3, h4, h5⟩ := hcov' b hb0
      refine ⟨hsh', cov', h1, h2, e'.trans e.symm, fun T x => ?_, fun T x => ?_, h5⟩
      · rw [h3, htileiff]; simp
      · rw [h4, hinneriff]; simp
  choose S hS using hj
  exact ⟨⟨n₀, u, S⟩, rfl, rfl, hS⟩

end AndersonAC.AgentS78
