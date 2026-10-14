import AndersonAC.GT.Cauchy

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! Dyson's Lemma 2 for the Golden–Thompson inequality (Forrester–Thompson 2014 §2.2).

Words are `List Bool` of fixed length `2*r`; `false` means `X`, `true` means `Xᴴ`.
Main result `dyson_word_bound`: every word product has
`‖Tr P‖ ≤ Tr((X*Xᴴ)^r).re`.
-/

/-- Factor of a word: `false` is `X`, `true` is `Xᴴ`. -/
def wFactor (X : Matrix n n ℂ) (b : Bool) : Matrix n n ℂ :=
  if b then Xᴴ else X

/-- Negating a letter takes the conjugate transpose. -/
lemma wFactor_neg (X : Matrix n n ℂ) (b : Bool) :
    wFactor X (!b) = (wFactor X b)ᴴ := by
  cases b <;> simp [wFactor, Matrix.conjTranspose_conjTranspose]

/-- Product of a word. -/
def wProd (X : Matrix n n ℂ) (l : List Bool) : Matrix n n ℂ :=
  (l.map (wFactor X)).prod

lemma wProd_nil (X : Matrix n n ℂ) : wProd X [] = 1 := rfl

lemma wProd_cons (X : Matrix n n ℂ) (b : Bool) (l : List Bool) :
    wProd X (b :: l) = wFactor X b * wProd X l := by
  simp [wProd, List.prod_cons]

lemma wProd_append (X : Matrix n n ℂ) (l₁ l₂ : List Bool) :
    wProd X (l₁ ++ l₂) = wProd X l₁ * wProd X l₂ := by
  simp [wProd, List.map_append, List.prod_append]

/-- Conjugate transpose of a word product is the reversed negated word product. -/
lemma wProd_conjTranspose (X : Matrix n n ℂ) (l : List Bool) :
    (wProd X l)ᴴ = wProd X ((l.map (! ·)).reverse) := by
  induction l with
  | nil => simp [wProd]
  | cons b l ih =>
    have hmap : ((b :: l).map (! ·)) = (!b) :: ((l.map (! ·))) := rfl
    have h1 : wFactor X (!b) = wProd X [!b] := by simp [wProd_cons, wProd_nil]
    rw [hmap, List.reverse_cons, wProd_cons, Matrix.conjTranspose_mul, ih,
      (wFactor_neg X b).symm, h1, ← wProd_append]

/-- Words of fixed length. -/
def wordDom (N : ℕ) := {l : List Bool // l.length = N}

/-- Fixed-length word lists form a finite type. -/
noncomputable instance wordDom_fintype (N : ℕ) : Fintype (wordDom N) := by
  classical
  refine Fintype.ofEquiv (Fin N → Bool) ?_
  exact
  { toFun := fun v => ⟨List.ofFn v, List.length_ofFn⟩
    invFun := fun l i => l.val[i.val]'(by rw [l.prop]; exact i.isLt)
    left_inv := by
      intro v
      funext i
      show (List.ofFn v)[i.val]'(by rw [List.length_ofFn]; exact i.isLt) = v i
      rw [List.getElem_ofFn]
    right_inv := by
      intro l
      apply Subtype.ext
      show List.ofFn (fun i : Fin N => l.val[i.val]'(by rw [l.prop]; exact i.isLt)) = l.val
      apply List.ext_getElem
      · rw [List.length_ofFn, l.prop]
      · intro i h₁ h₂
        rw [List.getElem_ofFn] }

/-- Linear alternation count (consecutive differences, no wraparound). -/
def linAlt : List Bool → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (if a != b then 1 else 0) + linAlt (b :: rest)

lemma linAlt_cons_cons (a b : Bool) (rest : List Bool) :
    linAlt (a :: b :: rest) = (if a != b then 1 else 0) + linAlt (b :: rest) := rfl

lemma linAlt_single (x : Bool) : linAlt [x] = 0 := rfl

/-- Boundary term between two lists (1 if both nonempty with different ends). -/
def midAlt (A B : List Bool) : ℕ :=
  match A.getLast?, B.head? with
  | some a, some b => if a != b then 1 else 0
  | _, _ => 0

/-- `linAlt` over a concatenation. -/
lemma linAlt_append (A B : List Bool) :
    linAlt (A ++ B) = linAlt A + midAlt A B + linAlt B := by
  induction A generalizing B with
  | nil => simp [linAlt, midAlt]
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases B with
      | nil => simp [linAlt, midAlt]
      | cons y ys => simp [linAlt, midAlt]
    | cons y ys =>
      have hmid : midAlt (y :: ys) B = midAlt (x :: y :: ys) B := by
        simp [midAlt]
      have hcons : (x :: y :: ys) ++ B = x :: y :: (ys ++ B) := rfl
      have htail : y :: (ys ++ B) = (y :: ys) ++ B := rfl
      rw [hcons]
      show (if x != y then 1 else 0) + linAlt (y :: (ys ++ B)) = _
      rw [htail, ih]
      simp [linAlt]
      omega

/-- Cyclic alternation count (includes wraparound pair). -/
def altCyc (l : List Bool) : ℕ :=
  linAlt l + match l.getLast?, l.head? with
    | some a, some b => if a != b then 1 else 0
    | _, _ => 0

/-- Reverse + negate preserves `linAlt` (for the `Q†Q` counting). -/
lemma linAlt_revMap_not (Q : List Bool) :
    linAlt ((Q.map (!·)).reverse) = linAlt Q := by
  induction Q with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      have hrev : ((x :: y :: ys).map (!·)).reverse
          = ((y :: ys).map (!·)).reverse ++ [!x] := by simp
      have hmid : midAlt (((y :: ys).map (!·)).reverse) [!x]
          = (if x != y then 1 else 0) := by
        have e1 : (((y :: ys).map (!·)).reverse).getLast? = some (!(y)) := by
          simp [List.getLast?_reverse]
        have e2 : ([!x].head? : Option Bool) = some (!(x)) := rfl
        have heq : ((!y) != (!(x))) = (x != y) := by cases x <;> cases y <;> rfl
        simp only [midAlt, e1, e2, heq]
      rw [hrev, linAlt_append, ih, hmid, linAlt_cons_cons, linAlt_single]
      omega

/-- The `Q†` word (reversed, negated). Its product is `(wProd Q)ᴴ`. -/
def qdag (Q : List Bool) : List Bool := (Q.map (!·)).reverse

lemma qdag_length (Q : List Bool) : (qdag Q).length = Q.length := by
  simp [qdag]

lemma qdag_ne_nil {Q : List Bool} (hQ : Q ≠ []) : qdag Q ≠ [] := by
  simp [qdag, hQ]

lemma linAlt_qdag (Q : List Bool) : linAlt (qdag Q) = linAlt Q :=
  linAlt_revMap_not Q

lemma qdag_head? (Q : List Bool) :
    (qdag Q).head? = Option.map (!·) Q.getLast? := by
  simp [qdag, List.head?_reverse, List.getLast?_map]

lemma qdag_getLast? (Q : List Bool) :
    (qdag Q).getLast? = Option.map (!·) Q.head? := by
  simp [qdag, List.getLast?_reverse, List.head?_map]

/-- `wProd` of the `Q†Q` word. -/
lemma wProd_qdag_append (X : Matrix n n ℂ) (Q : List Bool) :
    wProd X (qdag Q ++ Q) = (wProd X Q)ᴴ * wProd X Q := by
  have hqq : qdag Q = (Q.map (!·)).reverse := rfl
  rw [wProd_append, hqq, wProd_conjTranspose]

/-- Negation always differs: the `Q†Q` boundaries always alternate. -/
lemma bool_not_ne_self (b : Bool) : ((!b) != b) = true := by cases b <;> rfl

lemma bool_ne_not_self (b : Bool) : ((b) != (!b)) = true := by cases b <;> rfl

/-- Cyclic count of a `Q†Q` word. -/
lemma altCyc_qdag_append (Q : List Bool) (hQ : Q ≠ []) :
    altCyc (qdag Q ++ Q) = 2 * linAlt Q + 2 := by
  have hQd : qdag Q ≠ [] := qdag_ne_nil hQ
  have gQ : Q.getLast? = some (Q.getLast hQ) := List.getLast?_eq_some_getLast hQ
  have hQh : Q.head? = some (Q.head hQ) := List.head?_eq_some_head hQ
  have gQd : (qdag Q).getLast? = some (!(Q.head hQ)) := by
    simp [qdag_getLast?, hQh]
  have hQd' : (qdag Q).head? = some (!(Q.getLast hQ)) := by
    simp [qdag_head?, gQ]
  have hmid : midAlt (qdag Q) Q = 1 := by
    simp [midAlt, gQd, hQh, bool_ne_not_self]
  have oL : (qdag Q ++ Q).getLast? = some (Q.getLast hQ) := by
    simp [List.getLast?_append, gQ, gQd]
  have oH : (qdag Q ++ Q).head? = some (!(Q.getLast hQ)) := by
    simp [List.head?_append, hQd', hQh]
  have hwrap : (match (qdag Q ++ Q).getLast?, (qdag Q ++ Q).head? with
      | some a, some b => if a != b then 1 else 0
      | _, _ => 0) = 1 := by
    simp [oL, oH, bool_not_ne_self]
  have hlin : linAlt (qdag Q ++ Q) = linAlt (qdag Q) + 1 + linAlt Q := by
    rw [linAlt_append, hmid]
  show linAlt (qdag Q ++ Q) + (match (qdag Q ++ Q).getLast?, (qdag Q ++ Q).head? with
      | some a, some b => if a != b then 1 else 0
      | _, _ => 0) = 2 * linAlt Q + 2
  rw [hlin, linAlt_qdag, hwrap]
  omega

/-- Cyclic count is symmetric under swapping concatenated halves (nonempty). -/
lemma altCyc_append_comm {A B : List Bool} (hA : A ≠ []) (hB : B ≠ []) :
    altCyc (A ++ B) = altCyc (B ++ A) := by
  have hAB : A ++ B ≠ [] := by simp [hA]
  have hBA : B ++ A ≠ [] := by simp [hB]
  simp only [altCyc, linAlt_append, midAlt, List.getLast?_append, List.head?_append,
    List.getLast?_eq_some_getLast hA, List.getLast?_eq_some_getLast hB,
    List.head?_eq_some_head hA, List.head?_eq_some_head hB,
    List.getLast?_eq_some_getLast hAB, List.getLast?_eq_some_getLast hBA,
    List.head?_eq_some_head hAB, List.head?_eq_some_head hBA]
  have eL : (A ++ B).getLast hAB = B.getLast hB := by
    simp [List.getLast_append hAB, List.isEmpty_iff, hB]
  have eH : (A ++ B).head hAB = A.head hA := by
    simp [List.head_append hAB, List.isEmpty_iff, hA]
  have eL' : (B ++ A).getLast hBA = A.getLast hA := by
    simp [List.getLast_append hBA, List.isEmpty_iff, hA]
  have eH' : (B ++ A).head hBA = B.head hB := by
    simp [List.head_append hBA, List.isEmpty_iff, hB]
  rw [eL, eH, eL', eH']
  omega

/-- Either some consecutive pair is equal, or all consecutive pairs differ. -/
lemma find_double (l : List Bool) :
    (∃ t : ℕ, ∃ h1 : t < l.length, ∃ h2 : t + 1 < l.length,
      l[t]'h1 = l[t + 1]'h2) ∨
    (∀ i : ℕ, ∀ h1 : i < l.length, ∀ h2 : i + 1 < l.length,
      ¬ l[i]'h1 = l[i + 1]'h2) := by
  by_cases h : ∃ t : ℕ, ∃ h1 : t < l.length, ∃ h2 : t + 1 < l.length,
      l[t]'h1 = l[t + 1]'h2
  · exact Or.inl h
  · right
    push_neg at h
    exact h

/-- Trace is invariant under list rotation (via drop/take split). -/
lemma trace_wProd_rotate (X : Matrix n n ℂ) (l : List Bool) (s : ℕ)
    (hs : s ≤ l.length) :
    Matrix.trace (wProd X (l.rotate s)) = Matrix.trace (wProd X l) := by
  have hsplit : l = l.take s ++ l.drop s := (List.take_append_drop s l).symm
  calc Matrix.trace (wProd X (l.rotate s))
      = Matrix.trace (wProd X (l.drop s ++ l.take s)) := by
        rw [List.rotate_eq_drop_append_take hs]
    _ = Matrix.trace (wProd X (l.drop s) * wProd X (l.take s)) := by
        rw [wProd_append]
    _ = Matrix.trace (wProd X (l.take s) * wProd X (l.drop s)) :=
        Matrix.trace_mul_comm _ _
    _ = Matrix.trace (wProd X (l.take s ++ l.drop s)) := by
        rw [wProd_append]
    _ = Matrix.trace (wProd X l) := by rw [List.take_append_drop]

/-- Cyclic count is invariant under rotation. -/
lemma altCyc_rotate (l : List Bool) (s : ℕ) (hs : s ≤ l.length)
    (h1 : l.take s ≠ []) (h2 : l.drop s ≠ []) :
    altCyc (l.rotate s) = altCyc l := by
  have hsplit : l = l.take s ++ l.drop s := (List.take_append_drop s l).symm
  calc altCyc (l.rotate s)
      = altCyc (l.drop s ++ l.take s) := by
        rw [List.rotate_eq_drop_append_take hs]
    _ = altCyc (l.take s ++ l.drop s) := (altCyc_append_comm h1 h2).symm
    _ = altCyc l := by rw [List.take_append_drop]

/-- Unfolding equation for `altCyc`. -/
lemma altCyc_unfold (l : List Bool) : altCyc l
    = linAlt l + (match l.getLast?, l.head? with
      | some a, some b => if a != b then 1 else 0
      | _, _ => 0) := rfl

/-- The wraparound term is at most 1. -/
lemma wrapAlt_le_one (l : List Bool) :
    (match l.getLast?, l.head? with
      | some a, some b => (if a != b then 1 else 0)
      | _, _ => 0) ≤ 1 := by
  cases h1 : l.getLast? with
  | none => simp [h1]
  | some a =>
    cases h2 : l.head? with
    | none => simp [h1, h2]
    | some b =>
      simp only [h1, h2, reduceCtorEq]
      split <;> omega

/-- Transfer step: a middle double forces a strictly larger local budget,
contradicting maximality. `Q R` are the two halves (`|Q|=|R|=r`) with equal
middle values; `M` is the maximal `‖Tr‖` and `kmax` the maximal `altCyc`
among maximizers; the current concatenation attains both. -/
lemma transfer_contra (X : Matrix n n ℂ) (r : ℕ) (hr : 1 ≤ r)
    (Q R : List Bool) (hlenQ : Q.length = r) (hlenR : R.length = r)
    (hQ : Q ≠ []) (hR : R ≠ [])
    (hdbl : Q.getLast hQ = R.head hR)
    (M : ℝ) (kmax : ℕ)
    (hM : ∀ w : wordDom (2 * r), ‖Matrix.trace (wProd X w.val)‖ ≤ M)
    (hK : ∀ w : wordDom (2 * r),
      ‖Matrix.trace (wProd X w.val)‖ = M → altCyc w.val ≤ kmax)
    (hP : ‖Matrix.trace (wProd X Q * wProd X R)‖ = M)
    (hKcur : altCyc (Q ++ R) = kmax) :
    False := by
  have h2rQ : (qdag Q ++ Q).length = 2 * r := by
    simp [qdag_length, hlenQ]; omega
  have h2rR : (qdag R ++ R).length = 2 * r := by
    simp [qdag_length, hlenR]; omega
  have h2rQR : (Q ++ R).length = 2 * r := by
    simp [hlenQ, hlenR]; omega
  -- Lemma 1 applied to the split
  have hCS := trace_mul_norm_sq_le (wProd X Q) (wProd X R)
  rw [hP] at hCS
  -- nonnegativity and maximality bounds for the two factors
  have hnnA : (0:ℝ) ≤ (Matrix.trace ((wProd X Q)ᴴ * wProd X Q)).re :=
    trace_conjTranspose_mul_self_re_nonneg _
  have hnnB : (0:ℝ) ≤ (Matrix.trace ((wProd X R)ᴴ * wProd X R)).re :=
    trace_conjTranspose_mul_self_re_nonneg _
  have hM0 : (0:ℝ) ≤ M := by
    have hw0 := hM ⟨List.replicate (2 * r) false, List.length_replicate⟩
    exact le_trans (norm_nonneg _) hw0
  have hAle : (Matrix.trace ((wProd X Q)ᴴ * wProd X Q)).re ≤ M := by
    have e : (Matrix.trace ((wProd X Q)ᴴ * wProd X Q)).re
        = (Matrix.trace (wProd X (qdag Q ++ Q))).re := by
      rw [wProd_qdag_append]
    rw [e]
    calc (Matrix.trace (wProd X (qdag Q ++ Q))).re
        ≤ ‖Matrix.trace (wProd X (qdag Q ++ Q))‖ := Complex.re_le_norm _
      _ ≤ M := hM ⟨qdag Q ++ Q, h2rQ⟩
  have hBle : (Matrix.trace ((wProd X R)ᴴ * wProd X R)).re ≤ M := by
    have e : (Matrix.trace ((wProd X R)ᴴ * wProd X R)).re
        = (Matrix.trace (wProd X (qdag R ++ R))).re := by
      rw [wProd_qdag_append]
    rw [e]
    calc (Matrix.trace (wProd X (qdag R ++ R))).re
        ≤ ‖Matrix.trace (wProd X (qdag R ++ R))‖ := Complex.re_le_norm _
      _ ≤ M := hM ⟨qdag R ++ R, h2rR⟩
  -- force both factors to equal M
  have hforce : (Matrix.trace ((wProd X Q)ᴴ * wProd X Q)).re = M
      ∧ (Matrix.trace ((wProd X R)ᴴ * wProd X R)).re = M := by
    set A := (Matrix.trace ((wProd X Q)ᴴ * wProd X Q)).re with hAdef
    set B := (Matrix.trace ((wProd X R)ᴴ * wProd X R)).re with hBdef
    have hprod : M ^ 2 ≤ A * B := hCS
    by_cases hm : M = 0
    · rw [hm] at hAle hBle ⊢
      exact ⟨le_antisymm hAle hnnA, le_antisymm hBle hnnB⟩
    · have hMpos : (0:ℝ) < M := lt_of_le_of_ne hM0 (Ne.symm hm)
      have hAM : M ≤ A := by
        have h1 : M * M ≤ A * M :=
          calc M * M = M ^ 2 := by rw [sq]
            _ ≤ A * B := hprod
            _ ≤ A * M := mul_le_mul_of_nonneg_left hBle hnnA
        exact le_of_mul_le_mul_right h1 hMpos
      have hBM : M ≤ B := by
        have h1 : M * M ≤ M * B :=
          calc M * M = M ^ 2 := by rw [sq]
            _ ≤ A * B := hprod
            _ ≤ M * B := mul_le_mul_of_nonneg_right hAle hnnB
        exact le_of_mul_le_mul_left h1 hMpos
      exact ⟨le_antisymm hAle hAM, le_antisymm hBle hBM⟩
  -- L1 and L2 attain M
  have hT1 : ‖Matrix.trace (wProd X (qdag Q ++ Q))‖ = M := by
    apply le_antisymm (hM ⟨qdag Q ++ Q, h2rQ⟩)
    calc M = (Matrix.trace ((wProd X Q)ᴴ * wProd X Q)).re := hforce.1.symm
      _ = (Matrix.trace (wProd X (qdag Q ++ Q))).re := by
          rw [wProd_qdag_append]
      _ ≤ ‖Matrix.trace (wProd X (qdag Q ++ Q))‖ := Complex.re_le_norm _
  have hT2 : ‖Matrix.trace (wProd X (qdag R ++ R))‖ = M := by
    apply le_antisymm (hM ⟨qdag R ++ R, h2rR⟩)
    calc M = (Matrix.trace ((wProd X R)ᴴ * wProd X R)).re := hforce.2.symm
      _ = (Matrix.trace (wProd X (qdag R ++ R))).re := by
          rw [wProd_qdag_append]
      _ ≤ ‖Matrix.trace (wProd X (qdag R ++ R))‖ := Complex.re_le_norm _
  -- their counts are bounded by kmax
  have hK1 : altCyc (qdag Q ++ Q) ≤ kmax := hK ⟨qdag Q ++ Q, h2rQ⟩ hT1
  have hK2 : altCyc (qdag R ++ R) ≤ kmax := hK ⟨qdag R ++ R, h2rR⟩ hT2
  rw [altCyc_qdag_append Q hQ] at hK1
  rw [altCyc_qdag_append R hR] at hK2
  -- current count: middle double kills the middle term
  have hmid0 : midAlt Q R = 0 := by
    have gQ : Q.getLast? = some (Q.getLast hQ) := List.getLast?_eq_some_getLast hQ
    have hRh : R.head? = some (R.head hR) := List.head?_eq_some_head hR
    simp [midAlt, gQ, hRh, hdbl]
  -- current count is bounded by pieces + 1
  have hleN : altCyc (Q ++ R) ≤ linAlt Q + linAlt R + 1 := by
    rw [altCyc_unfold, linAlt_append, hmid0]
    have hw := wrapAlt_le_one (Q ++ R)
    omega
  rw [hKcur] at hleN
  omega

lemma wProd_single (X : Matrix n n ℂ) (b : Bool) :
    wProd X [b] = wFactor X b := by
  simp [wProd_cons, wProd_nil]

lemma wProd_pair (X : Matrix n n ℂ) (a b : Bool) :
    wProd X [a, b] = wFactor X a * wFactor X b := by
  simp [wProd_cons, wProd_nil]

/-- Power form of an alternating word product. -/
lemma wProd_alt (X : Matrix n n ℂ) (b0 : Bool) (r : ℕ) (l : List Bool)
    (hlen : l.length = 2 * r)
    (hb0 : ∀ h : 0 < l.length, l[0]'h = b0)
    (halt : ∀ i (h1 : i < l.length) (h2 : i + 1 < l.length),
      l[i + 1]'h2 = !(l[i]'h1)) :
    wProd X l = (wFactor X b0 * wFactor X (!b0)) ^ r := by
  revert l hb0 halt hlen
  induction r with
  | zero =>
    intro l hlen hb0 halt
    have : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst this
    simp [wProd_nil]
  | succ r ih =>
    intro l hlen hb0 halt
    have hlen2 : 2 ≤ l.length := by omega
    have h0 : 0 < l.length := by omega
    have h1 : 1 < l.length := by omega
    have hb0v : l[0]'h0 = b0 := hb0 h0
    have h1v : l[1]'h1 = !(l[0]'h0) := halt 0 h0 (by omega)
    have hlen_take : (l.take 2).length = ([b0, !b0] : List Bool).length := by
      simp only [List.length_take, List.length_cons, List.length_nil, hlen]; omega
    have hentries : ∀ i (h1 : i < (l.take 2).length) (h2 : i < ([b0, !b0] : List Bool).length),
        (l.take 2)[i]'h1 = ([b0, !b0][i]'h2) := by
      intro i h1 h2
      have hi2 : i < 2 := by simpa using h2
      have h01 : i = 0 ∨ i = 1 := by omega
      rcases h01 with rfl | rfl
      · have eL : (l.take 2)[0]'h1 = l[0]'h0 := List.getElem_take
        have eR : ([b0, !b0][0]'h2 = b0) := by simp
        rw [eL, eR]; exact hb0v
      · have eL : (l.take 2)[1]'h1 = l[1]'(by omega) := List.getElem_take
        have eR : ([b0, !b0][1]'h2 = !b0) := by simp
        rw [eL, eR, h1v, hb0v]
    have htake : l.take 2 = [b0, !b0] := List.ext_getElem hlen_take hentries
    have hsplit : l = [b0, !b0] ++ l.drop 2 := by
      rw [← htake, List.take_append_drop]
    have hdrop_len : (l.drop 2).length = 2 * r := by
      simp [List.length_drop, hlen]; omega
    have hdrop_hb0 : ∀ h : 0 < (l.drop 2).length, (l.drop 2)[0]'h = b0 := by
      intro h
      have e1 : (l.drop 2)[0]'h = l[0 + 2]'(by omega) := by
        simp only [List.getElem_drop, Nat.add_comm, Nat.add_assoc]
      have e2 : l[0 + 2]'(by omega : 0 + 2 < l.length)
          = !(l[0 + 1]'(by omega)) := halt (0 + 1) (by omega) (by omega)
      have e3 : l[0 + 1]'(by omega : 0 + 1 < l.length)
          = !(l[0]'h0) := halt 0 h0 (by omega)
      rw [e1]
      have e2' : l[0 + 2]'(by omega : 0 + 2 < l.length) = !(l[0 + 1]'(by omega)) := e2
      rw [e2', e3, hb0v, Bool.not_not]
    have hdrop_halt : ∀ i (h1 : i < (l.drop 2).length) (h2 : i + 1 < (l.drop 2).length),
        (l.drop 2)[i + 1]'h2 = !((l.drop 2)[i]'h1) := by
      intro i h1 h2
      have e1 : (l.drop 2)[i + 1]'h2 = l[i + 1 + 2]'(by omega) := by
        simp only [List.getElem_drop, Nat.add_comm, Nat.add_assoc]
      have e2 : (l.drop 2)[i]'h1 = l[i + 2]'(by omega) := by
        simp only [List.getElem_drop, Nat.add_comm, Nat.add_assoc]
      rw [e1, e2]
      have key : i + 1 + 2 = (i + 2) + 1 := by omega
      simp only [key]
      exact halt (i + 2) (by omega) (by omega)
    have ihr := ih (l.drop 2) hdrop_len hdrop_hb0 hdrop_halt
    rw [hsplit, wProd_append, wProd_pair, ihr, pow_succ']

/-- Trace of powers is cyclically symmetric. -/
lemma trace_pow_mul_comm (A B : Matrix n n ℂ) (k : ℕ) :
    Matrix.trace ((A * B) ^ k) = Matrix.trace ((B * A) ^ k) := by
  cases k with
  | zero => rfl
  | succ k =>
    have hpow : (A * B) ^ (k + 1) = A * ((B * A) ^ k * B) := by
      induction k with
      | zero => simp [pow_zero, pow_one, mul_assoc]
      | succ k ih =>
        calc (A * B) ^ (k + 1 + 1) = ((A * B) ^ (k + 1)) * (A * B) := by rw [pow_succ]
          _ = (A * ((B * A) ^ k * B)) * (A * B) := by rw [ih]
          _ = A * ((B * A) ^ (k + 1) * B) := by rw [pow_succ]; noncomm_ring
    rw [hpow, Matrix.trace_mul_comm, mul_assoc, ← pow_succ]

/-- `Tr((X*Xᴴ)^r)` is real and nonnegative (even/odd square trick). -/
lemma trace_XXdag_pow_re_nonneg_im (X : Matrix n n ℂ) (r : ℕ) :
    0 ≤ (Matrix.trace ((X * Xᴴ) ^ r)).re
    ∧ (Matrix.trace ((X * Xᴴ) ^ r)).im = 0 := by
  have hH : (X * Xᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self X
  rcases Nat.even_or_odd r with hev | hodd
  · obtain ⟨q, rfl⟩ := hev
    -- (XX†)^(q+q) = (Y† * Y) with Y = (XX†)^q
    have hY : (((X * Xᴴ) ^ q))ᴴ = ((X * Xᴴ) ^ q) := hH.pow q
    have eMM : (X * Xᴴ) ^ (q + q) = (((X * Xᴴ) ^ q))ᴴ * (((X * Xᴴ) ^ q)) := by
      rw [hY, ← pow_add]
    have htreq : Matrix.trace ((X * Xᴴ) ^ (q + q))
        = Matrix.trace (((((X * Xᴴ) ^ q))ᴴ * (((X * Xᴴ) ^ q)))) := by
      rw [eMM]
    rw [htreq]
    exact ⟨trace_conjTranspose_mul_self_re_nonneg _,
      trace_conjTranspose_mul_self_im _⟩
  · obtain ⟨q, rfl⟩ := hodd
    -- (XX†)^(2q+1) = Z * Zᴴ with Z = (XX†)^q * X; then Tr = Tr(Zᴴ*Z)
    have hHq : (((X * Xᴴ) ^ q))ᴴ = ((X * Xᴴ) ^ q) := hH.pow q
    have eZZ : (X * Xᴴ) ^ (2 * q + 1)
        = (((X * Xᴴ) ^ q * X)) * ((((X * Xᴴ) ^ q * X)))ᴴ := by
      rw [Matrix.conjTranspose_mul, hHq]
      have eexp : (2 * q + 1 : ℕ) = q + (q + 1) := by omega
      rw [eexp, pow_add, pow_succ']
      simp only [mul_assoc]
    have htreq : Matrix.trace ((X * Xᴴ) ^ (2 * q + 1))
        = Matrix.trace ((((((X * Xᴴ) ^ q * X)))ᴴ * ((((X * Xᴴ) ^ q * X))))) := by
      rw [eZZ, Matrix.trace_mul_comm]
    rw [htreq]
    exact ⟨trace_conjTranspose_mul_self_re_nonneg _,
      trace_conjTranspose_mul_self_im _⟩

/-- Trace norm as a function on words. -/
noncomputable def wordT (X : Matrix n n ℂ) {N : ℕ} (w : wordDom N) : ℝ :=
  ‖Matrix.trace (wProd X w.val)‖

/-- Cyclic count as a function on words. -/
def wordK {N : ℕ} (w : wordDom N) : ℕ := altCyc w.val


/-- Dyson's Lemma 2: every length-`2r` word product satisfies
`‖Tr P‖ ≤ Tr((X*Xᴴ)^r).re`. -/
theorem dyson_word_bound (X : Matrix n n ℂ) (r : ℕ)
    (w : wordDom (2 * r)) :
    ‖Matrix.trace (wProd X w.val)‖ ≤ (Matrix.trace ((X * Xᴴ) ^ r)).re := by
  by_cases hr0 : r = 0
  · subst hr0
    have hlen0 := w.prop
    have h0 : w.val.length = 0 := by omega
    have hempty : w.val = [] := List.length_eq_zero_iff.mp h0
    have htr1 : Matrix.trace (1 : Matrix n n ℂ) = ((Fintype.card n : ℕ) : ℂ) :=
      Matrix.trace_one
    have hnorm : ‖Matrix.trace (1 : Matrix n n ℂ)‖ = (Fintype.card n : ℝ) := by
      rw [htr1]; exact RCLike.norm_natCast _
    have hre : (Matrix.trace (1 : Matrix n n ℂ)).re = (Fintype.card n : ℝ) := by
      rw [htr1]; exact Complex.natCast_re _
    rw [hempty, wProd_nil, pow_zero, hnorm, hre]
  · have hr : 1 ≤ r := by omega
    have hne : (Finset.univ : Finset (wordDom (2 * r))).Nonempty :=
      ⟨⟨List.replicate (2 * r) false, List.length_replicate⟩, Finset.mem_univ _⟩
    have himgT : (Finset.univ.image (wordT X)).Nonempty :=
      Finset.image_nonempty.mpr hne
    set M := (Finset.univ.image (wordT X)).max' himgT with hMdef
    have hMub : ∀ v : wordDom (2 * r), wordT X v ≤ M :=
      fun v => Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ v))
    obtain ⟨w₀, _, hw₀⟩ := Finset.mem_image.mp (Finset.max'_mem _ himgT)
    have hSne : (Finset.univ.filter (fun v : wordDom (2 * r) => wordT X v = M)).Nonempty :=
      ⟨w₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw₀⟩⟩
    have himgK : ((Finset.univ.filter
      (fun v : wordDom (2 * r) => wordT X v = M)).image wordK).Nonempty :=
      Finset.image_nonempty.mpr hSne
    set kmax := ((Finset.univ.filter
      (fun v : wordDom (2 * r) => wordT X v = M)).image wordK).max' himgK with hkdef
    have hKub : ∀ v : wordDom (2 * r), wordT X v = M → wordK v ≤ kmax := by
      intro v hv
      have hvmem : v ∈ Finset.univ.filter (fun v : wordDom (2 * r) => wordT X v = M) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
      exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ hvmem)
    obtain ⟨w₁, hw₁mem, hw₁eq⟩ := Finset.mem_image.mp (Finset.max'_mem _ himgK)
    have hTw₁ : wordT X w₁ = M :=
      (Finset.mem_filter.mp hw₁mem).2
    have hKw₁ : wordK w₁ = kmax := hw₁eq
    suffices hMbound : M ≤ (Matrix.trace ((X * Xᴴ) ^ r)).re by
      calc ‖Matrix.trace (wProd X w.val)‖ = wordT X w := rfl
        _ ≤ M := hMub w
        _ ≤ (Matrix.trace ((X * Xᴴ) ^ r)).re := hMbound
    have hlen₁ : w₁.val.length = 2 * r := w₁.prop
    rcases find_double w₁.val with ⟨t, h1, h2, heq⟩ | hall
    · -- Linear double: rotate to middle, then transfer
      have htN : t + 1 < 2 * r := by omega
      by_cases hcase : r ≤ t + 1
      · by_cases hs0 : t + 1 = r
        · -- Double already at middle; split directly
          have hQlen : (w₁.val.take r).length = r := by
            rw [List.length_take, hlen₁]; omega
          have hRlen : (w₁.val.drop r).length = r := by
            rw [List.length_drop, hlen₁]; omega
          have hQ : w₁.val.take r ≠ [] := by
            intro hcon
            have h0 : (w₁.val.take r).length = 0 := by rw [hcon]; rfl
            omega
          have hR : w₁.val.drop r ≠ [] := by
            intro hcon
            have h0 : (w₁.val.drop r).length = 0 := by rw [hcon]; rfl
            omega
          have hdbl : (w₁.val.take r).getLast hQ = (w₁.val.drop r).head hR := by
            have eL : (w₁.val.take r).getLast hQ = w₁.val[r - 1]'(by omega) := by
              simp only [List.getLast_eq_getElem, hQlen, List.getElem_take]
            have eR : (w₁.val.drop r).head hR = w₁.val[r]'(by omega) := by
              exact List.head_drop hR
            rw [eL, eR]
            have k1 : r - 1 = t := by omega
            have k2 : r = t + 1 := hs0.symm
            simp only [k1, k2]
            exact heq
          have hQR : wProd X (w₁.val.take r) * wProd X (w₁.val.drop r)
              = wProd X w₁.val := by
            rw [← wProd_append, List.take_append_drop]
          have hP : ‖Matrix.trace
              (wProd X (w₁.val.take r) * wProd X (w₁.val.drop r))‖ = M := by
            rw [hQR]
            exact hTw₁
          have hKcur : altCyc (w₁.val.take r ++ w₁.val.drop r) = kmax := by
            rw [List.take_append_drop]
            exact hKw₁
          exact False.elim (transfer_contra X r hr _ _ hQlen hRlen hQ hR hdbl M kmax
            (fun v => hMub v) (fun v hv => hKub v hv) hP hKcur)
        · -- s = t+1-r > 0; rotate the double to the middle
          set s := t + 1 - r with hsdef
          have hspos : 0 < s := by omega
          have hslt : s < 2 * r := by omega
          have hsle : s ≤ w₁.val.length := by omega
          set l₂ := w₁.val.rotate s with hl₂def
          have hlen₂ : l₂.length = 2 * r := by
            simp [hl₂def, List.length_rotate, hlen₁]
          have htake_ne : w₁.val.take s ≠ [] := by
            intro hcon
            have h0 : (w₁.val.take s).length = 0 := by rw [hcon]; rfl
            have hpos : 0 < (w₁.val.take s).length := by
              simp [List.length_take, hlen₁]; omega
            omega
          have hdrop_ne : w₁.val.drop s ≠ [] := by
            intro hcon
            have h0 : (w₁.val.drop s).length = 0 := by rw [hcon]; rfl
            have hpos : 0 < (w₁.val.drop s).length := by
              simp [List.length_drop, hlen₁]; omega
            omega
          have hTl₂ : wordT X ⟨l₂, hlen₂⟩ = M := by
            have etrace : Matrix.trace (wProd X l₂) = Matrix.trace (wProd X w₁.val) :=
              trace_wProd_rotate X w₁.val s (by omega)
            show ‖Matrix.trace (wProd X l₂)‖ = M
            rw [etrace]
            exact hTw₁
          have hKl₂ : wordK ⟨l₂, hlen₂⟩ = kmax := by
            have ealt : altCyc l₂ = altCyc w₁.val :=
              altCyc_rotate w₁.val s (by omega) htake_ne hdrop_ne
            show altCyc l₂ = kmax
            rw [ealt]
            exact hKw₁
          -- middle double in l₂ maps to (t, t+1)
          have hrotlen : (w₁.val.rotate s).length = 2 * r := by
            rw [List.length_rotate, hlen₁]
          have hmid1 : l₂[r - 1]'(by omega) = w₁.val[t]'(by omega) := by
            have e := List.getElem_rotate w₁.val s (r - 1) (by omega)
            have key : ((r - 1 + s) % w₁.val.length) = t := by
              have e1 : r - 1 + s = t := by omega
              have e2 : t < w₁.val.length := by omega
              rw [e1]
              exact Nat.mod_eq_of_lt e2
            simp only [key] at e
            exact e
          have hmid2 : l₂[r]'(by omega) = w₁.val[t + 1]'(by omega) := by
            have e := List.getElem_rotate w₁.val s r (by omega)
            have key : ((r + s) % w₁.val.length) = t + 1 := by
              have e1 : r + s = t + 1 := by omega
              have e2 : t + 1 < w₁.val.length := by omega
              rw [e1]
              exact Nat.mod_eq_of_lt e2
            simp only [key] at e
            exact e
          -- split l₂ at the middle and transfer
          have hQlen : (l₂.take r).length = r := by
            rw [List.length_take, hlen₂]; omega
          have hRlen : (l₂.drop r).length = r := by
            rw [List.length_drop, hlen₂]; omega
          have hQ : l₂.take r ≠ [] := by
            intro hcon
            have h0 : (l₂.take r).length = 0 := by rw [hcon]; rfl
            omega
          have hR : l₂.drop r ≠ [] := by
            intro hcon
            have h0 : (l₂.drop r).length = 0 := by rw [hcon]; rfl
            omega
          have hdbl : (l₂.take r).getLast hQ = (l₂.drop r).head hR := by
            have eL : (l₂.take r).getLast hQ = l₂[r - 1]'(by omega) := by
              simp only [List.getLast_eq_getElem, hQlen, List.getElem_take]
            have eR : (l₂.drop r).head hR = l₂[r]'(by omega) := by
              exact List.head_drop hR
            rw [eL, eR, hmid1, hmid2]
            exact heq
          have hQR : wProd X (l₂.take r) * wProd X (l₂.drop r) = wProd X l₂ := by
            rw [← wProd_append, List.take_append_drop]
          have hP : ‖Matrix.trace
              (wProd X (l₂.take r) * wProd X (l₂.drop r))‖ = M := by
            rw [hQR]
            exact hTl₂
          have hKcur : altCyc (l₂.take r ++ l₂.drop r) = kmax := by
            rw [List.take_append_drop]
            exact hKl₂
          exact False.elim (transfer_contra X r hr _ _ hQlen hRlen hQ hR hdbl M kmax
            (fun v => hMub v) (fun v hv => hKub v hv) hP hKcur)
      · -- Case B: double in first half (t+1 < r); rotate by s = t+1+r
        have hlt : t + 1 < r := by omega
        set s := t + 1 + r with hsdef
        have hspos : 0 < s := by omega
        have hslt : s < 2 * r := by omega
        have hsle : s ≤ w₁.val.length := by omega
        set l₂ := w₁.val.rotate s with hl₂def
        have hlen₂ : l₂.length = 2 * r := by
          simp [hl₂def, List.length_rotate, hlen₁]
        have htake_ne : w₁.val.take s ≠ [] := by
          intro hcon
          have h0 : (w₁.val.take s).length = 0 := by rw [hcon]; rfl
          have hpos : 0 < (w₁.val.take s).length := by
            simp [List.length_take, hlen₁]; omega
          omega
        have hdrop_ne : w₁.val.drop s ≠ [] := by
          intro hcon
          have h0 : (w₁.val.drop s).length = 0 := by rw [hcon]; rfl
          have hpos : 0 < (w₁.val.drop s).length := by
            simp [List.length_drop, hlen₁]; omega
          omega
        have hTl₂ : wordT X ⟨l₂, hlen₂⟩ = M := by
          have etrace : Matrix.trace (wProd X l₂) = Matrix.trace (wProd X w₁.val) :=
            trace_wProd_rotate X w₁.val s (by omega)
          show ‖Matrix.trace (wProd X l₂)‖ = M
          rw [etrace]
          exact hTw₁
        have hKl₂ : wordK ⟨l₂, hlen₂⟩ = kmax := by
          have ealt : altCyc l₂ = altCyc w₁.val :=
            altCyc_rotate w₁.val s (by omega) htake_ne hdrop_ne
          show altCyc l₂ = kmax
          rw [ealt]
          exact hKw₁
        have hrotlen : (w₁.val.rotate s).length = 2 * r := by
          rw [List.length_rotate, hlen₁]
        have hmid1 : l₂[r - 1]'(by omega) = w₁.val[t]'(by omega) := by
          have e := List.getElem_rotate w₁.val s (r - 1) (by omega)
          have key : ((r - 1 + s) % w₁.val.length) = t := by
            have e1 : r - 1 + s = t + 2 * r := by omega
            have e2 : t < w₁.val.length := by omega
            rw [hlen₁, e1, Nat.add_mod_right]
            exact Nat.mod_eq_of_lt (by omega)
          simp only [key] at e
          exact e
        have hmid2 : l₂[r]'(by omega) = w₁.val[t + 1]'(by omega) := by
          have e := List.getElem_rotate w₁.val s r (by omega)
          have key : ((r + s) % w₁.val.length) = t + 1 := by
            have e1 : r + s = (t + 1) + 2 * r := by omega
            have e2 : t + 1 < w₁.val.length := by omega
            rw [hlen₁, e1, Nat.add_mod_right]
            exact Nat.mod_eq_of_lt (by omega)
          simp only [key] at e
          exact e
        have hQlen : (l₂.take r).length = r := by
          rw [List.length_take, hlen₂]; omega
        have hRlen : (l₂.drop r).length = r := by
          rw [List.length_drop, hlen₂]; omega
        have hQ : l₂.take r ≠ [] := by
          intro hcon
          have h0 : (l₂.take r).length = 0 := by rw [hcon]; rfl
          omega
        have hR : l₂.drop r ≠ [] := by
          intro hcon
          have h0 : (l₂.drop r).length = 0 := by rw [hcon]; rfl
          omega
        have hdbl : (l₂.take r).getLast hQ = (l₂.drop r).head hR := by
          have eL : (l₂.take r).getLast hQ = l₂[r - 1]'(by omega) := by
            simp only [List.getLast_eq_getElem, hQlen, List.getElem_take]
          have eR : (l₂.drop r).head hR = l₂[r]'(by omega) := by
            exact List.head_drop hR
          rw [eL, eR, hmid1, hmid2]
          exact heq
        have hQR : wProd X (l₂.take r) * wProd X (l₂.drop r) = wProd X l₂ := by
          rw [← wProd_append, List.take_append_drop]
        have hP : ‖Matrix.trace
            (wProd X (l₂.take r) * wProd X (l₂.drop r))‖ = M := by
          rw [hQR]
          exact hTl₂
        have hKcur : altCyc (l₂.take r ++ l₂.drop r) = kmax := by
          rw [List.take_append_drop]
          exact hKl₂
        exact False.elim (transfer_contra X r hr _ _ hQlen hRlen hQ hR hdbl M kmax
          (fun v => hMub v) (fun v hv => hKub v hv) hP hKcur)
    · -- All linear pairs alternate: power form, then bound
      have halt : ∀ i (h1 : i < w₁.val.length) (h2 : i + 1 < w₁.val.length),
          w₁.val[i + 1]'h2 = !(w₁.val[i]'h1) := by
        intro i h1 h2
        have hne := hall i h1 h2
        cases ha : w₁.val[i]'h1 <;> cases hb : w₁.val[i + 1]'h2 <;> simp_all
      have h0lt : 0 < w₁.val.length := by omega
      obtain ⟨b0, hb0eq⟩ : ∃ b : Bool, w₁.val[0]'h0lt = b := ⟨_, rfl⟩
      have hb0 : ∀ h : 0 < w₁.val.length, w₁.val[0]'h = b0 := fun h => hb0eq
      have hW := trace_XXdag_pow_re_nonneg_im X r
      have hnorm_le : ‖Matrix.trace ((X * Xᴴ) ^ r)‖
          ≤ (Matrix.trace ((X * Xᴴ) ^ r)).re := by
        have heq : Matrix.trace ((X * Xᴴ) ^ r)
            = (((Matrix.trace ((X * Xᴴ) ^ r)).re : ℝ) : ℂ) := by
          apply Complex.ext <;> simp [hW.2]
        have heq2 : ‖Matrix.trace ((X * Xᴴ) ^ r)‖
            = (Matrix.trace ((X * Xᴴ) ^ r)).re := by
          rw [heq, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
          exact abs_of_nonneg hW.1
        exact le_of_eq heq2
      cases b0 with
      | false =>
        have hprod := wProd_alt X false r w₁.val hlen₁ hb0 halt
        have hM : M = ‖Matrix.trace ((X * Xᴴ) ^ r)‖ := by
          calc M = ‖Matrix.trace (wProd X w₁.val)‖ := hTw₁.symm
            _ = ‖Matrix.trace ((wFactor X false * wFactor X (!false)) ^ r)‖ := by
              rw [hprod]
            _ = ‖Matrix.trace ((X * Xᴴ) ^ r)‖ := rfl
        rw [hM]
        exact hnorm_le
      | true =>
        have hprod := wProd_alt X true r w₁.val hlen₁ hb0 halt
        have hcyc : Matrix.trace ((Xᴴ * X) ^ r)
            = Matrix.trace ((X * Xᴴ) ^ r) :=
          trace_pow_mul_comm _ _ _
        have hM : M = ‖Matrix.trace ((X * Xᴴ) ^ r)‖ := by
          calc M = ‖Matrix.trace (wProd X w₁.val)‖ := hTw₁.symm
            _ = ‖Matrix.trace ((wFactor X true * wFactor X (!true)) ^ r)‖ := by
              rw [hprod]
            _ = ‖Matrix.trace ((Xᴴ * X) ^ r)‖ := rfl
            _ = ‖Matrix.trace ((X * Xᴴ) ^ r)‖ := by rw [hcyc]
        rw [hM]
        exact hnorm_le
