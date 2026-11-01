module

/-
KsIndexLean — ArcUpperEdge: the generic head bound `ind + nul ≤ 2` and the
edge classes `j ∈ {1, k−1}` at the circle level.

The index and nullity estimates assume `0 < a < 1` and `|b| < 1`.
For the edge classes one head symbol vanishes: at `a = 1 − 1/k = b` we have
`σ_{(a;k)}(0) = 0`, at `a = 1/k` (`1 − a = b`) we have `σ_{(a;k)}(−1) = 0`.  Then
the form is `≥ 0` on the arc-supported vectors vanishing at the other head,
with equality only when all off-head coordinates vanish — and an arc-supported
sequence supported on a single head is zero (`ς₁u = u` read at `m = 1`, resp.
`m = 0`: `ς̂₁(1) = 2/π ≠ 0`).  So the one-head engine gives `ind + nul ≤ 1`.

The paper obtains the edge-class upper bound through the geometric argument
`z-upper`. Here the circle-level result follows directly from the convolution
identity defining arc support and the one-coordinate form-index bound.
`ArcMain` specializes the vanishing-symbol hypotheses to the class parameters.
-/
public import KsIndexLean.ArcForm
public import KsIndexLean.FormIndexExt

@[expose] public section


noncomputable section

namespace KsIndex.ArcUpper

open KsIndex.ArcSpace KsIndex.ArcForm KsIndex.FormIndex KsIndex.CircleQ Real

/-! ### Single-head supports are trivial in `ArcDom` -/

lemma sgnHat_one : sgnHat 1 = 2 / π := by
  rw [show (1 : ℤ) = 2 * 0 + 1 by norm_num, sgnHat_odd]
  simp [chat]

lemma sgnHat_one_ne_zero : sgnHat 1 ≠ 0 := by
  rw [sgnHat_one]; positivity

/-- An arc-supported sequence supported in `{0}` vanishes. -/
lemma eq_zero_of_support_zero {u : ℤ → ℂ} (hu : u ∈ ArcDom)
    (h : ∀ ℓ : ℤ, ℓ ≠ 0 → u ℓ = 0) : u = 0 := by
  have h1 := hu.2 1
  rw [convS₁, tsum_eq_single 0 (fun n hn => by rw [h n hn, mul_zero])] at h1
  rw [h 1 (by norm_num), sub_zero, sgnHat_one] at h1
  have h0 : u 0 = 0 := by
    have hne : ((2 / π : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (2 / π : ℝ) ≠ 0 by positivity)
    exact (mul_eq_zero.mp h1).resolve_left hne
  funext ℓ
  by_cases hℓ : ℓ = 0
  · rw [hℓ, h0]; rfl
  · rw [h ℓ hℓ]; rfl

/-- An arc-supported sequence supported in `{−1}` vanishes. -/
lemma eq_zero_of_support_neg_one {u : ℤ → ℂ} (hu : u ∈ ArcDom)
    (h : ∀ ℓ : ℤ, ℓ ≠ -1 → u ℓ = 0) : u = 0 := by
  have h1 := hu.2 0
  rw [convS₁, tsum_eq_single (-1) (fun n hn => by rw [h n hn, mul_zero])] at h1
  rw [h 0 (by norm_num), show (0 : ℤ) - -1 = 1 by norm_num, sgnHat_one] at h1
  have h0 : u (-1) = 0 := by
    have hne : ((2 / π : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (2 / π : ℝ) ≠ 0 by positivity)
    exact (mul_eq_zero.mp h1).resolve_left hne
  funext ℓ
  by_cases hℓ : ℓ = -1
  · rw [hℓ, h0]; rfl
  · rw [h ℓ hℓ]; rfl

/-! ### The generic two-head bound -/

/-- `ind_DN + nul_DN ≤ 2` for every `a ∈ (0,1)`, `|b| < 1` (paper: the heads
`{0, −1}` are the only possibly nonpositive frequencies). -/
theorem indArc_add_nulArc_le_two (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| < 1) :
    indArc a b + nulArc a b ≤ 2 := by
  have h := formIndex_add_formNullity_le_card (Q := NQformArc a b) (B := NBformArc a b)
    (D := ArcDom) (F := {0, -1}) (NQformArc_zero a b) (NBformArc_self a b)
    (fun {x y v} hx hy hv => NBformArc_add_left ha b hx hy hv)
    (fun {x v w} hx hv hw => NBformArc_add_right ha b hx hv hw)
    (NBformArc_conj_symm a b)
    (fun u hu h0 hne => NQformArc_pos_of_heads_zero ha hb hu.1
      (h0 0 (by simp)) (h0 (-1) (by simp)) hne)
  rw [indArc, nulArc]
  simpa using h

/-! ### The edge classes -/

/-- For `0 < a < 1` and `|b| < 1`, if `σ(0) = 0` then `ind_DN + nul_DN ≤ 1`. -/
theorem indArc_add_nulArc_le_one_of_sigma_zero (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| < 1)
    (h0 : sigmaArc a b 0 = 0) : indArc a b + nulArc a b ≤ 1 := by
  have h := formIndex_add_formNullity_le_card (Q := NQformArc a b) (B := NBformArc a b)
    (D := ArcDom) (F := {-1}) (NQformArc_zero a b) (NBformArc_self a b)
    (fun {x y v} hx hy hv => NBformArc_add_left ha b hx hy hv)
    (fun {x v w} hx hv hw => NBformArc_add_right ha b hx hv hw)
    (NBformArc_conj_symm a b) ?_
  · rw [indArc, nulArc]; simpa using h
  intro u hu hF hne
  have hu1 : u (-1) = 0 := hF (-1) (by simp)
  rw [NQformArc_split ha b hu.1, h0, hu1]
  simp only [zero_mul, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, add_zero, zero_add]
  -- some off-head coordinate is nonzero, else `u` is supported in `{0}` and vanishes
  by_contra hle
  push Not at hle
  have hall : ∀ ℓ : ℤ, ℓ ≠ 0 → u ℓ = 0 := by
    intro ℓ hℓ
    by_cases hℓ1 : ℓ = -1
    · rw [hℓ1, hu1]
    · by_contra hne'
      have := tsum_tailTerm_pos ha hb hu.1 hℓ hℓ1 hne'
      linarith
  obtain ⟨i, hi⟩ := hne
  exact hi (by rw [eq_zero_of_support_zero hu hall]; rfl)

/-- For `0 < a < 1` and `|b| < 1`, if `σ(−1) = 0` then `ind_DN + nul_DN ≤ 1`. -/
theorem indArc_add_nulArc_le_one_of_sigma_neg_one (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| < 1)
    (h1 : sigmaArc a b (-1) = 0) : indArc a b + nulArc a b ≤ 1 := by
  have h := formIndex_add_formNullity_le_card (Q := NQformArc a b) (B := NBformArc a b)
    (D := ArcDom) (F := {0}) (NQformArc_zero a b) (NBformArc_self a b)
    (fun {x y v} hx hy hv => NBformArc_add_left ha b hx hy hv)
    (fun {x v w} hx hv hw => NBformArc_add_right ha b hx hv hw)
    (NBformArc_conj_symm a b) ?_
  · rw [indArc, nulArc]; simpa using h
  intro u hu hF hne
  have hu0 : u 0 = 0 := hF 0 (by simp)
  rw [NQformArc_split ha b hu.1, h1, hu0]
  simp only [zero_mul, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, add_zero, zero_add]
  by_contra hle
  push Not at hle
  have hall : ∀ ℓ : ℤ, ℓ ≠ -1 → u ℓ = 0 := by
    intro ℓ hℓ
    by_cases hℓ0 : ℓ = 0
    · rw [hℓ0, hu0]
    · by_contra hne'
      have := tsum_tailTerm_pos ha hb hu.1 hℓ0 hℓ hne'
      linarith
  obtain ⟨i, hi⟩ := hne
  exact hi (by rw [eq_zero_of_support_neg_one hu hall]; rfl)

end KsIndex.ArcUpper
