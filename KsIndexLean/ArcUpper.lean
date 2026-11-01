module

/-
KsIndexLean — ArcUpper: the m=2 upper bound for the interior classes
(`k ≥ 4`, `2 ≤ j ≤ k−2`) at the circle level — the paper's `Zclasses` proof.

The results assume `0 < a < 1`, `|b| < 1`, `a < b`, and `1 − a < b`.
They apply to the interior class parameters `a = 1 − j/k`, `b = 1 − 1/k`;
`ArcMain` supplies this specialization and combines it with the endpoint cases.

For any `u ∈ ArcDom` whose two distinguished coefficients satisfy
`u(0) = 1/σ(0)` and `u(−1) = −1/σ(−1)`, both symbols are negative. Set
`X = 1/|σ(0)| + 1/|σ(−1)|`. Splitting the form gives `N(u) = −X + tail(u)`.
The Cauchy–Schwarz estimate `ArcPsi.head_diff_sq_le` yields
`X² = |u(0)−u(−1)|² ≤ Sconst · tail(u)`, while
`ArcEstimateFaithful.Sconst_lt_paper` gives `Sconst < X`. Thus `tail(u) > X`
and `N(u) > 0`.

This is a conditional positivity statement on the prescribed-coefficient slice;
it does not construct a vector on that slice. Together with strict positivity
for nonzero vectors whose two distinguished coefficients vanish, it supplies
`FormIndexExt.formIndex_add_formNullity_add_one_le_card`. The resulting circle
bound is `indArc a b + nulArc a b ≤ 1`.
-/
public import KsIndexLean.ArcUpperEdge
public import KsIndexLean.ArcEstimateFaithful

@[expose] public section


noncomputable section

namespace KsIndex.ArcUpper

open KsIndex.ArcSpace KsIndex.ArcForm KsIndex.ArcPsi KsIndex.ArcEstimate KsIndex.FormIndex Real

lemma sigma_zero_neg (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hab : a < b) : sigmaArc a b 0 < 0 := by
  rw [sigma_zero_eq ha]
  have ha0 := ha.1
  apply div_neg_of_neg_of_pos _ ha0
  nlinarith

lemma sigma_neg_one_neg (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hab' : 1 - a < b) :
    sigmaArc a b (-1) < 0 := by
  rw [sigma_neg_one_eq ha]
  have ha1 : 0 < 1 - a := by linarith [ha.2]
  apply div_neg_of_neg_of_pos _ ha1
  nlinarith

/-- **Slice positivity** (paper's `Zclasses`): an arc-supported vector with heads
`(1/σ(0), −1/σ(−1))` has `N > 0`. -/
theorem NQformArc_pos_on_slice (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| < 1) (hab : a < b)
    (hab' : 1 - a < b) {u : ℤ → ℂ} (hu : u ∈ ArcDom)
    (h0 : u 0 = ((1 / sigmaArc a b 0 : ℝ) : ℂ))
    (h1 : u (-1) = ((-1 / sigmaArc a b (-1) : ℝ) : ℂ)) :
    0 < NQformArc a b u := by
  have hσ0 := sigma_zero_neg ha hab
  have hσ1 := sigma_neg_one_neg ha hab'
  set X : ℝ := -1 / sigmaArc a b 0 + -1 / sigmaArc a b (-1) with hX
  have hXpos : 0 < X := by
    rw [hX]
    have : 0 < -1 / sigmaArc a b 0 := div_pos_of_neg_of_neg (by norm_num) hσ0
    have : 0 < -1 / sigmaArc a b (-1) := div_pos_of_neg_of_neg (by norm_num) hσ1
    linarith
  have hS := KsIndex.ArcEstimateFaithful.Sconst_lt_paper ha hb.le hab hab'
  have hS0 := Sconst_nonneg ha hb.le
  have hCS := head_diff_sq_le ha hb hu
  have hT0 := tsum_tailTerm_nonneg ha hb u
  -- `u 0 − u (−1) = −X`
  have hdiff : ‖u 0 - u (-1)‖ ^ 2 = X ^ 2 := by
    rw [h0, h1, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs, hX]
    ring
  rw [hdiff] at hCS
  -- the head terms: `σ(0)|u0|² = 1/σ(0)`, `σ(−1)|u₋₁|² = 1/σ(−1)`
  rw [NQformArc_split ha b hu.1, h0, h1, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  have e0 : sigmaArc a b 0 * (1 / sigmaArc a b 0) ^ 2 = -(-1 / sigmaArc a b 0) := by
    field_simp
  have e1 : sigmaArc a b (-1) * (-1 / sigmaArc a b (-1)) ^ 2 = -(-1 / sigmaArc a b (-1)) := by
    field_simp
  rw [e0, e1]
  -- `tail > X`: otherwise `X² ≤ Sconst·tail ≤ Sconst·X < X²`
  have htail : X < ∑' ℓ : ℤ, tailTerm a b u ℓ := by
    by_contra hle
    push Not at hle
    have h1' : Sconst a b * ∑' ℓ : ℤ, tailTerm a b u ℓ ≤ Sconst a b * X :=
      mul_le_mul_of_nonneg_left hle hS0
    have h2' : Sconst a b * X < X * X := mul_lt_mul_of_pos_right (by linarith) hXpos
    nlinarith
  rw [hX] at htail
  linarith

/-- **`ind + nul ≤ 1` for the interior classes** (`0 < a < 1`, `a < b`, `1 − a < b`, `|b| < 1`). -/
theorem indArc_add_nulArc_le_one_interior (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| < 1)
    (hab : a < b) (hab' : 1 - a < b) : indArc a b + nulArc a b ≤ 1 := by
  classical
  set F : Finset ℤ := {0, -1} with hF
  let hvec : ↥F → ℂ := fun i =>
    if (i : ℤ) = 0 then ((1 / sigmaArc a b 0 : ℝ) : ℂ) else ((-1 / sigmaArc a b (-1) : ℝ) : ℂ)
  have h := formIndex_add_formNullity_add_one_le_card (Q := NQformArc a b) (B := NBformArc a b)
    (D := ArcDom) (F := F) (NQformArc_zero a b) (NBformArc_self a b)
    (fun {x y v} hx hy hv => NBformArc_add_left ha b hx hy hv)
    (fun {x v w} hx hv hw => NBformArc_add_right ha b hx hv hw)
    (NBformArc_conj_symm a b)
    (fun u hu h0 hne => NQformArc_pos_of_heads_zero ha hb hu.1
      (h0 0 (by simp [hF])) (h0 (-1) (by simp [hF])) hne)
    hvec ?_
  · have hcard : F.card = 2 := by simp [hF]
    rw [hcard] at h
    rw [indArc, nulArc]
    have h' : formIndex (NQformArc a b) ArcDom + formNullity (NBformArc a b) ArcDom + 1
        ≤ 1 + 1 := by
      have h2 : ((2 : ℕ) : ℕ∞) = 1 + 1 := by norm_num
      rwa [h2] at h
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h'
  · intro u hu hheads
    have h0 : u 0 = ((1 / sigmaArc a b 0 : ℝ) : ℂ) := by
      have := hheads ⟨0, by simp [hF]⟩
      simpa [hvec] using this
    have h1 : u (-1) = ((-1 / sigmaArc a b (-1) : ℝ) : ℂ) := by
      have := hheads ⟨-1, by simp [hF]⟩
      simpa [hvec] using this
    exact NQformArc_pos_on_slice ha hb hab hab' hu h0 h1

end KsIndex.ArcUpper
