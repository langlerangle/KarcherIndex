module

/-
# Finite truncations of a negative coefficient witness

`trunc N t` retains the coefficients with `|ℓ| ≤ N`. For `0 < a < 1`, arbitrary
real `b`, and a sequence with summable `(1+|ℓ|)‖t ℓ‖²`, the quadratic-form error
is bounded by a constant times the weighted tail. The tail tends to zero by
monotone cofinal exhaustion of the integers; no quantitative decay hypothesis
is needed.

Consequently, a negative witness has a finite truncation with negative form
value and arbitrarily small weighted tail (`exists_trunc`). The truncated form
is a finite sum (`NQ_trunc_eq_sum`). These statements concern weighted sequences
and form values; they do not assert that truncation preserves the arc-support
fixed-point condition defining `MemArc`.
-/
public import KsIndexLean.ArcWitness

@[expose] public section


noncomputable section

open Real Set Filter
open KsIndex.ArcForm KsIndex.ArcSpace

namespace KsIndex.ArcTrunc

/-- Truncation: zero every coefficient with `|ℓ| > N`. -/
def trunc (N : ℕ) (t : ℤ → ℂ) : ℤ → ℂ := fun ℓ => if |ℓ| ≤ (N : ℤ) then t ℓ else 0

lemma trunc_apply_of_le {N : ℕ} {t : ℤ → ℂ} {ℓ : ℤ} (h : |ℓ| ≤ (N : ℤ)) :
    trunc N t ℓ = t ℓ := if_pos h

lemma trunc_apply_of_gt {N : ℕ} {t : ℤ → ℂ} {ℓ : ℤ} (h : ¬ |ℓ| ≤ (N : ℤ)) :
    trunc N t ℓ = 0 := if_neg h

/-- The truncated `NQ` series is a finite sum over `Finset.Icc (−N) N`. -/
lemma NQ_trunc_eq_sum (a b : ℝ) (N : ℕ) (t : ℤ → ℂ) :
    NQformArc a b (trunc N t)
      = ∑ ℓ ∈ Finset.Icc (-(N : ℤ)) N, sigmaArc a b ℓ * ‖t ℓ‖ ^ 2 := by
  rw [NQformArc]
  rw [tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) N) (fun ℓ hℓ => ?_)]
  · refine Finset.sum_congr rfl (fun ℓ hℓ => ?_)
    rw [Finset.mem_Icc] at hℓ
    rw [trunc_apply_of_le (abs_le.mpr hℓ)]
  · have habs : ¬ |ℓ| ≤ (N : ℤ) := by
      rw [Finset.mem_Icc] at hℓ
      rw [not_le]
      rcases not_and_or.mp hℓ with h | h
      · rw [not_le] at h
        calc (N : ℤ) < -ℓ := by linarith
          _ ≤ |ℓ| := by rw [← abs_neg]; exact le_abs_self _
      · rw [not_le] at h
        exact lt_of_lt_of_le h (le_abs_self ℓ)
    rw [trunc_apply_of_gt habs, norm_zero]
    ring

/-- The tail of the weighted series, as a `tsum`. -/
def tailW (N : ℕ) (t : ℤ → ℂ) : ℝ :=
  ∑' ℓ : ℤ, if |ℓ| ≤ (N : ℤ) then (0 : ℝ) else (1 + |(ℓ : ℝ)|) * ‖t ℓ‖ ^ 2

/-- The exhaustion `N ↦ Icc (−N) N` is monotone and cofinal. -/
lemma tendsto_Icc_atTop :
    Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) N) atTop atTop := by
  apply Filter.tendsto_atTop_finset_of_monotone
  · intro M N hMN
    apply Finset.Icc_subset_Icc <;> omega
  · intro ℓ
    exact ⟨ℓ.natAbs, Finset.mem_Icc.mpr (by omega)⟩

/-- For summable nonnegative `w`, the tail outside `[-N, N]` tends to zero.
The proof uses convergence of partial sums along a cofinal exhaustion. -/
lemma tendsto_tail_indicator {w : ℤ → ℝ} (hwn : ∀ ℓ, 0 ≤ w ℓ) (hw : Summable w) :
    Tendsto (fun N : ℕ => ∑' ℓ : ℤ, if |ℓ| ≤ (N : ℤ) then (0:ℝ) else w ℓ) atTop (nhds 0) := by
  set W : ℝ := ∑' ℓ : ℤ, w ℓ with hWdef
  -- head + tail = whole, so tail = W − head
  have hhead : ∀ N : ℕ, Summable (fun ℓ : ℤ => if |ℓ| ≤ (N : ℤ) then w ℓ else 0) := by
    intro N
    refine Summable.of_nonneg_of_le (fun ℓ => ?_) (fun ℓ => ?_) hw
    · by_cases h : |ℓ| ≤ (N : ℤ)
      · rw [if_pos h]; exact hwn ℓ
      · rw [if_neg h]
    · by_cases h : |ℓ| ≤ (N : ℤ)
      · rw [if_pos h]
      · rw [if_neg h]; exact hwn ℓ
  have htail : ∀ N : ℕ, Summable (fun ℓ : ℤ => if |ℓ| ≤ (N : ℤ) then (0:ℝ) else w ℓ) := by
    intro N
    refine Summable.of_nonneg_of_le (fun ℓ => ?_) (fun ℓ => ?_) hw
    · by_cases h : |ℓ| ≤ (N : ℤ)
      · rw [if_pos h]
      · rw [if_neg h]; exact hwn ℓ
    · by_cases h : |ℓ| ≤ (N : ℤ)
      · rw [if_pos h]; exact hwn ℓ
      · rw [if_neg h]
  have hsplit : ∀ N : ℕ, (∑' ℓ : ℤ, if |ℓ| ≤ (N : ℤ) then (0:ℝ) else w ℓ)
      = W - ∑ ℓ ∈ Finset.Icc (-(N : ℤ)) N, w ℓ := by
    intro N
    have hadd : (∑' ℓ : ℤ, ((if |ℓ| ≤ (N : ℤ) then w ℓ else 0)
        + if |ℓ| ≤ (N : ℤ) then (0:ℝ) else w ℓ)) = W := by
      rw [hWdef]
      refine tsum_congr (fun ℓ => ?_)
      by_cases h : |ℓ| ≤ (N : ℤ) <;> simp [h]
    rw [(hhead N).tsum_add (htail N)] at hadd
    have hheadsum : (∑' ℓ : ℤ, if |ℓ| ≤ (N : ℤ) then w ℓ else 0)
        = ∑ ℓ ∈ Finset.Icc (-(N : ℤ)) N, w ℓ := by
      rw [tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) N) (fun ℓ hℓ => ?_)]
      · refine Finset.sum_congr rfl (fun ℓ hℓ => ?_)
        rw [Finset.mem_Icc] at hℓ
        rw [if_pos (abs_le.mpr hℓ)]
      · rw [Finset.mem_Icc, not_and_or] at hℓ
        have : ¬ |ℓ| ≤ (N : ℤ) := by
          rw [not_le]
          rcases hℓ with h | h
          · rw [not_le] at h
            calc (N : ℤ) < -ℓ := by linarith
              _ ≤ |ℓ| := by rw [← abs_neg]; exact le_abs_self _
          · rw [not_le] at h
            exact lt_of_lt_of_le h (le_abs_self ℓ)
        rw [if_neg this]
    rw [hheadsum] at hadd
    linarith [hadd]
  have hpart : Tendsto (fun N : ℕ => ∑ ℓ ∈ Finset.Icc (-(N : ℤ)) N, w ℓ) atTop (nhds W) :=
    (hw.hasSum.comp tendsto_Icc_atTop)
  have h0 : Tendsto (fun N : ℕ => W - ∑ ℓ ∈ Finset.Icc (-(N : ℤ)) N, w ℓ) atTop (nhds 0) := by
    have := (tendsto_const_nhds (x := W) (f := atTop (α := ℕ))).sub hpart
    simpa using this
  exact h0.congr (fun N => (hsplit N).symm)

/-- The weighted tail vanishes as `N → ∞` (no decay rate needed). -/
lemma tendsto_tailW {t : ℤ → ℂ}
    (hw : Summable (fun ℓ : ℤ => (1 + |(ℓ : ℝ)|) * ‖t ℓ‖ ^ 2)) :
    Tendsto (fun N : ℕ => tailW N t) atTop (nhds 0) :=
  tendsto_tail_indicator (fun ℓ => by positivity) hw

/-- For `0 < a < 1` and weighted-square-summable `t`, a positive constant
bounds the quadratic-form error by the weighted tail for every truncation. -/
theorem exists_NQ_trunc_perturb {a : ℝ} (ha : a ∈ Set.Ioo (0:ℝ) 1) (b : ℝ) {t : ℤ → ℂ}
    (hw : Summable (fun ℓ : ℤ => (1 + |(ℓ : ℝ)|) * ‖t ℓ‖ ^ 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      |NQformArc a b t - NQformArc a b (trunc N t)| ≤ C * tailW N t := by
  set Cσ : ℝ := 1 + b ^ 2 / min a (1 - a) with hCσdef
  have hm : 0 < min a (1 - a) := lt_min ha.1 (by linarith [ha.2])
  have hCσ0 : 0 < Cσ := by rw [hCσdef]; positivity
  refine ⟨Cσ, hCσ0, fun N => ?_⟩
  have hkey : |NQformArc a b t - NQformArc a b (trunc N t)| ≤ Cσ * tailW N t := by
    have hSt := summable_sigmaArc_mul_sq ha b hw
    have hStrunc : Summable (fun ℓ : ℤ => sigmaArc a b ℓ * ‖trunc N t ℓ‖ ^ 2) := by
      refine Summable.of_norm (Summable.of_nonneg_of_le (fun ℓ => norm_nonneg _)
        (fun ℓ => ?_) hSt.abs)
      by_cases h : |ℓ| ≤ (N : ℤ)
      · rw [trunc_apply_of_le h, Real.norm_eq_abs]
      · rw [trunc_apply_of_gt h, Real.norm_eq_abs, norm_zero]
        rw [show (0:ℝ) ^ 2 = 0 by ring, mul_zero, abs_zero]
        exact abs_nonneg _
    have hdiff : NQformArc a b t - NQformArc a b (trunc N t)
        = ∑' ℓ : ℤ, (sigmaArc a b ℓ * ‖t ℓ‖ ^ 2 - sigmaArc a b ℓ * ‖trunc N t ℓ‖ ^ 2) := by
      rw [NQformArc, NQformArc]
      exact (hSt.tsum_sub hStrunc).symm
    rw [hdiff]
    -- termwise: the difference is the tail indicator of σ‖t‖²
    have hterm : ∀ ℓ : ℤ,
        |sigmaArc a b ℓ * ‖t ℓ‖ ^ 2 - sigmaArc a b ℓ * ‖trunc N t ℓ‖ ^ 2|
          ≤ Cσ * (if |ℓ| ≤ (N : ℤ) then (0:ℝ) else (1 + |(ℓ : ℝ)|) * ‖t ℓ‖ ^ 2) := by
      intro ℓ
      by_cases h : |ℓ| ≤ (N : ℤ)
      · rw [trunc_apply_of_le h, sub_self, abs_zero, if_pos h, mul_zero]
      · rw [trunc_apply_of_gt h, if_neg h, norm_zero]
        have hσ := abs_sigmaArc_le ha b ℓ
        have h2 : |sigmaArc a b ℓ * ‖t ℓ‖ ^ 2 - sigmaArc a b ℓ * 0 ^ 2|
            = |sigmaArc a b ℓ| * ‖t ℓ‖ ^ 2 := by
          rw [show (0:ℝ) ^ 2 = 0 by ring, mul_zero, sub_zero, abs_mul,
            abs_of_nonneg (sq_nonneg ‖t ℓ‖)]
        rw [h2, hCσdef]
        calc |sigmaArc a b ℓ| * ‖t ℓ‖ ^ 2
            ≤ ((1 + b ^ 2 / min a (1 - a)) * (1 + |(ℓ : ℝ)|)) * ‖t ℓ‖ ^ 2 :=
              mul_le_mul_of_nonneg_right hσ (sq_nonneg _)
          _ = (1 + b ^ 2 / min a (1 - a)) * ((1 + |(ℓ : ℝ)|) * ‖t ℓ‖ ^ 2) := by ring
    -- summable majorant, then |tsum| ≤ tsum
    have hmaj : Summable (fun ℓ : ℤ =>
        Cσ * (if |ℓ| ≤ (N : ℤ) then (0:ℝ) else (1 + |(ℓ : ℝ)|) * ‖t ℓ‖ ^ 2)) := by
      refine Summable.mul_left Cσ ?_
      refine Summable.of_nonneg_of_le (fun ℓ => ?_) (fun ℓ => ?_) hw
      · by_cases h : |ℓ| ≤ (N : ℤ)
        · rw [if_pos h]
        · rw [if_neg h]; positivity
      · by_cases h : |ℓ| ≤ (N : ℤ)
        · rw [if_pos h]; positivity
        · rw [if_neg h]
    have hnorm_sum : Summable (fun ℓ : ℤ =>
        ‖sigmaArc a b ℓ * ‖t ℓ‖ ^ 2 - sigmaArc a b ℓ * ‖trunc N t ℓ‖ ^ 2‖) := by
      refine Summable.of_nonneg_of_le (fun ℓ => norm_nonneg _) (fun ℓ => ?_) hmaj
      rw [Real.norm_eq_abs]
      exact hterm ℓ
    have habs := norm_tsum_le_tsum_norm (f := fun ℓ : ℤ =>
        sigmaArc a b ℓ * ‖t ℓ‖ ^ 2 - sigmaArc a b ℓ * ‖trunc N t ℓ‖ ^ 2) hnorm_sum
    rw [Real.norm_eq_abs] at habs
    refine le_trans habs ?_
    have h2 := hnorm_sum.tsum_le_tsum (fun ℓ => by
      rw [Real.norm_eq_abs]
      exact hterm ℓ) hmaj
    refine le_trans h2 (le_of_eq ?_)
    rw [tsum_mul_left]
    rfl
  exact hkey

/-- For `0 < a < 1`, a weighted-square-summable negative witness has a finite
truncation that remains negative and has weighted tail less than any given `ε > 0`. -/
theorem exists_trunc {a : ℝ} (ha : a ∈ Set.Ioo (0:ℝ) 1) (b : ℝ) {t : ℤ → ℂ}
    (hw : Summable (fun ℓ : ℤ => (1 + |(ℓ : ℝ)|) * ‖t ℓ‖ ^ 2))
    (hneg : NQformArc a b t < 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, NQformArc a b (trunc N t) < 0 ∧ tailW N t < ε := by
  obtain ⟨Cσ, hCσ0, hkey⟩ := exists_NQ_trunc_perturb ha b hw
  set m : ℝ := -(NQformArc a b t) with hmdef
  have hm0 : 0 < m := by rw [hmdef]; linarith
  -- pick N with Cσ · tailW < m/2 (and tailW < ε)
  have htail := tendsto_tailW hw
  have hδ' : (0:ℝ) < min (m / (2 * Cσ)) ε := lt_min (by positivity) hε
  have hev : ∀ᶠ N : ℕ in atTop, tailW N t < min (m / (2 * Cσ)) ε :=
    htail.eventually_lt_const hδ'
  obtain ⟨N, hN⟩ := hev.exists
  refine ⟨N, ?_, lt_of_lt_of_le hN (min_le_right _ _)⟩
  have h1 : NQformArc a b (trunc N t) ≤ NQformArc a b t + Cσ * tailW N t := by
    have := (abs_le.mp (hkey N)).1
    linarith
  have h2 : Cσ * tailW N t < m / 2 := by
    have htw : tailW N t < m / (2 * Cσ) := lt_of_lt_of_le hN (min_le_left _ _)
    have h3 : Cσ * tailW N t < Cσ * (m / (2 * Cσ)) := by
      exact mul_lt_mul_of_pos_left htw hCσ0
    have h4 : Cσ * (m / (2 * Cσ)) = m / 2 := by
      field_simp
    linarith
  have hNQt : NQformArc a b t = -m := by rw [hmdef]; ring
  rw [hNQt] at h1
  linarith

end KsIndex.ArcTrunc
