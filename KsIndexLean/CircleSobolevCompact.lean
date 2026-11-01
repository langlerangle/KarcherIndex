module

public import KsIndexLean.CircleSobolevApproximation

@[expose] public section


/-! Compactness of the half-order inclusion by uniform finite Fourier approximation. -/
noncomputable section
open Filter
namespace KsIndex.CircleSobolev

lemma half_weight_sq (n : ℤ) : weight (1 / 2 : ℝ) n ^ 2 = 1 + |(n : ℝ)| := by
  rw [weight_sq]
  norm_num

/-- Uniform decay of the reciprocal half-order weight outside a finite set. -/
lemma exists_finite_half_tail (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset ℤ, ∀ n ∉ F, 1 ≤ ε * weight (1 / 2 : ℝ) n := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε ^ 2)
  refine ⟨Finset.Icc (-(N : ℤ)) (N : ℤ), ?_⟩
  intro n hn
  have hn' : ¬ (-(N : ℤ) ≤ n ∧ n ≤ (N : ℤ)) := by simpa using hn
  have hab : (N : ℝ) ≤ |(n : ℝ)| := by
    rcases lt_or_ge n (-(N : ℤ)) with h | h
    · have hr : (n : ℝ) < -(N : ℝ) := by exact_mod_cast h
      have hh := neg_le_abs (n : ℝ)
      linarith
    · have hr : (N : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_not_ge (fun hh => hn' ⟨h, hh⟩))
      exact le_trans hr.le (le_abs_self _)
  have he : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hlarge : 1 < (N : ℝ) * ε ^ 2 := (div_lt_iff₀ he).mp hN
  have hw := weight_pos (1 / 2 : ℝ) n
  have hs := half_weight_sq n
  have hmul := mul_le_mul_of_nonneg_right hab he.le
  have hsprod := congrArg (fun x : ℝ => ε ^ 2 * x) hs
  have hpos := mul_pos hε hw
  nlinarith [sq_nonneg (ε * weight (1 / 2 : ℝ) n - 1)]

lemma half_tail_coordinate_bound (F : Finset ℤ) (ε : ℝ) (hε : 0 ≤ ε)
    (hF : ∀ n ∉ F, 1 ≤ ε * weight (1 / 2 : ℝ) n)
    (u : Space (1 / 2 : ℝ)) (n : ℤ) :
    ‖(inclusion (show (0 : ℝ) ≤ 1 / 2 by norm_num) u -
      truncate 0 F (inclusion (show (0 : ℝ) ≤ 1 / 2 by norm_num) u)) n‖ ≤
        ‖((ε : ℂ) • u) n‖ := by
  change ‖inclusion _ u n - truncate 0 F (inclusion _ u) n‖ ≤ ‖(ε : ℂ) • u n‖
  rw [truncate_apply]
  by_cases hn : n ∈ F
  · rw [ite_eq_left hn, sub_self, norm_zero]
    exact norm_nonneg _
  · rw [ite_eq_right hn, sub_zero]
    have hu : ‖u n‖ = weight (1 / 2 : ℝ) n * ‖coeff (1 / 2 : ℝ) u n‖ := by
      conv_lhs => rw [← weight_mul_coeff (1 / 2 : ℝ) u n]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (weight_pos _ _)]
    have hi : inclusion (show (0 : ℝ) ≤ 1 / 2 by norm_num) u n = coeff (1 / 2 : ℝ) u n := by
      simp [inclusion, weight]
    rw [hi, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε, hu]
    nlinarith [mul_le_mul_of_nonneg_right (hF n hn) (norm_nonneg (coeff (1 / 2 : ℝ) u n))]

theorem half_tail_norm_bound (F : Finset ℤ) (ε : ℝ) (hε : 0 ≤ ε)
    (hF : ∀ n ∉ F, 1 ≤ ε * weight (1 / 2 : ℝ) n) (u : Space (1 / 2 : ℝ)) :
    ‖inclusion (show (0 : ℝ) ≤ 1 / 2 by norm_num) u -
      truncate 0 F (inclusion (show (0 : ℝ) ≤ 1 / 2 by norm_num) u)‖ ≤ ε * ‖u‖ := by
  have h := lp.norm_mono (x := inclusion (show (0 : ℝ) ≤ 1 / 2 by norm_num) u -
    truncate 0 F (inclusion (show (0 : ℝ) ≤ 1 / 2 by norm_num) u))
    (y := (ε : ℂ) • u) (by norm_num : (2 : ENNReal) ≠ 0)
    (half_tail_coordinate_bound F ε hε hF u)
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε] using h

def halfInclusion : Space (1 / 2 : ℝ) →L[ℂ] Space 0 :=
  inclusionCLM (show (0 : ℝ) ≤ 1 / 2 by norm_num)

def halfTruncatedInclusion (F : Finset ℤ) : Space (1 / 2 : ℝ) →L[ℂ] Space 0 :=
  (truncateCLM 0 F).comp halfInclusion

/-- Uniform finite Fourier approximation in operator norm. -/
theorem tendsto_halfTruncatedInclusion :
    Tendsto halfTruncatedInclusion atTop (nhds halfInclusion) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨F, hF⟩ := exists_finite_half_tail (ε / 2) (by positivity)
  filter_upwards [eventually_ge_atTop F] with G hG
  rw [dist_eq_norm, norm_sub_rev]
  have hb : ‖halfInclusion - halfTruncatedInclusion G‖ ≤ ε / 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro u
    change ‖inclusion (show (0 : ℝ) ≤ 1 / 2 by norm_num) u -
      truncateCLM 0 G (inclusion (show (0 : ℝ) ≤ 1 / 2 by norm_num) u)‖ ≤ _
    rw [truncateCLM_apply]
    exact half_tail_norm_bound G (ε / 2) (by positivity)
      (fun n hn => hF n (fun h => hn (hG h))) u
  linarith

/-- Compact half-order inclusion into coefficient L2. -/
theorem isCompactOperator_halfInclusion : IsCompactOperator halfInclusion := by
  apply isCompactOperator_of_tendsto tendsto_halfTruncatedInclusion
  exact Filter.Eventually.of_forall fun F =>
    (isCompactOperator_truncateCLM 0 F).comp_clm halfInclusion

/-- Compact H^(1/2) inclusion into the existing geometric circle L2 space. -/
theorem isCompactOperator_toL2_half :
    IsCompactOperator (toL2 (show (0 : ℝ) ≤ 1 / 2 by norm_num)) := by
  exact isCompactOperator_halfInclusion.clm_comp
    KsIndex.Trace.circleFourierCLE.symm.toContinuousLinearMap

end KsIndex.CircleSobolev
