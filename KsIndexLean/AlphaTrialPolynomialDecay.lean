module

public import KsIndexLean.PowerArcPolynomialShift
public import KsIndexLean.AlphaResidualSummability
public import KsIndexLean.AlphaRemarkTrial

@[expose] public section


/-! Absolute transpose summability for the fixed rational threshold trial. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ PowerArc WeightedConvolution AlphaResidual

theorem convS_trial_decay : ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℤ,
    ‖convS trial m‖ ≤ C * weight m ^ (-(11/8 : ℝ)) := by
  have hβ (i : Fin 25) : (2/5 : ℝ) ≤ exponent i := by fin_cases i <;> norm_num [exponent]
  have hβ1 (i : Fin 25) : exponent i ≤ 1 := by fin_cases i <;> norm_num [exponent]
  choose C hC hb using (fun i : Fin 25 => exists_shift_decay (hβ i) (hβ1 i) (shift i+1))
  let D : Fin 25 → ℝ := fun i => ‖coefficient i‖ * (C i / |g (exponent i) 0|)
  refine ⟨∑ i : Fin 25, D i, Finset.sum_nonneg (fun i _ => ?_), ?_⟩
  · exact mul_nonneg (norm_nonneg _) (div_nonneg (hC i) (abs_nonneg _))
  · intro m
    rw [convS_trial]
    calc
      _ ≤ ∑ i : Fin 25, ‖coefficient i *
          (g (exponent i) (2*(m:ℝ)+(shift i+1)) / g (exponent i) 0 : ℝ)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i : Fin 25, D i * weight m ^ (-(11/8 : ℝ)) := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div]
        have hh := hb i m
        push_cast at hh
        have hd := div_le_div_of_nonneg_right hh (abs_nonneg (g (exponent i) 0))
        have hm := mul_le_mul_of_nonneg_left hd (norm_nonneg (coefficient i))
        dsimp [D]
        convert hm using 1; first | rfl | ring
      _ = _ := by rw [Finset.sum_mul]

/-- The actual trial satisfies absolute double summability against every domain vector. -/
theorem trial_double_summable {z : ℤ → ℂ} (hz : MemDom z) :
    Summable (fun p : ℤ × ℤ => (sigM p.1 : ℂ) *
      (starRingEnd ℂ) (convS trial p.1) * (chat (p.1-p.2) : ℂ) * z p.2) := by
  obtain ⟨C, hC, hb⟩ := convS_trial_decay
  exact double_summable_of_decay (mul_nonneg (by norm_num) hC)
    (transpose_factor_decay hb) hz

/-- The transpose residual formula for the fixed trial has no extra summability hypothesis. -/
theorem trial_Bform_eq_coefficientResidual {s : ℝ} {z : ℤ → ℂ} (hz : MemDom z) :
    Statements.Bform s trial z = ∑' n, coefficientResidual s trial n * z n :=
  Bform_eq_coefficientResidual trial_memDom hz (trial_double_summable hz)

/-- The certificate test space uses the residual with its zero coefficient removed. -/
theorem trial_Bform_eq_headZeroResidual {s : ℝ} {z : ℤ → ℂ}
    (hz : MemDom z) (hz0 : z 0 = 0) :
    Statements.Bform s trial z =
      ∑' n, (if n = 0 then 0 else coefficientResidual s trial n) * z n :=
  Bform_eq_headZeroResidual trial_memDom hz hz0 (trial_double_summable hz)

end KsIndex.AlphaRemarkTrial
