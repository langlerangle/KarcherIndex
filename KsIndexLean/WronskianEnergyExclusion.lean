module

public import KsIndexLean.RadialWronskian
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace

lemma eq_zero_of_log_bounds {C b B : ℝ} (hC : 0 ≤ C) (hb : 0 < b)
    (h : ∀ a : ℝ, 0 < a → a < b → C * Real.log (b / a) ≤ B) : C = 0 := by
  by_contra hn
  have hCp : 0 < C := lt_of_le_of_ne hC (Ne.symm hn)
  let a := Real.exp (Real.log b - (|B| + 1) / C)
  have ha : 0 < a := Real.exp_pos _
  have hab : a < b := by
    rw [← Real.exp_log hb]
    apply Real.exp_lt_exp.mpr
    have hp : 0 < (|B| + 1) / C := div_pos (by positivity) hCp
    linarith
  have he := h a ha hab
  rw [Real.log_div hb.ne' ha.ne', show Real.log a = Real.log b - (|B| + 1) / C from Real.log_exp _] at he
  have hx : C * (Real.log b - (Real.log b - (|B| + 1) / C)) = |B| + 1 := by
    field_simp
    ring
  rw [hx] at he
  linarith [le_abs_self B]

/-- Finite weighted value and derivative energies force a conserved radial
Wronskian against a comparison profile with bounded value and derivative to vanish. -/
lemma radialWronskian_eq_zero_of_energy {f f' g g' : ℝ → ℂ} {c : ℂ} {M B : ℝ}
    (hf : ContinuousOn f (Ioo (0 : ℝ) 1)) (hf' : ContinuousOn f' (Ioo (0 : ℝ) 1))
    (hM : 0 ≤ M)
    (hg : ∀ r ∈ Ioo (0 : ℝ) 1, ‖g r‖ ≤ M)
    (hg' : ∀ r ∈ Ioo (0 : ℝ) 1, ‖g' r‖ ≤ M)
    (hW : ∀ r ∈ Ioo (0 : ℝ) 1, radialWronskian f f' g g' r = c)
    (hE : ∀ a : ℝ, 0 < a → a < 1 / 2 →
      (∫ r in Ioo a (1 / 2), r * ‖f' r‖ ^ 2 + r * ‖f r‖ ^ 2) ≤ B) : c = 0 := by
  have hz : ‖c‖ ^ 2 = 0 := by
    apply eq_zero_of_log_bounds (sq_nonneg _) (by norm_num : (0 : ℝ) < 1 / 2)
      (B := 2 * M ^ 2 * B)
    intro a ha hab
    have hsub : Icc a (1 / 2 : ℝ) ⊆ Ioo (0 : ℝ) 1 := by
      intro r hr
      exact ⟨ha.trans_le hr.1, hr.2.trans_lt (by norm_num)⟩
    have hEi : IntegrableOn (fun r => r * ‖f' r‖ ^ 2 + r * ‖f r‖ ^ 2)
        (Ioo a (1 / 2 : ℝ)) volume :=
      ((continuousOn_id.mul ((hf'.mono hsub).norm.pow 2)).add
        (continuousOn_id.mul ((hf.mono hsub).norm.pow 2))).integrableOn_Icc.mono_set Ioo_subset_Icc_self
    have hci : IntegrableOn (fun r : ℝ => ‖c‖ ^ 2 / r) (Ioo a (1 / 2 : ℝ)) volume :=
      (continuousOn_const.div continuousOn_id (fun r hr => (ha.trans_le hr.1).ne')).integrableOn_Icc.mono_set
        Ioo_subset_Icc_self
    have hi : (∫ r in Ioo a (1 / 2), ‖c‖ ^ 2 / r) ≤
        2 * M ^ 2 * (∫ r in Ioo a (1 / 2), r * ‖f' r‖ ^ 2 + r * ‖f r‖ ^ 2) := by
      rw [← integral_const_mul]
      apply integral_mono_ae hci (hEi.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      have hrI := hsub (Ioo_subset_Icc_self hr)
      rw [← hW r hrI]
      exact radialWronskian_norm_sq_div_le hrI.1 hM (hg r hrI) (hg' r hrI)
    have he : (∫ r in Ioo a (1 / 2 : ℝ), ‖c‖ ^ 2 / r) =
        ‖c‖ ^ 2 * Real.log ((1 / 2) / a) := by
      have hdiv (r : ℝ) : ‖c‖ ^ 2 / r = ‖c‖ ^ 2 * r⁻¹ := div_eq_mul_inv _ _
      simp_rw [hdiv]
      rw [integral_const_mul, restrict_Ioo_eq_restrict_Ioc,
        ← intervalIntegral.integral_of_le hab.le, integral_inv_of_pos ha (by norm_num)]
    rw [he] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left (hE a ha hab) (by positivity))
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

lemma eq_const_mul_of_radialWronskian_zero {f f' g g' : ℝ → ℂ}
    (hf : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' r) r)
    (hg : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt g (g' r) r)
    (hgn : ∀ r ∈ Ioo (0 : ℝ) 1, g r ≠ 0)
    (hW : ∀ r ∈ Ioo (0 : ℝ) 1, radialWronskian f f' g g' r = 0) :
    ∃ c : ℂ, ∀ r ∈ Ioo (0 : ℝ) 1, f r = c * g r := by
  have hd : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun t => f t / g t) 0 r := by
    intro r hr
    have hw := hW r hr
    have he : (r : ℂ) * (f' r * g r - f r * g' r) = 0 := by
      dsimp only [radialWronskian] at hw
      linear_combination hw
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.1.ne'
    have hz := (mul_eq_zero.mp he).resolve_left hr0
    exact ((hf r hr).div (hg r hr) (hgn r hr)).congr_deriv (by rw [hz, zero_div])
  have hc : ∀ r ∈ Ioo (0 : ℝ) 1, f r / g r = f (1 / 2) / g (1 / 2) := by
    intro r hr
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hd x hx).deriv) hr (by norm_num)
  refine ⟨f (1 / 2) / g (1 / 2), ?_⟩
  intro r hr
  rw [← hc r hr, div_mul_cancel₀ _ (hgn r hr)]

end KsIndex.Trace
