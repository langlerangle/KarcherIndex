module

public import KsIndexLean.CircleSobolevL2
public import KsIndexLean.BoundaryArcClosure
public import KsIndexLean.NodeCSymbol

@[expose] public section


/-!
# The paper trial function `Ψ`

The paper's explicit trial function for the middle-class `Q`-lower bound:
`Ψ = 1 − e^{−iθ}` on the support arc `boundaryArc 1 1` (`Re w > 0`), and
`(2−π)/(2+π)·(1 − e^{−iθ})` off it.  On the circle `e^{−iθ} = conj w`.

We cut the arc at `0 ≤ Re w` (differing from the open arc only on the null set
`{±i}`), so `{Re w ≥ 0}` (= `closure (boundaryArc 1 1)`, the DN support) and
`{Re w < 0}` (= `boundaryArc 1 0`, where DN data vanish) partition the circle
exactly.  This file: the definition, `MemLp` realization, and the on-support value.
-/

noncomputable section
open MeasureTheory Complex
namespace KsIndex.NodeC
open KsIndex.Trace KsIndex.CircleSobolev KsIndex.WeakH1

/-- The off-arc damping factor `(2−π)/(2+π)` from the paper trial function. -/
def psiFactor : ℝ := (2 - Real.pi) / (2 + Real.pi)

/-- The paper trial function `Ψ w = (1 − conj w)·[1 on `Re w ≥ 0`, else `(2−π)/(2+π)`]`. -/
def trialPsi (w : Circle₁) : ℂ :=
  (1 - (starRingEnd ℂ) (w : ℂ)) * (if 0 ≤ (w : ℂ).re then 1 else (psiFactor : ℂ))

/-- `|psiFactor| < 1` (since `π > 2`). -/
lemma abs_psiFactor_lt_one : |psiFactor| < 1 := by
  change |(2 - Real.pi) / (2 + Real.pi)| < 1
  have hpi : (2 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  rw [abs_div, abs_of_neg (by linarith : 2 - Real.pi < 0),
    abs_of_pos (by linarith : (0 : ℝ) < 2 + Real.pi),
    div_lt_one (by linarith : (0 : ℝ) < 2 + Real.pi)]
  linarith

/-- The trial function is measurable. -/
lemma measurable_trialPsi : Measurable trialPsi := by
  unfold trialPsi
  refine Measurable.mul ?_ ?_
  · exact measurable_const.sub (Complex.continuous_conj.measurable.comp measurable_subtype_coe)
  · refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_le measurable_const
      (Complex.measurable_re.comp measurable_subtype_coe)

/-- Pointwise bound `‖Ψ w‖ ≤ 2` on the unit circle. -/
lemma norm_trialPsi_le (w : Circle₁) : ‖trialPsi w‖ ≤ 2 := by
  have hw : ‖(w : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
  unfold trialPsi
  rw [norm_mul]
  have h1 : ‖1 - (starRingEnd ℂ) (w : ℂ)‖ ≤ 2 := by
    calc ‖1 - (starRingEnd ℂ) (w : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖(starRingEnd ℂ) (w : ℂ)‖ :=
          norm_sub_le _ _
      _ = 2 := by rw [norm_one, starRingEnd_apply, norm_star, hw]; norm_num
  have h2 : ‖(if 0 ≤ (w : ℂ).re then (1 : ℂ) else (psiFactor : ℂ))‖ ≤ 1 := by
    split_ifs with h
    · rw [norm_one]
    · rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_psiFactor_lt_one.le
  calc ‖1 - (starRingEnd ℂ) (w : ℂ)‖ *
        ‖(if 0 ≤ (w : ℂ).re then (1 : ℂ) else (psiFactor : ℂ))‖
      ≤ 2 * 1 := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
    _ = 2 := by norm_num

/-- The trial function is in `L²(circleMeasure)`. -/
lemma trialPsi_memLp : MemLp trialPsi 2 circleMeasure := by
  have : IsFiniteMeasure circleMeasure :=
    ⟨by rw [circleMeasure_univ]; exact ENNReal.ofReal_lt_top⟩
  refine MemLp.of_bound measurable_trialPsi.aestronglyMeasurable 2 ?_
  filter_upwards with w using norm_trialPsi_le w

/-- On the DN support `Re w ≥ 0` (= `closure (boundaryArc 1 1)`), `Ψ = 1 − conj w`. -/
lemma trialPsi_of_re_nonneg {w : Circle₁} (hw : 0 ≤ (w : ℂ).re) :
    trialPsi w = 1 - (starRingEnd ℂ) (w : ℂ) := by
  simp [trialPsi, hw]

end KsIndex.NodeC
