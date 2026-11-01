module

public import KsIndexLean.KarcherGlobalGaussianCurvature
public import KsIndexLean.KarcherPotentialIntegral
public import KsIndexLean.KarcherQuotientCurvature

@[expose] public section


/-! Total curvature of the EW period quotient, with respect to its induced area. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData
open scoped QuotientArea

lemma integrableOn_disk_potV (k : ℕ) : IntegrableOn (Surface.potV k)
    (Metric.ball (0 : ℂ) 1) volume := by
  exact ((CutoffContinuity.continuous_potV k).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : ℂ) 1)).mono_set Metric.ball_subset_closedBall

lemma lintegral_disk_potV {k : ℕ} (hk : 2 ≤ k) :
    (∫⁻ z in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (Surface.potV k z)) =
      ENNReal.ofReal (4 * Real.pi * ((k : ℝ) - 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_disk_potV k)
    (Filter.Eventually.of_forall (SurfaceForm.potV_nonneg k)), integral_disk_potV hk]

namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

lemma lintegral_quotientAbsA_sq :
    (∫⁻ q, ENNReal.ofReal (R.quotientAbsA (m := m) q ^ 2) ∂(R.quotientArea)) =
      ENNReal.ofReal (8 * Real.pi * ((k : ℝ) - 1) * (m : ℝ)) := by
  have ht := R.lintegral_quotientPotential (m := m) (fun _ => (1 : ℂ)) continuous_const
  simp only [norm_one, one_pow, mul_one] at ht
  rw [ht, R.ewPotentialEnergyGeom_eq_flat _ continuous_const]
  unfold ewPotentialEnergyFlat
  have hc : ∀ n : ZMod (2 * m),
      (∫⁻ z, ENNReal.ofReal (Surface.potV k z *
        ‖encodeDiskFunction (R.diskFunctionPullback (fun _ => (1 : ℂ))) n z‖ ^ 2)) =
      ENNReal.ofReal (4 * Real.pi * ((k : ℝ) - 1)) := by
    intro n
    rw [← lintegral_disk_potV h.out, ← lintegral_indicator measurableSet_ball]
    apply lintegral_congr_ae
    have ha : ∀ᵐ z : ℂ ∂volume, ‖z‖ ≠ 1 := by
      apply ae_iff.mpr
      simpa [Metric.sphere, dist_zero_right] using Measure.addHaar_sphere volume (0 : ℂ) 1
    filter_upwards [ha] with z hz
    by_cases hd : z ∈ Metric.ball (0 : ℂ) 1
    · have hn : ‖z‖ < 1 := by simpa using hd
      have hp := not_puncture_of_norm_lt_one h.out hn
      simp [Set.indicator_of_mem hd, encodeDiskFunction, hp, hn.le, diskFunctionPullback]
    · have hn : 1 < ‖z‖ := lt_of_le_of_ne (by simpa using hd) hz.symm
      simp [Set.indicator_of_notMem hd, encodeDiskFunction_exterior _ n z hn]
  simp only [hc, Finset.sum_const, Finset.card_univ, ZMod.card]
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  push_cast
  ring

/-- Squared norm of the second fundamental form is genuinely integrable. -/
lemma integrable_quotientAbsA_sq :
    Integrable (fun q => R.quotientAbsA (m := m) q ^ 2) R.quotientArea := by
  refine ⟨(R.measurable_quotientAbsA.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),
    R.lintegral_quotientAbsA_sq]
  exact ENNReal.ofReal_lt_top

lemma integral_quotientAbsA_sq :
    (∫ q, R.quotientAbsA (m := m) q ^ 2 ∂(R.quotientArea)) =
      8 * Real.pi * ((k : ℝ) - 1) * (m : ℝ) := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    R.integrable_quotientAbsA_sq.aestronglyMeasurable,
    R.lintegral_quotientAbsA_sq, ENNReal.toReal_ofReal]
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by have := h.out; omega)
  positivity

/-- A measurable representative of Gaussian curvature on the period quotient.
Its agreement with the determinant of the actual fundamental forms is proved
in `quotientGaussianCurvature_ae_geometry`. -/
def quotientGaussianCurvature
    (q : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) : ℝ :=
  -(R.quotientAbsA q ^ 2) / 2

lemma quotientGaussianCurvature_ae_geometry :
    ∀ᵐ x ∂(R.quotientArea (m := m)),
      ∃ (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (v : PuncturedPlane k),
        HeightLift.periodQuotientMap m q = x ∧ HeightLift.projection q = finiteParameter v ∧
        R.quotientGaussianCurvature x = chartGaussianCurvature (R.centeredChart q) v.val := by
  filter_upwards [R.quotientAbsA_ae_geometry (m := m)] with x hx
  obtain ⟨q, v, hq, hv, he⟩ := hx
  refine ⟨q, v, hq, hv, ?_⟩
  have hc := R.centeredChart_gaussianCurvature q
  rw [R.chartCenter_finite q v hv] at hc
  rw [quotientGaussianCurvature, he, (R.centeredChart_finite_curvature q v hv).2, hc]

lemma integrable_quotientGaussianCurvature :
    Integrable (R.quotientGaussianCurvature (m := m)) R.quotientArea :=
  R.integrable_quotientAbsA_sq.neg.div_const 2

/-- The total Gaussian curvature of the actual EW m-period quotient. -/
theorem integral_quotientGaussianCurvature :
    (∫ q, R.quotientGaussianCurvature (m := m) q ∂(R.quotientArea)) =
      -4 * Real.pi * ((k : ℝ) - 1) * (m : ℝ) := by
  simp only [quotientGaussianCurvature, integral_div, integral_neg,
    R.integral_quotientAbsA_sq]
  ring

end PaperHalfPeriodRealization
end KsIndex.KarcherData
