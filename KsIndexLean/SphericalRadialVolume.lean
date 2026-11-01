module

public import KsIndexLean.SphericalRadialChangeOfVariables
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

@[expose] public section


open Set MeasureTheory intervalIntegral
open scoped ENNReal
noncomputable section
namespace KsIndex.Spherical

lemma volume_preserving_radialCoord : MeasurePreserving radialCoord volume volume := by
  have hc := Complex.volume_preserving_equiv_pi.symm Complex.measurableEquivPi
  have hp := (MeasurePreserving.id (volume : Measure ℝ)).prod hc
  have hh := hp.comp (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)
  convert! hh using 1
  funext p
  simp [radialCoord_apply, MeasurableEquiv.piFinSuccAbove_apply, mul_comm, Fin.tail]

lemma volume_preserving_ambient_coordinates :
    MeasurePreserving (WithLp.ofLp : Ambient → (Fin 3 → ℝ)) volume volume :=
  PiLp.volume_preserving_ofLp (Fin 3)

lemma lintegral_radius_sq :
    ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r ^ 2) ∂volume = ENNReal.ofReal (1 / 3 : ℝ) := by
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal (intervalIntegrable_pow 2).1,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  · norm_num
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    positivity

lemma lintegral_radial_product (s : Set ℂ) (h : ℂ → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ p in Ioo (0 : ℝ) 1 ×ˢ s, ENNReal.ofReal (p.1 ^ 2) * h p.2 ∂volume =
      ENNReal.ofReal (1 / 3 : ℝ) * ∫⁻ z in s, h z ∂volume := by
  change (∫⁻ p, ENNReal.ofReal (p.1 ^ 2) * h p.2
    ∂(volume.prod volume).restrict (Ioo (0 : ℝ) 1 ×ˢ s)) = _
  rw [← Measure.prod_restrict]
  have hf : AEMeasurable (fun r : ℝ => ENNReal.ofReal (r ^ 2))
      (volume.restrict (Ioo (0 : ℝ) 1)) := by fun_prop
  have hg : AEMeasurable h (volume.restrict s) := hh.aemeasurable
  rw [lintegral_prod_mul hf hg, lintegral_radius_sq]

end KsIndex.Spherical
