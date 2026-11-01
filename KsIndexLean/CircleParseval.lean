module

public import KsIndexLean.CircleMeasure
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

@[expose] public section


/-! # Parseval identity for circle arclength measure
The coefficients use the normalized angular integral; circleMeasure itself
has mass 2π. Consequently Parseval contains the explicit factor (2π)⁻¹.
-/
noncomputable section
open MeasureTheory Set
open scoped Real
namespace KsIndex.Trace

/-- Fourier coefficients of a circle function, using its angular pullback. -/
def circleFourierCoeff (f : Circle₁ → ℂ) (n : ℤ) : ℂ :=
  fourierCoeffOn Real.two_pi_pos (fun θ => f (circleParam θ)) n

/-- Parseval with arclength measure, for arbitrary L² data. -/
theorem hasSum_sq_circleFourierCoeff {f : Circle₁ → ℂ}
    (hf : MemLp f 2 circleMeasure) :
    HasSum (fun n : ℤ => ‖circleFourierCoeff f n‖ ^ 2)
      ((2 * π)⁻¹ * ∫ w, ‖f w‖ ^ 2 ∂circleMeasure) := by
  have hp : MemLp (fun θ => f (circleParam θ)) 2
      (volume.restrict (Ico 0 (2 * π))) :=
    hf.comp_of_map measurable_circleParam.aemeasurable
  have hp' : MemLp (fun θ => f (circleParam θ)) 2
      (volume.restrict (Ioc 0 (2 * π))) := by
    simpa only [restrict_Ico_eq_restrict_Ioc] using hp
  have h := hasSum_sq_fourierCoeffOn Real.two_pi_pos hp'
  have hi := integral_circleMeasure (hf.aestronglyMeasurable.norm.pow 2)
  rw [setIntegral_Ico_eq_intervalIntegral] at hi
  simp only [Pi.pow_apply] at hi
  rw [hi]
  simpa only [circleFourierCoeff, sub_zero, smul_eq_mul] using h

theorem tsum_sq_circleFourierCoeff {f : Circle₁ → ℂ}
    (hf : MemLp f 2 circleMeasure) :
    ∑' n : ℤ, ‖circleFourierCoeff f n‖ ^ 2 =
      (2 * π)⁻¹ * ∫ w, ‖f w‖ ^ 2 ∂circleMeasure :=
  (hasSum_sq_circleFourierCoeff hf).tsum_eq

/-- The coefficients depend only on the arclength-a.e. equivalence class. -/
theorem circleFourierCoeff_congr_ae {f g : Circle₁ → ℂ}
    (hfg : f =ᵐ[circleMeasure] g) : circleFourierCoeff f = circleFourierCoeff g := by
  have h := ae_of_ae_map measurable_circleParam.aemeasurable hfg
  have h' : (fun θ => f (circleParam θ)) =ᵐ[volume.restrict (Ioc 0 (2 * π))]
      (fun θ => g (circleParam θ)) := by
    simpa only [Filter.EventuallyEq, restrict_Ico_eq_restrict_Ioc] using h
  exact fourierCoeffOn_congr_ae Real.two_pi_pos h'

/-- Continuous (hence also smooth) circle data satisfy the same Parseval identity. -/
theorem parseval_continuous_circle (f : C(Circle₁, ℂ)) :
    ∑' n : ℤ, ‖circleFourierCoeff f n‖ ^ 2 =
      (2 * π)⁻¹ * ∫ w, ‖f w‖ ^ 2 ∂circleMeasure :=
  tsum_sq_circleFourierCoeff (f.memLp (μ := circleMeasure) (p := 2) ℂ)

end KsIndex.Trace

