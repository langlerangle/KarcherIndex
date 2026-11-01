module

public import KsIndexLean.CircleFourierTransport
public import KsIndexLean.DiskTraceBound
public import KsIndexLean.ArcInversionEnergy
public import KsIndexLean.ModeTraceEstimate

@[expose] public section


/-! Fourier coefficients of the actual weak disk radial representative. -/
noncomputable section
open MeasureTheory Set
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Evaluation of a physical boundary Fourier coefficient as a bounded linear map. -/
def circleCoefficientCLM (n : ℤ) : Lp ℂ 2 circleMeasure →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).comp circleFourierCLE.toContinuousLinearMap

@[simp] theorem circleCoefficientCLM_apply (n : ℤ) (f : Lp ℂ 2 circleMeasure) :
    circleCoefficientCLM n f = circleFourierCoeff f n := by
  change circleFourierCLE f n = _
  exact circleFourierCLE_apply f n

def diskMode (u : ComplexH1) (n : ℤ) (r : ℝ) : ℂ :=
  circleCoefficientCLM n (diskRepresentative u r)

def diskRadialMode (u : ComplexH1) (n : ℤ) (r : ℝ) : ℂ :=
  circleCoefficientCLM n (diskRadialProfile u r)

theorem diskMode_continuousOn (u : ComplexH1) (n : ℤ) :
    ContinuousOn (diskMode u n) (Icc (1 / 2 : ℝ) 1) :=
  (circleCoefficientCLM n).continuous.comp_continuousOn (diskRepresentative_continuousOn u)

/-- Fourier extraction commutes with the actual weak radial integral identity. -/
theorem diskMode_sub_eq_integral (u : ComplexH1) (n : ℤ) {s t : ℝ}
    (hs : s ∈ Icc (1 / 2 : ℝ) 1) (ht : t ∈ Icc (1 / 2 : ℝ) 1) :
    diskMode u n t - diskMode u n s = ∫ r in s..t, diskRadialMode u n r := by
  have hg := (disk_weak_polar u).2.1
  have hsub : uIcc s t ⊆ uIcc (1 / 2 : ℝ) 1 := by
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    exact uIcc_subset_Icc hs ht
  have h := representative_sub_eq_integral (by norm_num : (1 / 2 : ℝ) < 1)
    (diskProfile u) hg hs ht
  change diskRepresentative u t - diskRepresentative u s = _ at h
  change circleCoefficientCLM n (diskRepresentative u t) -
    circleCoefficientCLM n (diskRepresentative u s) = _
  rw [← map_sub, h, ← (circleCoefficientCLM n).intervalIntegral_comp_comm (hg.mono_set hsub)]
  rfl

/-- The endpoint is the Fourier coefficient of the existing L2 trace. -/
theorem diskMode_one (u : ComplexH1) (n : ℤ) :
    diskMode u n 1 = circleFourierCoeff (diskTraceCLM u) n := by
  rw [diskMode, circleCoefficientCLM_apply]
  rfl

theorem diskRadialMode_intervalIntegrable (u : ComplexH1) (n : ℤ) :
    IntervalIntegrable (diskRadialMode u n) volume (1 / 2) 1 :=
  ⟨(circleCoefficientCLM n).integrable_comp (disk_weak_polar u).2.1.1,
    (circleCoefficientCLM n).integrable_comp (disk_weak_polar u).2.1.2⟩

theorem diskRadialMode_sq_integrable (u : ComplexH1) (n : ℤ) :
    IntervalIntegrable (fun r => ‖diskRadialMode u n r‖ ^ 2) volume (1 / 2) 1 := by
  have hi := (diskRadialProfile_sq_integrable u).const_mul (‖circleCoefficientCLM n‖ ^ 2)
  apply hi.mono_fun'
  · have hm := (diskRadialMode_intervalIntegrable u n).def'.aestronglyMeasurable
    exact hm.norm.pow 2
  · filter_upwards [] with r
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := (circleCoefficientCLM n).le_opNorm (diskRadialProfile u r)
    change ‖diskRadialMode u n r‖ ≤ _ at h
    nlinarith [sq_le_sq₀ (norm_nonneg (diskRadialMode u n r))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr h]

/-- The frequency estimate applies to the genuine weak disk modes and existing trace. -/
theorem diskMode_frequency_bound (u : ComplexH1) (n : ℤ) (L : ℝ) (hL : 1 ≤ L) :
    L * ‖circleFourierCoeff (diskTraceCLM u) n‖ ^ 2 ≤
      4 * L ^ 2 * (∫ r in (1 / 2 : ℝ)..1, ‖diskMode u n r‖ ^ 2) +
      ∫ r in (1 / 2 : ℝ)..1, ‖diskRadialMode u n r‖ ^ 2 := by
  have h := endpoint_frequency_estimate L hL (diskMode_continuousOn u n)
    (diskRadialMode_intervalIntegrable u n) (diskRadialMode_sq_integrable u n)
    (fun r hr => diskMode_sub_eq_integral u n hr (by norm_num))
  simpa only [diskMode_one] using h

end KsIndex.Trace
