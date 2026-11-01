module

public import KsIndexLean.FourierEnergyBounds
public import KsIndexLean.CircleSobolevL2

@[expose] public section


/-! Summability of the half-order Fourier coefficients of the weak trace. -/
noncomputable section
open MeasureTheory Set
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma diskRadialMode_integral_finite_sq_le (u : ComplexH1) (F : Finset ℤ) :
    (∑ n ∈ F, ∫ r in (1 / 2 : ℝ)..1, ‖diskRadialMode u n r‖ ^ 2) ≤
      (2 * Real.pi)⁻¹ * ∫ r in (1 / 2 : ℝ)..1, ‖diskRadialProfile u r‖ ^ 2 := by
  rw [← intervalIntegral.integral_finsetSum (fun n _ => diskRadialMode_sq_integrable u n),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by norm_num : (1 / 2 : ℝ) ≤ 1)
  · have he : (∑ n ∈ F, fun r : ℝ => ‖diskRadialMode u n r‖ ^ 2) =
        (fun r => ∑ n ∈ F, ‖diskRadialMode u n r‖ ^ 2) := by
      funext r; simp only [Finset.sum_apply]
    rw [← he]
    exact IntervalIntegrable.sum F (fun n _ => diskRadialMode_sq_integrable u n)
  · exact (diskRadialProfile_sq_integrable u).const_mul _
  · intro r _
    simpa only [diskRadialMode, circleCoefficientCLM_apply] using
      circleFourier_finite_sq_le (diskRadialProfile u r) F

/-- A collar-energy bound independent of the finite set of boundary modes. -/
theorem diskTrace_finite_half_weight_le (u : ComplexH1) (F : Finset ℤ) :
    (∑ n ∈ F, (1 + |(n : ℝ)|) * ‖circleFourierCoeff (diskTraceCLM u) n‖ ^ 2) ≤
      8 * (2 * Real.pi)⁻¹ *
        ((∫ r in (1 / 2 : ℝ)..1, ‖diskProfile u r‖ ^ 2) +
         ∫ r in (1 / 2 : ℝ)..1, ‖diskAngularProfile u r‖ ^ 2) +
      (2 * Real.pi)⁻¹ * ∫ r in (1 / 2 : ℝ)..1, ‖diskRadialProfile u r‖ ^ 2 := by
  have hs := Finset.sum_le_sum (fun n (_ : n ∈ F) =>
    diskMode_frequency_bound u n (1 + |(n : ℝ)|) (by linarith [abs_nonneg (n : ℝ)]))
  have he : (∑ n ∈ F, 4 * (1 + |(n : ℝ)|) ^ 2 *
      (∫ r in (1 / 2 : ℝ)..1, ‖diskMode u n r‖ ^ 2)) =
      4 * ∫ r in (1 / 2 : ℝ)..1, ∑ n ∈ F,
        (1 + |(n : ℝ)|) ^ 2 * ‖diskMode u n r‖ ^ 2 := by
    rw [intervalIntegral.integral_finsetSum
      (fun n _ => (diskMode_sq_integrable u n).const_mul _), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [intervalIntegral.integral_const_mul]
    ring
  rw [Finset.sum_add_distrib, he] at hs
  have hv := diskMode_integral_finite_weight_sq_le u F
  have hr := diskRadialMode_integral_finite_sq_le u F
  linarith

/-- The L² trace has half-order Fourier regularity. -/
theorem diskTrace_half_weight_summable (u : ComplexH1) :
    Summable (fun n : ℤ => (1 + |(n : ℝ)|) * ‖circleFourierCoeff (diskTraceCLM u) n‖ ^ 2) :=
  summable_of_sum_le (fun n => by positivity) (diskTrace_finite_half_weight_le u)

/-- The trace has a unique half-order Sobolev representative on the same circle. -/
theorem diskTrace_exists_unique_half (u : ComplexH1) :
    ∃! v : KsIndex.CircleSobolev.Space (1 / 2 : ℝ),
      KsIndex.CircleSobolev.toL2 (show (0 : ℝ) ≤ 1 / 2 by norm_num) v = diskTraceCLM u := by
  have hs : diskTraceCLM u ∈ Set.range
      (KsIndex.CircleSobolev.toL2 (show (0 : ℝ) ≤ 1 / 2 by norm_num)) := by
    rw [KsIndex.CircleSobolev.mem_range_toL2_iff]
    simpa only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one]
      using diskTrace_half_weight_summable u
  obtain ⟨v, hv⟩ := hs
  refine ⟨v, hv, ?_⟩
  intro w hw
  exact KsIndex.CircleSobolev.toL2_injective (by norm_num) (hw.trans hv.symm)

end KsIndex.Trace
