module

public import KsIndexLean.AlphaLowModeCache

@[expose] public section


/-! Reusable analytic consumer for independently checked sample-cache blocks. -/
namespace KsIndex.AlphaRemarkTrial
open CertifiedApproximation

def blockLinearNumerator {L : ℕ} (base n : ℤ) (a : Fin L → ℤ) : ℤ :=
  ∑ i : Fin L, (rationalKernelWeight n (base+i.val)).num * a i /
    ((rationalKernelWeight n (base+i.val)).den : ℤ)

def blockLinearRadius {L : ℕ} (base n : ℤ) (e : Fin L → ℤ) : ℤ :=
  ∑ i : Fin L, (|(rationalKernelWeight n (base+i.val)).num| * e i /
    ((rationalKernelWeight n (base+i.val)).den : ℤ) + 2)

/-- A checked cache block encloses its actual analytic linear sum. -/
theorem actual_cached_block_bound {N L : ℕ} {t : CoefficientTable}
    (ht : ValidCoefficientTable N t) (base n : ℤ) (a e : Fin L → ℤ)
    (hc : ∀ i : Fin L, SampleCovered N (2*(base+i.val)+1))
    (ha : ∀ i : Fin L, a i = tableSampleNumerator t (2*(base+i.val)+1))
    (he : ∀ i : Fin L, e i = tableSampleRadius t (2*(base+i.val)+1)) :
    |(∑ i : Fin L, (rationalKernelWeight n (base+i.val) : ℝ) *
        sample (2*(base+i.val)+1)) - (blockLinearNumerator base n a : ℝ)/10^51| ≤
      (blockLinearRadius base n e : ℝ)/10^51 := by
  have hs (i : Fin L) : |sample (2*(base+i.val)+1) - (a i : ℝ)/10^51| ≤
      (e i : ℝ)/10^51 := by
    rw [ha i, he i, tableSampleNumerator_eq ht (hc i), tableSampleRadius_eq ht (hc i)]
    exact integer_sample_certificate _
  have h := finite_integer_linear_error (Finset.univ : Finset (Fin L))
    (fun i => sample (2*(base+i.val)+1))
    (fun i => (rationalKernelWeight n (base+i.val)).num)
    (fun i => ((rationalKernelWeight n (base+i.val)).den : ℤ)) a e
    (by norm_num : (0 : ℤ) < 10^51)
    (by intro i _; exact_mod_cast (rationalKernelWeight n (base+i.val)).den_pos)
    (by intro i _; simpa only [Int.cast_pow, Int.cast_ofNat] using hs i)
  simpa only [Int.cast_natCast, Int.cast_pow, Int.cast_ofNat, ← Rat.cast_def,
    blockLinearNumerator, blockLinearRadius] using h

/-- Every entry of a block contained in the full direct window has coefficient coverage. -/
theorem low_block_covered (start L : ℕ) (h : start+L ≤ 32770) (i : Fin L) :
    SampleCovered 16389 (2*((-16385 : ℤ)+start+i.val)+1) := by
  apply low_window_covered 16385 16389 (by norm_num)
  simp only [Finset.mem_Ico]
  have hi := i.isLt
  omega

end KsIndex.AlphaRemarkTrial
