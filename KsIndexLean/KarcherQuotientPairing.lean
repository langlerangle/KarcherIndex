module

public import KsIndexLean.KarcherDensityIntegral

@[expose] public section


/-! Complex Jacobi integration on the actual quotient, conjugate-linear in
its first slot, with the weighted paper pairing and integrability identified. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData
open scoped QuotientArea
namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)
  (G H : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)

/-- The weighted complex Jacobi density in an ordered disk coordinate. -/
def copyJacobiDensity (n : ZMod (2*m)) (z : ℂ) : ℂ :=
  ((Surface.rho k z ^ 2)⁻¹ : ℝ) •
    GradOrtho.gradInner (encodeDiskFunction (R.diskFunctionPullback G) n)
      (encodeDiskFunction (R.diskFunctionPullback H) n) z -
  (Surface.absA k z ^ 2 : ℝ) •
    ((starRingEnd ℂ) (encodeDiskFunction (R.diskFunctionPullback G) n z) *
      encodeDiskFunction (R.diskFunctionPullback H) n z)

/-- Complex density on the quotient, with null seams assigned zero. -/
def quotientJacobiDensity := R.assembleCopyDensity (R.copyJacobiDensity G H)

/-- The complex Jacobi pairing integrated against quotient area. -/
def quotientJacobiB : ℂ := ∫ x, R.quotientJacobiDensity G H x ∂(R.quotientArea)

lemma measurable_copyJacobiDensity (hG : Continuous G) (hH : Continuous H) (n : ZMod (2*m)) :
    Measurable (R.copyJacobiDensity G H n) := by
  unfold copyJacobiDensity
  exact (((measurable_rho k).pow_const 2).inv.smul (SurfaceForm.measurable_gradInner _ _)).sub
    (((measurable_absA k).pow_const 2).smul
      (((Complex.continuous_conj.measurable.comp (R.measurable_encoding G hG n))).mul
        (R.measurable_encoding H hH n)))

lemma copyJacobiDensity_exterior (n : ZMod (2*m)) (z : ℂ) (hz : 1 < ‖z‖) :
    R.copyJacobiDensity G H n z = 0 := by
  simp [copyJacobiDensity, GradOrtho.gradInner, encodeDiskFunction_exterior _ n z hz,
    fderiv_eq_zero_of_exterior _ (encodeDiskFunction_exterior _ n) hz]

lemma compactSmooth_quotientJacobiDensity_integrable :
    letI := HeightLift.periodChartedSpace R.hC m
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G → HasCompactSupport G →
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ H → HasCompactSupport H →
    Integrable (R.quotientJacobiDensity G H) R.quotientArea := by
  let := HeightLift.periodChartedSpace R.hC m
  intro hg hgc hh hhc
  apply (R.integrable_assembleCopyDensity_iff _
    (R.measurable_copyJacobiDensity G H hg.continuous hh.continuous)).mpr
  intro n
  have hi := R.compactSmooth_pairing_integrable G H hg hgc hh hhc n
  exact (hi.1.sub hi.2).integrableOn

lemma compactSmooth_quotientJacobiB_eq_copywise :
    letI := HeightLift.periodChartedSpace R.hC m
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G → HasCompactSupport G →
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ H → HasCompactSupport H →
    R.quotientJacobiB G H = ewJacobiB R G H := by
  let := HeightLift.periodChartedSpace R.hC m
  intro hg hgc hh hhc
  have hu := (R.compactSmooth_iff_encoding_mem_CcSmooth G).mp ⟨hg,hgc⟩
  have hv := (R.compactSmooth_iff_encoding_mem_CcSmooth H).mp ⟨hh,hhc⟩
  rw [quotientJacobiB, quotientJacobiDensity,
    R.integral_assembleCopyDensity _ (R.measurable_copyJacobiDensity G H hg.continuous hh.continuous)
      (fun n => ((R.encoding_pairing_integrable G H hu hv n).1.sub
        (R.encoding_pairing_integrable G H hu hv n).2).integrableOn),
    R.ewJacobiB_eq_integral G H hu hv]
  apply Finset.sum_congr rfl
  intro n _
  exact (integral_ew_eq_disk_of_exterior k (R.copyJacobiDensity G H n)
    (R.copyJacobiDensity_exterior G H n)).symm

lemma compactSmooth_quotientJacobiB_eq_model :
    letI := HeightLift.periodChartedSpace R.hC m
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G → HasCompactSupport G →
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ H → HasCompactSupport H →
    R.quotientJacobiB G H = SurfaceForm.jacobiB k m
      (encodeDiskFunction (R.diskFunctionPullback G))
      (encodeDiskFunction (R.diskFunctionPullback H)) := by
  let := HeightLift.periodChartedSpace R.hC m
  intro hg hgc hh hhc
  rw [R.compactSmooth_quotientJacobiB_eq_copywise G H hg hgc hh hhc, R.ewJacobiB_eq_model]

lemma compactSmooth_quotientJacobiB_self :
    letI := HeightLift.periodChartedSpace R.hC m
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G → HasCompactSupport G →
    R.quotientJacobiB G G = (R.quotientJacobiQ G : ℂ) := by
  let := HeightLift.periodChartedSpace R.hC m
  intro hg hc
  rw [R.compactSmooth_quotientJacobiB_eq_model G G hg hc hg hc, SurfaceForm.jacobiB_self h.out,
    R.compactSmooth_quotientJacobiQ_eq_model G hg hc]

end PaperHalfPeriodRealization
end KsIndex.KarcherData
