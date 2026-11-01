module

public import KsIndexLean.JacobiBoundaryData
public import KsIndexLean.JacobiFieldsSym
public import KsIndexLean.NaturalCoreH1
public import KsIndexLean.DiskTraceAgreement
public import KsIndexLean.WeakTransmissionDomains

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.JacobiFields

/-- A globally smooth function has finite value and derivative L2 norms on the
bounded disk. The weak encoding retains the actual function and derivatives. -/
def globalSmoothData (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) : SmoothH1Data where
  F := f
  smooth := hf.contDiffOn
  value_mem := continuous_memLp_disk hf.continuous
  dx_mem := continuous_memLp_disk
    ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
  dy_mem := continuous_memLp_disk
    ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)

def globalSmoothH1 (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) : ComplexH1 :=
  smoothToH1 (globalSmoothData f hf)

lemma globalSmoothH1_value (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) :
    valueCLM (globalSmoothH1 f hf) =ᵐ[volume.restrict (disk : Set ℂ)] f :=
  smoothToH1_value_ae _

lemma globalSmoothH1_trace (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) :
    (diskTraceCLM (globalSmoothH1 f hf) : Circle₁ → ℂ) =ᵐ[circleMeasure]
      (fun w => f (w : ℂ)) :=
  diskTrace_smooth_agreement _ hf.continuous.continuousOn

def verticalThreeH1 : ComplexH1 := globalSmoothH1 (nu3 3) (nu3_contDiff 3 (by decide))

def horizontalThreeH1 : ComplexH1 := globalSmoothH1
  (fun w => nu1 3 w + Complex.I * nu2 3 w)
  ((nu1_contDiff 3 (by decide)).add (contDiff_const.mul (nu2_contDiff 3 (by decide))))

lemma verticalThreeH1_value :
    valueCLM verticalThreeH1 =ᵐ[volume.restrict (disk : Set ℂ)] nu3 3 :=
  globalSmoothH1_value _ _

lemma verticalThreeH1_trace : diskTraceCLM verticalThreeH1 = 0 := by
  apply Lp.ext
  filter_upwards [globalSmoothH1_trace (nu3 3) (nu3_contDiff 3 (by decide)),
    Lp.coeFn_zero (E := ℂ) (p := (2 : ENNReal)) (μ := circleMeasure)] with w hw hz
  rw [hz]
  exact hw.trans (nu3_three_boundary (by simpa [Metric.mem_sphere, dist_zero_right] using w.property))

lemma horizontalThreeH1_trace :
    (diskTraceCLM horizontalThreeH1 : Circle₁ → ℂ) =ᵐ[circleMeasure]
      (fun w => (w : ℂ) ^ 2) := by
  filter_upwards [globalSmoothH1_trace
    (fun w => nu1 3 w + Complex.I * nu2 3 w)
    ((nu1_contDiff 3 (by decide)).add (contDiff_const.mul (nu2_contDiff 3 (by decide))))] with w hw
  exact hw.trans (horizontal_three_boundary
    (by simpa [Metric.mem_sphere, dist_zero_right] using w.property))

lemma horizontalThreeH1_trace_ne_zero_ae :
    ∀ᵐ w ∂circleMeasure, (diskTraceCLM horizontalThreeH1 : Circle₁ → ℂ) w ≠ 0 := by
  filter_upwards [horizontalThreeH1_trace] with w hw
  rw [hw]
  apply pow_ne_zero
  have hn : ‖(w : ℂ)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using w.property
  intro hz
  simp [hz] at hn


lemma globalSmoothH1_dx (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) :
    dxCLM (globalSmoothH1 f hf) =ᵐ[volume.restrict (disk : Set ℂ)]
      (fun w => fderiv ℝ f w 1) := smoothToH1_dx_ae _

lemma globalSmoothH1_dy (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) :
    dyCLM (globalSmoothH1 f hf) =ᵐ[volume.restrict (disk : Set ℂ)]
      (fun w => fderiv ℝ f w Complex.I) := smoothToH1_dy_ae _

lemma verticalThreeH1_zeroTrace (A : Set Circle₁) :
    verticalThreeH1 ∈ zeroTraceDomain A := by
  change boundaryRestrictCLM A (diskTraceCLM verticalThreeH1) = 0
  rw [verticalThreeH1_trace, map_zero]

/-- The vertical field's opposite-sign hemisphere pair satisfies every value
phase condition. Thus its exclusion from a nontrivial-phase weak kernel must
use the weak equation (normal flux), not value-domain membership alone. -/
lemma verticalThreeH1_pair_all_value_phases (phase : ℂ) :
    (verticalThreeH1, -verticalThreeH1) ∈ slitTraceDomain 3 phase := by
  constructor <;> apply mem_transmission_of_zero
  · exact verticalThreeH1_zeroTrace _
  · exact (zeroTraceDomain _).neg_mem (verticalThreeH1_zeroTrace _)
  · exact verticalThreeH1_zeroTrace _
  · exact (zeroTraceDomain _).neg_mem (verticalThreeH1_zeroTrace _)

end KsIndex.Trace

