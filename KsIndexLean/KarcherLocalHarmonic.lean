module

public import KsIndexLean.KarcherInfinityIdentification
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

@[expose] public section


/-! Smooth harmonic finite-chart representatives of the actual EW quotient map.
These are analytic ingredients for minimality, not a global surface theorem. -/
noncomputable section
open scoped ContDiff
open InnerProductSpace
namespace KsIndex.KarcherData

/-- The three ambient coordinate functions are harmonic on a neighborhood of
 every point of the specified parameter set. -/
def HarmonicCoordinates (X : ℂ → ℝ × ℝ × ℝ) (U : Set ℂ) : Prop :=
  HarmonicOnNhd (fun z => (X z).1) U ∧
  HarmonicOnNhd (fun z => (X z).2.1) U ∧
  HarmonicOnNhd (fun z => (X z).2.2) U

lemma realPrimitive_smooth_harmonic {U : Set ℂ} (hU : IsOpen U)
    {F₁ F₂ F₃ : ℂ → ℂ} (h₁ : DifferentiableOn ℂ F₁ U)
    (h₂ : DifferentiableOn ℂ F₂ U) (h₃ : DifferentiableOn ℂ F₃ U) :
    ContDiffOn ℝ ∞ (realPrimitive F₁ F₂ F₃) U ∧
    HarmonicCoordinates (realPrimitive F₁ F₂ F₃) U := by
  have hc (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F U) :
      ContDiffOn ℝ ∞ (fun z => (F z).re) U :=
    Complex.reCLM.contDiff.comp_contDiffOn ((hF.contDiffOn hU).restrict_scalars ℝ)
  refine ⟨(hc F₁ h₁).prodMk ((hc F₂ h₂).prodMk (hc F₃ h₃)), ?_⟩
  exact ⟨fun z hz => (h₁.analyticOnNhd hU z hz).harmonicAt_re,
    fun z hz => (h₂.analyticOnNhd hU z hz).harmonicAt_re,
    fun z hz => (h₃.analyticOnNhd hU z hz).harmonicAt_re⟩

/-- The actual quotient integral admits smooth harmonic representatives with
 the prescribed EW differential at every finite non-puncture. -/
theorem exists_smooth_harmonic_local_representative {k : ℕ} (hk : 2 ≤ k)
    (b x : PuncturedPlane k) :
    ∃ r : ℝ, 0 < r ∧ ∃ X : ℂ → ℝ × ℝ × ℝ,
      X x.val = 0 ∧ ContDiffOn ℝ ∞ X (Metric.ball x.val r) ∧
      HarmonicCoordinates X (Metric.ball x.val r) ∧
      (∀ z ∈ Metric.ball x.val r, HasFDerivAt X (ewRealDifferential k z) z) ∧
      (∀ y : PuncturedPlane k, y.val ∈ Metric.ball x.val r →
        descendedIntegral hk b y = descendedIntegral hk b x + projectPeriod (X y.val)) ∧
      Function.Injective (ewRealDifferential k x.val) := by
  obtain ⟨r, hr, F₁, F₂, F₃, hF₁, hF₂, hF₃, hd₁, hd₂, hd₃, hrepr⟩ :=
    exists_local_primitives hk b x
  have hs := realPrimitive_smooth_harmonic Metric.isOpen_ball
    (fun z hz => (hd₁ z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd₂ z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd₃ z hz).differentiableAt.differentiableWithinAt)
  refine ⟨r, hr, realPrimitive F₁ F₂ F₃, ?_, hs.1, hs.2, ?_, hrepr,
    ewRealDifferential_injective hk x.property⟩
  · simp [realPrimitive, hF₁, hF₂, hF₃]
  · intro z hz
    exact hasFDerivAt_realPrimitive (hd₁ z hz) (hd₂ z hz) (hd₃ z hz)

/-- The infinity representative can simultaneously be chosen harmonic and
identified with the actual quotient integral on the full punctured overlap. -/
theorem exists_smooth_harmonic_infinity_chart {k : ℕ} (hk : 2 ≤ k)
    (b : PuncturedPlane k) :
    ∃ r : ℝ, ∃ _hr0 : 0 < r, ∃ hr1 : r < 1,
    ∃ X : ℂ → ℝ × ℝ × ℝ, ∃ C : PeriodTarget,
      X 0 = 0 ∧ ContDiffOn ℝ ∞ X (Metric.ball (0 : ℂ) r) ∧
      HarmonicCoordinates X (Metric.ball (0 : ℂ) r) ∧
      (∀ v ∈ Metric.ball (0 : ℂ) r, HasFDerivAt X (infinityRealDifferential k v) v) ∧
      (∀ v ∈ Metric.ball (0 : ℂ) r, Function.Injective (infinityRealDifferential k v)) ∧
      (∀ v : infinityOverlap r,
        descendedIntegral hk b (infinityOverlapPoint hk hr1.le v) = C + projectPeriod (X v.val)) := by
  obtain ⟨F₁, F₂, F₃, hF₁, hF₂, hF₃, hd₁, hd₂, hd₃⟩ := exists_infinity_primitives hk
  have hs := realPrimitive_smooth_harmonic Metric.isOpen_ball
    (fun z hz => (hd₁ z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd₂ z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd₃ z hz).differentiableAt.differentiableWithinAt)
  let X := realPrimitive F₁ F₂ F₃
  have hsub : Metric.ball (0 : ℂ) (1 / 2 : ℝ) ⊆ Metric.ball (0 : ℂ) 1 :=
    Metric.ball_subset_ball (by norm_num)
  have hder : ∀ v ∈ Metric.ball (0 : ℂ) (1 / 2 : ℝ),
      HasFDerivAt X (infinityRealDifferential k v) v := by
    intro v hv
    exact hasFDerivAt_infinity_realPrimitive (hd₁ v (hsub hv))
      (hd₂ v (hsub hv)) (hd₃ v (hsub hv))
  obtain ⟨C, hC⟩ := infinity_primitive_identification hk b
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) X hder
  refine ⟨1 / 2, by norm_num, by norm_num, X, C, ?_, hs.1.mono hsub,
    ⟨hs.2.1.mono hsub, hs.2.2.1.mono hsub, hs.2.2.2.mono hsub⟩, hder, ?_, hC⟩
  · simp [X, realPrimitive, hF₁, hF₂, hF₃]
  · intro v hv
    exact infinityRealDifferential_injective hk
      (not_puncture_of_norm_lt_one hk (by simpa using hsub hv))

end KsIndex.KarcherData
