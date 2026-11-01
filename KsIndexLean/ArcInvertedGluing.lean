module

public import KsIndexLean.ArcRadialGluing
public import KsIndexLean.InvertedRadialProfile

@[expose] public section


open Set MeasureTheory TauCeti

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- The right radial profile uses actual inversion of the second disk's a.e. profile. -/
def arcInvertedProfile (A : Set Circle₁) (u : ComplexH1) :
    ℝ → Lp ℂ 2 (circleMeasure.restrict A) := fun r => arcProfile A u r⁻¹

lemma arcInvertedProfile_weak (A : Set Circle₁) (u : ComplexH1) :
    HasWeakLineDerivOn volume (intervalOpens 1 2) (arcInvertedProfile A u)
      (invertedRadialDeriv (arcRadialProfile A u)) 1 :=
  invertedProfile_weak (arcProfile_weak A u) (arcRadialProfile_integrable A u)

lemma arcInvertedProfile_endpoint (A : Set Circle₁) (u : ComplexH1) :
    representative (by norm_num : (1 : ℝ) < 2) (arcInvertedProfile A u)
      (invertedRadialDeriv (arcRadialProfile A u)) 1 = arcTrace A u := by
  exact (invertedProfile_endpoint (arcProfile_weak A u)
    (arcRadialProfile_integrable A u)).trans (arcProfile_endpoint A u)

/-- Radial gluing of a disk profile and an inverted disk profile is equivalent to trace matching. -/
theorem arcInverted_gluing_iff (A : Set Circle₁) (u v : ComplexH1) :
    HasWeakLineDerivOn volume (intervalOpens (1 / 2) 2)
      (joinAt 1 (arcProfile A u) (arcInvertedProfile A v))
      (joinAt 1 (arcRadialProfile A u) (invertedRadialDeriv (arcRadialProfile A v))) 1 ↔
      arcTrace A u = arcTrace A v := by
  rw [arcProfile_gluing_iff A u (by norm_num) (arcInvertedProfile_weak A v)
    (invertedRadialDeriv_integrable (arcRadialProfile_integrable A v)),
    arcInvertedProfile_endpoint]

/-- Any constant complex scalar is allowed, including zero; no division by the scalar is needed. -/
theorem arcInverted_phase_gluing_iff (A : Set Circle₁) (u v : ComplexH1) (c : ℂ) :
    HasWeakLineDerivOn volume (intervalOpens (1 / 2) 2)
      (joinAt 1 (arcProfile A u) (c • arcInvertedProfile A v))
      (joinAt 1 (arcRadialProfile A u)
        (c • invertedRadialDeriv (arcRadialProfile A v))) 1 ↔
      arcTrace A u = c • arcTrace A v := by
  have hv := arcInvertedProfile_weak A v
  have hg := invertedRadialDeriv_integrable (arcRadialProfile_integrable A v)
  rw [arcProfile_gluing_iff A u (by norm_num) (weak_deriv_const_smul_complex c hv)
    (hg.smul c)]
  have he := representative_smul_complex (by norm_num : (1 : ℝ) < 2) c hv hg
    (by norm_num : (1 : ℝ) ∈ Icc 1 2)
  rw [he, Pi.smul_apply, arcInvertedProfile_endpoint]

end KsIndex.Trace
