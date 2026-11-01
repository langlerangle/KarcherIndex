module

public import KsIndexLean.CircleFourierTransport
public import KsIndexLean.SlitSeamGauges
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section


/-! The geometric power cover preserves the actual arclength measure.
This supplies representative-safe pullback for the single-arc reduction. -/
noncomputable section
open MeasureTheory Set
open scoped Real
namespace KsIndex.Trace
local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

def circlePower (k : ℕ) (w : Circle₁) : Circle₁ :=
  ⟨(w : ℂ)^k, by
    have hw : ‖(w : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
    simp [norm_pow, hw]⟩

lemma continuous_circlePower (k : ℕ) : Continuous (circlePower k) :=
  (continuous_subtype_val.pow k).subtype_mk _

lemma circlePower_circleParam (k : ℕ) (θ : ℝ) :
    circlePower k (circleParam θ) = circleParam ((k : ℝ) * θ) := by
  apply Subtype.ext
  change (circleParam θ : ℂ)^k = (circleParam ((k : ℝ)*θ) : ℂ)
  rw [circleParam_coe, circleParam_coe, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma circlePower_angular (k : ℕ) (x : AddCircle (2 * π)) :
    circlePower k (fourierCircleHomeomorph x) =
      fourierCircleHomeomorph ((k : ℤ) • x) := by
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [fourierCircleHomeomorph_coe, circlePower_circleParam]
  have he : (k : ℤ) • (θ : AddCircle (2 * π)) =
      (((k : ℝ) * θ : ℝ) : AddCircle (2 * π)) := by
    simp
  rw [he, fourierCircleHomeomorph_coe]

theorem measurePreserving_circlePower {k : ℕ} (hk : 0 < k) :
    MeasurePreserving (circlePower k) circleMeasure circleMeasure := by
  have hm : MeasurePreserving (fun x : AddCircle (2 * π) => (k : ℤ) • x)
      volume volume := Measure.measurePreserving_zsmul volume (by exact_mod_cast hk.ne')
  have h := measurePreserving_fourierCircleHomeomorph.comp
    (hm.comp measurePreserving_fourierCircleHomeomorph_symm)
  have he : fourierCircleHomeomorph ∘
      ((fun x : AddCircle (2 * π) => (k : ℤ) • x) ∘ fourierCircleHomeomorph.symm) =
      circlePower k := by
    funext w
    simp only [Function.comp_apply, ← circlePower_angular,
      fourierCircleHomeomorph.apply_symm_apply]
  rwa [he] at h

lemma circlePower_preimage_arc (k p : ℕ) :
    circlePower k ⁻¹' boundaryArc 1 p = boundaryArc k p := by
  ext w
  have hw : ‖(w : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
  simp [boundaryArc, KsIndex.Surface.arc, circlePower]

/-- The covering also preserves the measures restricted to corresponding arcs. -/
lemma measurePreserving_circlePower_arc {k : ℕ} (hk : 0 < k) (p : ℕ) :
    MeasurePreserving (circlePower k) (circleMeasure.restrict (boundaryArc k p))
      (circleMeasure.restrict (boundaryArc 1 p)) := by
  have h := (measurePreserving_circlePower hk).restrict_preimage
    (isOpen_boundaryArc 1 p).measurableSet
  rwa [circlePower_preimage_arc] at h

/-- Both directions of a.e. arc vanishing, with measurability explicit. -/
theorem circlePower_arc_zero_iff {k : ℕ} (hk : 0 < k) (p : ℕ)
    {g : Circle₁ → ℂ} (hg : Measurable g) :
    (∀ᵐ w ∂circleMeasure.restrict (boundaryArc k p), g (circlePower k w) = 0) ↔
    (∀ᵐ w ∂circleMeasure.restrict (boundaryArc 1 p), g w = 0) := by
  have hm := measurePreserving_circlePower_arc hk p
  rw [← hm.map_eq]
  exact (ae_map_iff hm.measurable.aemeasurable (hg (measurableSet_singleton 0))).symm

/-- The unit-modulus phase does not change arc vanishing. -/
theorem phased_circlePower_arc_zero_iff {k : ℕ} (hk : 0 < k) (c p : ℕ)
    {g : Circle₁ → ℂ} (hg : Measurable g) :
    (∀ᵐ (w : Circle₁) ∂circleMeasure.restrict (boundaryArc k p),
      (w : ℂ)^c * g (circlePower k w) = 0) ↔
    (∀ᵐ w ∂circleMeasure.restrict (boundaryArc 1 p), g w = 0) := by
  have he (w : Circle₁) : (w : ℂ)^c * g (circlePower k w) = 0 ↔
      g (circlePower k w) = 0 := by
    have hw : (w : ℂ) ≠ 0 := by
      intro h
      have hn := mem_sphere_zero_iff_norm.mp w.property
      rw [h, norm_zero] at hn
      exact zero_ne_one hn
    simp [hw]
  simp only [he]
  exact circlePower_arc_zero_iff hk p hg

end KsIndex.Trace
