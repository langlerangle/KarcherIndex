module

public import KsIndexLean.CircleParseval
public import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreservingEquiv
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

@[expose] public section


/-! # Fourier equivalence for circle arclength measure

The angular homeomorphism preserves measures of total mass `2π`. Passing from
angular volume to probability Haar measure preserves function values almost
everywhere and changes the `L²` norm by `√((2π)⁻¹)`.

`circleFourierCLE` returns the normalized Fourier coefficients without rescaling
them. It is a continuous linear equivalence, with norm factor `√((2π)⁻¹)`
and inner-product factor `(2π)⁻¹`. Its inverse realizes every square-summable
coefficient sequence as a circle `L²` class.
-/
noncomputable section
open MeasureTheory Set
open scoped Real
namespace KsIndex.Trace

local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- The angular homeomorphism from the additive circle to the unit-circle subtype. -/
def fourierCircleHomeomorph : AddCircle (2 * π) ≃ₜ Circle₁ :=
  AddCircle.homeomorphCircle'

@[simp] theorem fourierCircleHomeomorph_coe (θ : ℝ) :
    fourierCircleHomeomorph (θ : AddCircle (2 * π)) = circleParam θ := by
  apply Subtype.ext
  change (Circle.exp θ : ℂ) = (circleParam θ : ℂ)
  simp only [Circle.coe_exp, circleParam_coe]

/-- No renormalization: additive-circle volume transports to geometric arclength. -/
theorem measurePreserving_fourierCircleHomeomorph :
    MeasurePreserving fourierCircleHomeomorph volume circleMeasure := by
  refine ⟨fourierCircleHomeomorph.continuous.measurable, ?_⟩
  have hm := (AddCircle.measurePreserving_mk (2 * π) 0).map_eq
  simp only [zero_add] at hm
  rw [← hm, Measure.map_map fourierCircleHomeomorph.continuous.measurable
    (AddCircle.measurePreserving_mk (2 * π) 0).measurable]
  have he : fourierCircleHomeomorph ∘ (fun θ : ℝ => (θ : AddCircle (2 * π))) =
      circleParam := by funext θ; exact fourierCircleHomeomorph_coe θ
  rw [he, circleMeasure, restrict_Ico_eq_restrict_Ioc]

theorem measurePreserving_fourierCircleHomeomorph_symm :
    MeasurePreserving fourierCircleHomeomorph.symm circleMeasure volume :=
  MeasurePreserving.symm fourierCircleHomeomorph.toMeasurableEquiv
    measurePreserving_fourierCircleHomeomorph

/-- Isometric transport of the actual geometric L² space to angular volume L². -/
def circleL2Equiv : Lp ℂ 2 circleMeasure ≃ₗᵢ[ℂ]
    Lp ℂ 2 (volume : Measure (AddCircle (2 * π))) :=
  Lp.compMeasurePreservingₗᵢEquiv ℂ measurePreserving_fourierCircleHomeomorph
    measurePreserving_fourierCircleHomeomorph_symm
    (Filter.Eventually.of_forall (fun w => fourierCircleHomeomorph.apply_symm_apply w))

theorem circleL2Equiv_norm (u : Lp ℂ 2 circleMeasure) : ‖circleL2Equiv u‖ = ‖u‖ :=
  circleL2Equiv.norm_map u

abbrev AngularL2 := Lp ℂ 2 (volume : Measure (AddCircle (2 * π)))
abbrev HaarL2 := Lp ℂ 2 (AddCircle.haarAddCircle (T := 2 * π))

lemma angular_ae_eq_haar :
    ae (volume : Measure (AddCircle (2 * π))) = ae AddCircle.haarAddCircle := by
  rw [AddCircle.volume_eq_smul_haarAddCircle,
    Measure.ae_ennreal_smul_measure_eq (by positivity)]

/-- Change the measure normalization while preserving function values almost everywhere. -/
def angularToHaar (u : AngularL2) : HaarL2 :=
  (memLp_haarAddCircle_iff.mpr (Lp.memLp u)).toLp u

def haarToAngular (u : HaarL2) : AngularL2 :=
  (memLp_haarAddCircle_iff.mp (Lp.memLp u)).toLp u

lemma angularToHaar_ae (u : AngularL2) :
    angularToHaar u =ᵐ[AddCircle.haarAddCircle] u := MemLp.coeFn_toLp _

lemma haarToAngular_ae (u : HaarL2) :
    haarToAngular u =ᵐ[volume] u := MemLp.coeFn_toLp _

/-- Normalization changes the norm, but preserves the complex vector space. -/
def angularHaarEquiv : AngularL2 ≃ₗ[ℂ] HaarL2 where
  toFun := angularToHaar
  invFun := haarToAngular
  left_inv u := by
    apply Lp.ext
    have h := angularToHaar_ae u
    rw [← angular_ae_eq_haar] at h
    exact (haarToAngular_ae _).trans h
  right_inv u := by
    apply Lp.ext
    have h := haarToAngular_ae u
    rw [angular_ae_eq_haar] at h
    exact (angularToHaar_ae _).trans h
  map_add' u v := by
    apply Lp.ext
    have h := Lp.coeFn_add u v
    rw [angular_ae_eq_haar] at h
    filter_upwards [angularToHaar_ae (u + v), h,
      Lp.coeFn_add (angularToHaar u) (angularToHaar v),
      angularToHaar_ae u, angularToHaar_ae v] with x h1 h2 h3 h4 h5
    simp only [Pi.add_apply] at *
    rw [h1, h2, h3, h4, h5]
  map_smul' c u := by
    apply Lp.ext
    have h := Lp.coeFn_smul c u
    rw [angular_ae_eq_haar] at h
    filter_upwards [angularToHaar_ae (c • u), h,
      Lp.coeFn_smul c (angularToHaar u), angularToHaar_ae u] with x h1 h2 h3 h4
    simp only [Pi.smul_apply, RingHom.id_apply] at *
    rw [h1, h2, h3, h4]

/-- The Fourier equivalence of the actual geometric L² space with coefficient ℓ².
Norm normalization is recorded separately; this map does not rescale coefficients. -/
def circleFourierEquiv : Lp ℂ 2 circleMeasure ≃ₗ[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  circleL2Equiv.toLinearEquiv.trans
    (angularHaarEquiv.trans (fourierBasis (T := 2 * π)).repr.toLinearEquiv)

lemma circleL2Equiv_ae (u : Lp ℂ 2 circleMeasure) :
    circleL2Equiv u =ᵐ[volume] (fun x => u (fourierCircleHomeomorph x)) :=
  Lp.coeFn_compMeasurePreservingₗᵢEquiv ℂ _ _ _ u

/-- The equivalence yields exactly the coefficients in geometric-circle Parseval. -/
theorem circleFourierEquiv_apply (u : Lp ℂ 2 circleMeasure) (n : ℤ) :
    circleFourierEquiv u n = circleFourierCoeff u n := by
  have h := circleL2Equiv_ae u
  rw [angular_ae_eq_haar] at h
  have hc := (angularToHaar_ae (circleL2Equiv u)).trans h
  change (fourierBasis (T := 2 * π)).repr (angularToHaar (circleL2Equiv u)) n = _
  rw [fourierBasis_repr, congrFun (fourierCoeff_congr_ae hc) n]
  rw [fourierCoeff_eq_intervalIntegral _ _ 0, circleFourierCoeff,
    fourierCoeffOn_eq_integral]
  simp only [zero_add, sub_zero, fourierCircleHomeomorph_coe]
  simp only [fourier_coe_apply, sub_zero]

lemma integral_sq_norm_circleL2 (u : Lp ℂ 2 circleMeasure) :
    ∫ w, ‖u w‖ ^ 2 ∂circleMeasure = ‖u‖ ^ 2 := by
  have h := congrArg (RCLike.re : ℂ → ℝ) (L2.inner_def u u)
  rw [← integral_re] at h
  · simpa only [inner_self_eq_norm_sq] using h.symm
  · exact L2.integrable_inner u u

/-- Parseval gives the exact norm change, including the arclength factor. -/
theorem circleFourierEquiv_norm_sq (u : Lp ℂ 2 circleMeasure) :
    ‖circleFourierEquiv u‖ ^ 2 = (2 * π)⁻¹ * ‖u‖ ^ 2 := by
  have h := lp.hasSum_norm (show (0 : ℝ) < (2 : ENNReal).toReal by norm_num)
    (circleFourierEquiv u)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, circleFourierEquiv_apply] at h
  rw [← h.tsum_eq, tsum_sq_circleFourierCoeff (Lp.memLp u), integral_sq_norm_circleL2]

theorem circleFourierEquiv_norm (u : Lp ℂ 2 circleMeasure) :
    ‖circleFourierEquiv u‖ = Real.sqrt ((2 * π)⁻¹) * ‖u‖ := by
  calc
    ‖circleFourierEquiv u‖ = Real.sqrt (‖circleFourierEquiv u‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt ((2 * π)⁻¹ * ‖u‖ ^ 2) := by rw [circleFourierEquiv_norm_sq]
    _ = Real.sqrt ((2 * π)⁻¹) * ‖u‖ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg u)]

/-- Fourier expansion is a bounded equivalence for the actual circle measure. -/
def circleFourierCLE : Lp ℂ 2 circleMeasure ≃L[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  ContinuousLinearEquiv.ofHomothety circleFourierEquiv
    (Real.sqrt ((2 * π)⁻¹)) (by positivity) circleFourierEquiv_norm

@[simp] theorem circleFourierCLE_apply (u : Lp ℂ 2 circleMeasure) (n : ℤ) :
    circleFourierCLE u n = circleFourierCoeff u n := circleFourierEquiv_apply u n

/-- Every ℓ² sequence is realized with exactly its prescribed Fourier coefficients. -/
theorem circleFourierCoeff_inverse (a : lp (fun _ : ℤ => ℂ) 2) (n : ℤ) :
    circleFourierCoeff (circleFourierCLE.symm a) n = a n := by
  rw [← circleFourierCLE_apply, circleFourierCLE.apply_symm_apply]

lemma inner_angularToHaar (u v : AngularL2) :
    inner ℂ (angularToHaar u) (angularToHaar v) =
      ((2 * π)⁻¹ : ℝ) • inner ℂ u v := by
  rw [L2.inner_def]
  have he : (∫ x, inner ℂ (angularToHaar u x) (angularToHaar v x)
      ∂AddCircle.haarAddCircle) =
      ∫ x, inner ℂ (u x) (v x) ∂AddCircle.haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [angularToHaar_ae u, angularToHaar_ae v] with x hu hv
    rw [hu, hv]
  rw [he, AddCircle.integral_haarAddCircle, L2.inner_def]

/-- Polarized Parseval, with the actual arclength normalization. -/
theorem circleFourierCLE_inner (u v : Lp ℂ 2 circleMeasure) :
    inner ℂ (circleFourierCLE u) (circleFourierCLE v) =
      ((2 * π)⁻¹ : ℝ) • inner ℂ u v := by
  change inner ℂ ((fourierBasis (T := 2 * π)).repr (angularToHaar (circleL2Equiv u)))
    ((fourierBasis (T := 2 * π)).repr (angularToHaar (circleL2Equiv v))) = _
  rw [LinearIsometryEquiv.inner_map_map, inner_angularToHaar,
    LinearIsometryEquiv.inner_map_map]

end KsIndex.Trace
