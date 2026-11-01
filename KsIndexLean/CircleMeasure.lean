module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

@[expose] public section


/-! # Arclength measure on the unit circle

`circleMeasure` is the pushforward of Lebesgue measure on `[0, 2π)` under
`θ ↦ exp(θ·I)`, with values in the subtype `Metric.sphere (0 : ℂ) 1`.
Its total mass is `2π`.

The module provides change of variables for nonnegative and Bochner integrals,
conversion between half-open set integrals and interval integrals, independence
of the angular window, and invariance under every real rotation.
-/

open MeasureTheory Set Complex
open scoped Real

noncomputable section

namespace KsIndex.Trace

/-- The unit circle as a subtype. -/
abbrev Circle₁ := Metric.sphere (0 : ℂ) 1

/-- The parametrization `θ ↦ e^{iθ}` into the sphere subtype, via `circleMap 0 1`. -/
def circleParam (θ : ℝ) : Circle₁ :=
  ⟨circleMap 0 1 θ, circleMap_mem_sphere (0 : ℂ) zero_le_one θ⟩

@[simp] lemma circleParam_coe (θ : ℝ) :
    (circleParam θ : ℂ) = Complex.exp (θ * Complex.I) := by
  change circleMap 0 1 θ = _
  simp [circleMap]

lemma continuous_circleParam : Continuous circleParam := by
  unfold circleParam
  exact (continuous_circleMap 0 1).subtype_mk _

lemma measurable_circleParam : Measurable circleParam :=
  continuous_circleParam.measurable

lemma circleParam_periodic : Function.Periodic circleParam (2 * π) := by
  intro θ
  apply Subtype.ext
  simpa [circleParam] using periodic_circleMap 0 1 θ

/-- **The boundary measure σ**: pushforward of Lebesgue on `[0, 2π)`. -/
def circleMeasure : Measure Circle₁ :=
  Measure.map circleParam (volume.restrict (Ico 0 (2 * π)))

/-- The arclength measure has total mass `2π`. -/
lemma circleMeasure_univ : circleMeasure Set.univ = ENNReal.ofReal (2 * π) := by
  rw [circleMeasure, Measure.map_apply measurable_circleParam MeasurableSet.univ]
  simp [Real.volume_Ico]

instance isFiniteMeasure_circleMeasure : IsFiniteMeasure circleMeasure :=
  ⟨by rw [circleMeasure_univ]; exact ENNReal.ofReal_lt_top⟩

/-- Change of variables, lintegral form, on the `Ico` window. -/
lemma lintegral_circleMeasure {f : Circle₁ → ENNReal} (hf : Measurable f) :
    ∫⁻ w, f w ∂circleMeasure = ∫⁻ θ in Ico 0 (2 * π), f (circleParam θ) := by
  rw [circleMeasure, lintegral_map hf measurable_circleParam]

/-- Bochner change of variables on the half-open angular window. -/
lemma integral_circleMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Circle₁ → E} (hf : AEStronglyMeasurable f circleMeasure) :
    ∫ w, f w ∂circleMeasure = ∫ θ in Ico 0 (2 * π), f (circleParam θ) :=
  integral_map measurable_circleParam.aemeasurable hf

/-- Endpoint-null conversion: the `Ico` window integral as an interval integral. -/
lemma setIntegral_Ico_eq_intervalIntegral {f : ℝ → ℝ} :
    ∫ θ in Ico 0 (2 * π), f θ = ∫ θ in (0)..(2 * π), f θ := by
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,
    integral_Ico_eq_integral_Ioc]

/-- Bochner change of variables for an integrable function. -/
lemma integral_circleMeasure_of_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : Circle₁ → E} (hf : Integrable f circleMeasure) :
    ∫ w, f w ∂circleMeasure = ∫ θ in Ico 0 (2 * π), f (circleParam θ) :=
  integral_circleMeasure hf.aestronglyMeasurable

/-- Rotation on the circle subtype: multiplication by `e^{iα}`. -/
def circleRotate (α : ℝ) (w : Circle₁) : Circle₁ :=
  ⟨Complex.exp (α * Complex.I) * w, by
    have hw : ‖(w : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
    simp [hw, Complex.norm_exp_ofReal_mul_I α]⟩

lemma continuous_circleRotate (α : ℝ) : Continuous (circleRotate α) :=
  Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) _

lemma circleRotate_circleParam (α θ : ℝ) :
    circleRotate α (circleParam θ) = circleParam (α + θ) := by
  apply Subtype.ext
  simp [circleRotate, circleParam, circleMap, ← Complex.exp_add]
  ring_nf

/-- Translating a restricted Lebesgue window translates the window. -/
lemma map_translate (α x y : ℝ) :
    Measure.map (fun θ => α + θ) (volume.restrict (Ico x y)) =
      volume.restrict (Ico (α + x) (α + y)) := by
  ext s hs
  rw [Measure.map_apply (measurable_const_add α) hs,
    Measure.restrict_apply (hs.preimage (measurable_const_add α)),
    Measure.restrict_apply hs]
  have hpre : (fun θ => α + θ) ⁻¹' (s ∩ Ico (α + x) (α + y)) =
      ((fun θ => α + θ) ⁻¹' s) ∩ Ico x y := by
    ext t
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_Ico]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by linarith, by linarith⟩
  rw [← hpre, measure_preimage_add]

/-- Shifting a window by an integer number of periods does not change the pushforward. -/
lemma map_circleParam_shift (n : ℤ) (x y : ℝ) :
    Measure.map circleParam
        (volume.restrict (Ico ((n : ℝ) * (2 * π) + x) ((n : ℝ) * (2 * π) + y))) =
      Measure.map circleParam (volume.restrict (Ico x y)) := by
  rw [← map_translate, Measure.map_map measurable_circleParam (measurable_const_add _)]
  congr 1
  funext θ
  change circleParam ((n : ℝ) * (2 * π) + θ) = circleParam θ
  rw [add_comm]
  exact (circleParam_periodic.int_mul n) θ

/-- Window independence: the pushforward from any length-`2π` window is σ. -/
lemma map_circleParam_Ico (a : ℝ) :
    Measure.map circleParam (volume.restrict (Ico a (a + 2 * π))) = circleMeasure := by
  set n : ℤ := ⌈a / (2 * π)⌉ with hn
  set c : ℝ := (n : ℝ) * (2 * π) with hc
  have hac : a ≤ c := by
    rw [hc]
    have h := Int.le_ceil (a / (2 * π))
    calc a = (a / (2 * π)) * (2 * π) := by field_simp
    _ ≤ (n : ℝ) * (2 * π) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast h) Real.two_pi_pos.le
  have hca : c < a + 2 * π := by
    rw [hc]
    have h := Int.ceil_lt_add_one (a / (2 * π))
    calc (n : ℝ) * (2 * π) < (a / (2 * π) + 1) * (2 * π) :=
          mul_lt_mul_of_pos_right (by exact_mod_cast h) Real.two_pi_pos
    _ = a + 2 * π := by field_simp
  have hsplit : Ico a (a + 2 * π) = Ico a c ∪ Ico c (a + 2 * π) :=
    (Ico_union_Ico_eq_Ico hac hca.le).symm
  rw [hsplit, Measure.restrict_union Ico_disjoint_Ico_same measurableSet_Ico,
    Measure.map_add _ _ measurable_circleParam]
  have hp1a : ((n - 1 : ℤ) : ℝ) * (2 * π) + (a + 2 * π - c) = a := by
    rw [hc]; push_cast; ring
  have hp1b : ((n - 1 : ℤ) : ℝ) * (2 * π) + (2 * π) = c := by
    rw [hc]; push_cast; ring
  have hpiece1 : Measure.map circleParam (volume.restrict (Ico a c)) =
      Measure.map circleParam (volume.restrict (Ico (a + 2 * π - c) (2 * π))) := by
    have h := map_circleParam_shift (n - 1) (a + 2 * π - c) (2 * π)
    rw [hp1a, hp1b] at h
    exact h
  have hp2a : (n : ℝ) * (2 * π) + 0 = c := by rw [hc]; ring
  have hp2b : (n : ℝ) * (2 * π) + (a + 2 * π - c) = a + 2 * π := by rw [hc]; ring
  have hpiece2 : Measure.map circleParam (volume.restrict (Ico c (a + 2 * π))) =
      Measure.map circleParam (volume.restrict (Ico 0 (a + 2 * π - c))) := by
    have h := map_circleParam_shift n 0 (a + 2 * π - c)
    rw [hp2a, hp2b] at h
    exact h
  rw [hpiece1, hpiece2, ← Measure.map_add _ _ measurable_circleParam,
    add_comm (volume.restrict (Ico (a + 2 * π - c) (2 * π))),
    ← Measure.restrict_union Ico_disjoint_Ico_same measurableSet_Ico,
    Ico_union_Ico_eq_Ico (by linarith) (by linarith)]
  rfl

/-- Change of variables over any angular window of length `2π`. -/
lemma integral_circleMeasure_window {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) {f : Circle₁ → E} (hf : AEStronglyMeasurable f circleMeasure) :
    ∫ w, f w ∂circleMeasure = ∫ θ in Ico a (a + 2 * π), f (circleParam θ) := by
  rw [← map_circleParam_Ico a] at hf ⊢
  exact integral_map measurable_circleParam.aemeasurable hf

/-- Change of variables over an arbitrary angular window for an integrable function. -/
lemma integral_circleMeasure_window_of_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (a : ℝ) {f : Circle₁ → E} (hf : Integrable f circleMeasure) :
    ∫ w, f w ∂circleMeasure = ∫ θ in Ico a (a + 2 * π), f (circleParam θ) :=
  integral_circleMeasure_window a hf.aestronglyMeasurable

/-- **Rotation invariance**: every rotation is σ-preserving. -/
lemma measurePreserving_circleRotate (α : ℝ) :
    MeasurePreserving (circleRotate α) circleMeasure circleMeasure := by
  refine ⟨(continuous_circleRotate α).measurable, ?_⟩
  conv_lhs => rw [circleMeasure]
  rw [Measure.map_map (continuous_circleRotate α).measurable measurable_circleParam]
  have hcomp : circleRotate α ∘ circleParam = circleParam ∘ (fun θ => α + θ) := by
    funext θ
    exact circleRotate_circleParam α θ
  rw [hcomp, ← Measure.map_map measurable_circleParam (measurable_const_add α),
    map_translate, add_zero, map_circleParam_Ico]

end KsIndex.Trace
