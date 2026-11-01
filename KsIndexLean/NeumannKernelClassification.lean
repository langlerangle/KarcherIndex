module

public import KsIndexLean.NeumannTraceInjectivity
public import KsIndexLean.CircleFourierRotation

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

lemma circleFourierCoeff_fourierAmbient (m n : ℤ) :
    circleFourierCoeff (fun w : Circle₁ => fourierAmbient m w) n = (Pi.single m 1 : ℤ → ℂ) n := by
  rw [← fourierCoeff_geometric_pullback]
  have he : (fun x : AddCircle (2 * Real.pi) => fourierAmbient m (fourierCircleHomeomorph x)) =
      fourier m := by
    funext x
    induction x using QuotientAddGroup.induction_on with
    | H x => rw [fourierCircleHomeomorph_coe, fourierAmbient_circleParam]
  rw [he, fourierCoeff_fourier]

lemma horizontalThree_trace_coeff (n : ℤ) :
    circleFourierCoeff (diskTraceCLM horizontalThreeH1) n = (Pi.single 2 1 : ℤ → ℂ) n := by
  rw [congrFun (circleFourierCoeff_congr_ae horizontalThreeH1_trace) n]
  exact circleFourierCoeff_fourierAmbient 2 n

lemma horizontalThreeConj_trace_coeff (n : ℤ) :
    circleFourierCoeff (diskTraceCLM horizontalThreeConjH1) n = (Pi.single (-2) 1 : ℤ → ℂ) n := by
  have h : (diskTraceCLM horizontalThreeConjH1 : Circle₁ → ℂ) =ᵐ[circleMeasure]
      fun w => fourierAmbient (-2) w := by
    filter_upwards [horizontalThreeConjH1_trace] with w hw
    change diskTraceCLM horizontalThreeConjH1 w = (starRingEnd ℂ) (w : ℂ) ^ 2
    simpa only [map_pow] using hw
  rw [congrFun (circleFourierCoeff_congr_ae h) n]
  exact circleFourierCoeff_fourierAmbient (-2) n

lemma weak_neumann_eq_horizontal_combination (u : ComplexH1)
    (hu : ∀ v : ComplexH1, weakJacobi (surfacePotential 3) u v = 0) :
    u = circleFourierCoeff (diskTraceCLM u) 2 • horizontalThreeH1 +
      circleFourierCoeff (diskTraceCLM u) (-2) • horizontalThreeConjH1 := by
  apply weak_neumann_eq_of_resonant_coefficients u _ hu
  · intro v
    rw [weakJacobi_add_left, weakJacobi_smul_left, weakJacobi_smul_left,
      horizontalThree_weak_neumann, horizontalThreeConj_weak_neumann]
    simp
  · simp only [← circleCoefficientCLM_apply, map_add, map_smul]
    simp only [circleCoefficientCLM_apply, horizontalThree_trace_coeff, horizontalThreeConj_trace_coeff, smul_eq_mul]
    norm_num [Pi.single_apply]
  · simp only [← circleCoefficientCLM_apply, map_add, map_smul]
    simp only [circleCoefficientCLM_apply, horizontalThree_trace_coeff, horizontalThreeConj_trace_coeff, smul_eq_mul]
    norm_num [Pi.single_apply]

lemma weak_neumann_iff_horizontal_span (u : ComplexH1) :
    (∀ v : ComplexH1, weakJacobi (surfacePotential 3) u v = 0) ↔
      ∃ a b : ℂ, u = a • horizontalThreeH1 + b • horizontalThreeConjH1 := by
  constructor
  · intro hu
    exact ⟨_, _, weak_neumann_eq_horizontal_combination u hu⟩
  · rintro ⟨a, b, rfl⟩ v
    rw [weakJacobi_add_left, weakJacobi_smul_left, weakJacobi_smul_left,
      horizontalThree_weak_neumann, horizontalThreeConj_weak_neumann]
    simp

end KsIndex.Trace
