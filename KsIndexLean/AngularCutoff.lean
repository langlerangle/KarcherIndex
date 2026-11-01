module

public import KsIndexLean.CircleMultiplier

@[expose] public section


open Set MeasureTheory
open scoped ContDiff InnerProductSpace

noncomputable section
namespace KsIndex.Trace

def realCircleMap (η : ℂ → ℝ) (hη : Continuous η) : C(Circle₁, ℝ) :=
  ⟨fun w => η w, hη.comp continuous_subtype_val⟩

lemma circleMul_angularTestLp (η H : ℂ → ℝ) (hη : Continuous η) (hH : Continuous H) :
    circleMul (realCircleMap η hη) (angularTestLp H hH) =
      angularTestLp (fun z => η z * H z) (hη.mul hH) := by
  apply Lp.ext
  filter_upwards [circleMul_coe (realCircleMap η hη) (angularTestLp H hH),
    ContinuousMap.coeFn_toLp (p := 2) (μ := circleMeasure) (𝕜 := ℂ) (realAngularMap H hH),
    ContinuousMap.coeFn_toLp (p := 2) (μ := circleMeasure) (𝕜 := ℂ)
      (realAngularMap (fun z => η z * H z) (hη.mul hH))] with w hm hH hP
  change _ = ((ContinuousMap.toLp 2 circleMeasure ℂ _) : Circle₁ → ℂ) w
  rw [hm, hP]
  change η w • ((ContinuousMap.toLp 2 circleMeasure ℂ _) : Circle₁ → ℂ) w = _
  rw [hH]
  simp [realAngularMap, Complex.real_smul]

lemma angularTestLp_product_deriv {η H : ℂ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hH : ContDiff ℝ (⊤ : ℕ∞) H) :
    angularTestLp (angularTestDeriv (fun z => η z * H z))
      (contDiff_angularTestDeriv (hη.mul hH)).continuous =
    circleMul (realCircleMap η hη.continuous)
      (angularTestLp (angularTestDeriv H) (contDiff_angularTestDeriv hH).continuous) +
    circleMul (realCircleMap (angularTestDeriv η) (contDiff_angularTestDeriv hη).continuous)
      (angularTestLp H hH.continuous) := by
  rw [circleMul_angularTestLp, circleMul_angularTestLp]
  apply Lp.ext
  filter_upwards [
    ContinuousMap.coeFn_toLp (p := 2) (μ := circleMeasure) (𝕜 := ℂ)
      (realAngularMap _ (contDiff_angularTestDeriv (hη.mul hH)).continuous),
    ContinuousMap.coeFn_toLp (p := 2) (μ := circleMeasure) (𝕜 := ℂ)
      (realAngularMap (fun z => η z * angularTestDeriv H z)
        (hη.continuous.mul (contDiff_angularTestDeriv hH).continuous)),
    ContinuousMap.coeFn_toLp (p := 2) (μ := circleMeasure) (𝕜 := ℂ)
      (realAngularMap (fun z => angularTestDeriv η z * H z)
        ((contDiff_angularTestDeriv hη).continuous.mul hH.continuous)),
    Lp.coeFn_add
      (angularTestLp (fun z => η z * angularTestDeriv H z) _)
      (angularTestLp (fun z => angularTestDeriv η z * H z) _)] with w hP hA hB hsum
  simp only [Pi.add_apply] at hsum
  rw [hsum]
  change ((ContinuousMap.toLp 2 circleMeasure ℂ _) : Circle₁ → ℂ) w =
    ((ContinuousMap.toLp 2 circleMeasure ℂ _) : Circle₁ → ℂ) w +
    ((ContinuousMap.toLp 2 circleMeasure ℂ _) : Circle₁ → ℂ) w
  rw [hP, hA, hB]
  simp only [realAngularMap, ContinuousMap.coe_mk, angularTestDeriv_mul hη hH,
    Complex.ofReal_add, Complex.ofReal_mul]
  ring

/-- Smooth real angular cutoffs preserve the weak graph, with the full product term. -/
theorem circleAngularGraph_cutoff {F G : Lp ℂ 2 circleMeasure}
    (h : (F, G) ∈ circleAngularGraph) {η : ℂ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    (circleMul (realCircleMap η hη.continuous) F,
      circleMul (realCircleMap η hη.continuous) G +
      circleMul (realCircleMap (angularTestDeriv η) (contDiff_angularTestDeriv hη).continuous) F)
        ∈ circleAngularGraph := by
  rw [mem_circleAngularGraph_iff]
  intro H hH
  have hp := (mem_circleAngularGraph_iff F G).mp h _ (hη.mul hH)
  rw [angularTestLp_product_deriv hη hH, inner_add_left] at hp
  rw [inner_add_right, inner_circleMul, inner_circleMul, inner_circleMul]
  simp only [circleMul_angularTestLp] at hp ⊢
  linear_combination hp

end KsIndex.Trace
