module

public import KsIndexLean.JoinedJetUniqueness

@[expose] public section


open Set MeasureTheory TopologicalSpace
open scoped ContDiff Distributions Topology

noncomputable section
namespace KsIndex.Trace

lemma contDiff_mul_test {Ω : Opens ℂ} {χ : ℂ → ℝ}
    (hχ : ContDiffOn ℝ (⊤ : ℕ∞) χ Ω) (φ : 𝓓(Ω, ℝ)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => χ z * φ z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ Ω
  · exact (hχ.contDiffAt (Ω.isOpen.mem_nhds hz)).mul φ.contDiff.contDiffAt
  · have hs : z ∉ tsupport (φ : ℂ → ℝ) := fun h => hz (φ.tsupport_subset h)
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hs] with w hw
    simp only [hw, mul_zero, Pi.zero_apply]

def smoothMultiplierTest {Ω : Opens ℂ} (χ : ℂ → ℝ)
    (hχ : ContDiffOn ℝ (⊤ : ℕ∞) χ Ω) (φ : 𝓓(Ω, ℝ)) : 𝓓(Ω, ℝ) :=
  ⟨fun z => χ z * φ z, contDiff_mul_test hχ φ, φ.hasCompactSupport.mul_left,
    tsupport_mul_subset_right.trans φ.tsupport_subset⟩

lemma lineDeriv_smoothMultiplierTest {Ω : Opens ℂ} {χ : ℂ → ℝ}
    (hχ : ContDiffOn ℝ (⊤ : ℕ∞) χ Ω) (φ : 𝓓(Ω, ℝ)) (z d : ℂ) :
    lineDeriv ℝ (smoothMultiplierTest χ hχ φ : ℂ → ℝ) z d =
      (fderiv ℝ χ z d) * φ z + χ z * lineDeriv ℝ (φ : ℂ → ℝ) z d := by
  by_cases hz : z ∈ Ω
  · have hc := (hχ.contDiffAt (Ω.isOpen.mem_nhds hz)).differentiableAt (by simp)
    have hp := φ.contDiff.differentiable (by simp) z
    change lineDeriv ℝ (fun w => χ w * φ w) z d = _
    have hm : DifferentiableAt ℝ (fun w => χ w * φ w) z := hc.mul hp
    rw [hm.lineDeriv_eq_fderiv, fderiv_fun_mul hc hp, hp.lineDeriv_eq_fderiv]
    simp [mul_comm, add_comm]
  · have hs : z ∉ tsupport (φ : ℂ → ℝ) := fun h => hz (φ.tsupport_subset h)
    have ht : z ∉ tsupport (smoothMultiplierTest χ hχ φ : ℂ → ℝ) :=
      fun h => hz ((smoothMultiplierTest χ hχ φ).tsupport_subset h)
    have hp := φ.contDiff.differentiable (by simp) z
    have hm := (smoothMultiplierTest χ hχ φ).contDiff.differentiable (by simp) z
    rw [hm.lineDeriv_eq_fderiv, hp.lineDeriv_eq_fderiv,
      fderiv_of_notMem_tsupport ℝ ht, fderiv_of_notMem_tsupport ℝ hs]
    simp [image_eq_zero_of_notMem_tsupport hs]

end KsIndex.Trace
