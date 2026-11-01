module

public import KsIndexLean.ExplicitModeJacobi
public import KsIndexLean.WeakDirichletKernelClassification

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma verticalThree_flux_pairing_ne_zero :
    weakJacobi (surfacePotential 3) verticalThreeH1 slitFluxTestH1 ≠ 0 := by
  change weakJacobi (surfacePotential 3) verticalThreeH1
    (globalSmoothH1 slitFluxTest slitFluxTest_smooth) ≠ 0
  rw [verticalThree_smooth_green]
  exact mul_ne_zero (by norm_num) slitFluxTest_boundary_integral_ne_zero

/-- Zero boundary trace and the full weak Neumann equation force zero. -/
lemma weak_neumann_zero_of_trace_zero (u : ComplexH1)
    (hu : ∀ v : ComplexH1, weakJacobi (surfacePotential 3) u v = 0)
    (ht : diskTraceCLM u = 0) : u = 0 := by
  obtain ⟨c, hc⟩ := fullDirichlet_kernel_eq_smul_vertical
    ⟨u, (mem_fullZeroTrace_iff u).mpr ht⟩ (fun v => hu v)
  change u = c • verticalThreeH1 at hc
  have h := hu slitFluxTestH1
  rw [hc, weakJacobi_smul_left] at h
  have hz := (mul_eq_zero.mp h).resolve_right verticalThree_flux_pairing_ne_zero
  have hc0 : c = 0 := (starRingEnd ℂ).injective (hz.trans (map_zero (starRingEnd ℂ)).symm)
  rw [hc, hc0, zero_smul]

lemma weak_neumann_eq_of_trace_eq (u v : ComplexH1)
    (hu : ∀ w : ComplexH1, weakJacobi (surfacePotential 3) u w = 0)
    (hv : ∀ w : ComplexH1, weakJacobi (surfacePotential 3) v w = 0)
    (ht : diskTraceCLM u = diskTraceCLM v) : u = v := by
  apply sub_eq_zero.mp
  apply weak_neumann_zero_of_trace_zero (u - v)
  · intro w
    rw [sub_eq_add_neg, ← neg_one_smul ℂ v, weakJacobi_add_left, weakJacobi_smul_left,
      hu, hv, mul_zero, add_zero]
  · rw [map_sub, ht, sub_self]

/-- The two resonant trace coefficients determine a full k=3 Neumann solution. -/
lemma weak_neumann_eq_of_resonant_coefficients (u v : ComplexH1)
    (hu : ∀ w : ComplexH1, weakJacobi (surfacePotential 3) u w = 0)
    (hv : ∀ w : ComplexH1, weakJacobi (surfacePotential 3) v w = 0)
    (hp : circleFourierCoeff (diskTraceCLM u) 2 = circleFourierCoeff (diskTraceCLM v) 2)
    (hm : circleFourierCoeff (diskTraceCLM u) (-2) = circleFourierCoeff (diskTraceCLM v) (-2)) :
    u = v := by
  apply weak_neumann_eq_of_trace_eq u v hu hv
  apply circle_eq_of_coefficients_eq
  intro n
  simp only [circleCoefficientCLM_apply]
  by_cases hn : n.natAbs = 2
  · have he : n = 2 ∨ n = -2 := by omega
    rcases he with rfl | rfl
    · exact hp
    · exact hm
  · rw [weak_neumann_nonresonant_boundary_zero (by decide : 2 ≤ 3) u hu n hn,
      weak_neumann_nonresonant_boundary_zero (by decide : 2 ≤ 3) v hv n hn]

end KsIndex.Trace
