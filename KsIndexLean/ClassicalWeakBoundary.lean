module

public import KsIndexLean.DiskNeighborhoodExtension
public import KsIndexLean.SmoothWeakGreen

@[expose] public section


/-! Classical pure-boundary Jacobi equations imply the full weak test
identities. The normal flux in Green's formula is the actual derivative. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Surface

/-- An interior classical Jacobi solution annihilates all zero-trace tests. -/
theorem smooth_jacobi_dirichlet_tests (V : BoundedRealPotential) (G : ℂ → ℂ)
    (hG : ContDiff ℝ ∞ G)
    (hP : ∀ z ∈ (WeakH1.disk : Set ℂ), laplacian G z + (V.V z : ℂ) * G z = 0) :
    ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi V (globalSmoothH1 G hG) v = 0 := by
  let flux : C(Circle₁, ℂ) :=
    ⟨fun w => fderiv ℝ G w w,
      ((hG.continuous_fderiv (by simp)).comp continuous_subtype_val).clm_apply
        continuous_subtype_val⟩
  have hm := flux.memLp (μ := circleMeasure) (p := 2) ℂ
  intro v hv
  rw [smooth_weak_green_of_flux V G hG hP (hm.toLp flux) hm.coeFn_toLp v,
    (mem_fullZeroTrace_iff v).mp hv, inner_zero_right]

/-- A classical solution with zero radial derivative annihilates every H¹ test. -/
theorem smooth_jacobi_neumann_tests (V : BoundedRealPotential) (G : ℂ → ℂ)
    (hG : ContDiff ℝ ∞ G)
    (hP : ∀ z ∈ (WeakH1.disk : Set ℂ), laplacian G z + (V.V z : ℂ) * G z = 0)
    (hN : ∀ z : ℂ, ‖z‖ = 1 → fderiv ℝ G z z = 0) :
    ∀ v : ComplexH1, weakJacobi V (globalSmoothH1 G hG) v = 0 := by
  intro v
  have hflux : ((0 : Lp ℂ 2 circleMeasure) : Circle₁ → ℂ) =ᵐ[circleMeasure]
      (fun w => fderiv ℝ G w w) := by
    filter_upwards [Lp.coeFn_zero (E := ℂ) (p := (2 : ENNReal)) (μ := circleMeasure)] with w hw
    rw [hw, hN w (mem_sphere_zero_iff_norm.mp w.property)]
    rfl
  rw [smooth_weak_green_of_flux V G hG hP 0 hflux v, inner_zero_left]

/-- A neighborhood solution can be replaced by a globally smooth function
without changing its disk equation or any closed-disk germ. -/
lemma exists_global_jacobi_disk (V : BoundedRealPotential) {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Metric.ball 0 2))
    (hP : ∀ z ∈ (WeakH1.disk : Set ℂ), laplacian f z + (V.V z : ℂ) * f z = 0) :
    ∃ G : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) G ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, G =ᶠ[nhds z] f) ∧
      ∀ z ∈ (WeakH1.disk : Set ℂ), laplacian G z + (V.V z : ℂ) * G z = 0 := by
  obtain ⟨G, hG, _, he⟩ := exists_global_smooth_disk_extension hf
  refine ⟨G, hG, he, ?_⟩
  intro z hz
  have hg := he z (Metric.ball_subset_closedBall hz)
  rw [JacobiFamily.laplacian_congr hg, hg.self_of_nhds]
  exact hP z hz

/-- Smooth neighborhood Dirichlet solutions yield actual zero-trace weak
radicals, with the original values retained almost everywhere. -/
theorem neighborhood_dirichlet_weak (V : BoundedRealPotential) {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Metric.ball 0 2))
    (hP : ∀ z ∈ (WeakH1.disk : Set ℂ), laplacian f z + (V.V z : ℂ) * f z = 0)
    (hD : ∀ z : ℂ, ‖z‖ = 1 → f z = 0) :
    ∃ u : ComplexH1, valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] f ∧
      u ∈ zeroTraceDomain Set.univ ∧
      ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi V u v = 0 := by
  obtain ⟨G, hG, he, hGP⟩ := exists_global_jacobi_disk V hf hP
  refine ⟨globalSmoothH1 G hG, ?_, ?_, smooth_jacobi_dirichlet_tests V G hG hGP⟩
  · filter_upwards [globalSmoothH1_value G hG,
      ae_restrict_mem WeakH1.disk.isOpen.measurableSet] with z hz hd
    exact hz.trans (he z (Metric.ball_subset_closedBall hd)).self_of_nhds
  · apply globalSmoothH1_zeroTrace_of_vanish MeasurableSet.univ hG
    intro w _
    have hw := mem_sphere_zero_iff_norm.mp w.property
    have hc : (w : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, hw]
    rw [(he w hc).self_of_nhds]
    exact hD w hw

/-- Smooth neighborhood Neumann solutions yield actual full weak radicals. -/
theorem neighborhood_neumann_weak (V : BoundedRealPotential) {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Metric.ball 0 2))
    (hP : ∀ z ∈ (WeakH1.disk : Set ℂ), laplacian f z + (V.V z : ℂ) * f z = 0)
    (hN : ∀ z : ℂ, ‖z‖ = 1 → fderiv ℝ f z z = 0) :
    ∃ u : ComplexH1, valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] f ∧
      ∀ v : ComplexH1, weakJacobi V u v = 0 := by
  obtain ⟨G, hG, he, hGP⟩ := exists_global_jacobi_disk V hf hP
  refine ⟨globalSmoothH1 G hG, ?_, ?_⟩
  · filter_upwards [globalSmoothH1_value G hG,
      ae_restrict_mem WeakH1.disk.isOpen.measurableSet] with z hz hd
    exact hz.trans (he z (Metric.ball_subset_closedBall hd)).self_of_nhds
  · apply smooth_jacobi_neumann_tests V G hG hGP
    intro z hz
    have hc : z ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, hz]
    rw [(he z hc).fderiv_eq]
    exact hN z hz

end KsIndex.Trace
