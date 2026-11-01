module

public import KsIndexLean.HemisphereGermH1
public import KsIndexLean.WeakFiniteOrderGreen
public import KsIndexLean.SphericalChartDirichletEigen
public import KsIndexLean.JacobiFamily

@[expose] public section

noncomputable section
open Set Filter Topology Metric MeasureTheory
open scoped ContDiff
namespace KsIndex.Spherical
open KsIndex.WeakH1 KsIndex.Trace
/-- Smooth ambient germs on the closed hemisphere suffice for the classical-to-weak
spherical eigenvalue equation; no globally smooth extension is assumed. -/
lemma hemisphere_classical_weak_eigen (k : ℕ) (lam : ℝ) (f : Sphere → ℂ)
    (hf : ∀ p : Sphere, p.val 2 ≤ 0 → HasSmoothClosedHemisphereGerm f p)
    (he : ∀ z ∈ (WeakH1.disk : Set ℂ),
      sphericalChartJacobiOperator k (f ∘ sphereChart) z = -(lam : ℂ) * f (sphereChart z))
    (v : ComplexH1) (hv : v ∈ zeroTraceDomain Set.univ) :
    weakJacobi (surfacePotential k) (hemisphereGermH1 f hf) v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM (hemisphereGermH1 f hf))
        (weightedDiskValueCLM v) := by
  obtain ⟨G, hG, _, hGf⟩ := hemisphere_germs_finite_closed_chart_extension f hf 2
  have heq (z : ℂ) (hz : z ∈ (WeakH1.disk : Set ℂ)) :
      (f ∘ sphereChart) =ᶠ[𝓝 z] G := by
    filter_upwards [WeakH1.disk.isOpen.mem_nhds hz] with w hw
    exact hGf w (ball_subset_closedBall hw)
  have hval : valueCLM (hemisphereGermH1 f hf) =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] G := by
    filter_upwards [hemisphereGermH1_value f hf,
      ae_restrict_mem WeakH1.disk.isOpen.measurableSet] with z hz hzd
    exact hz.trans (hGf z (ball_subset_closedBall hzd))
  have hdx : dxCLM (hemisphereGermH1 f hf) =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)]
      (fun z => fderiv ℝ G z 1) := by
    filter_upwards [hemisphereGermH1_dx f hf,
      ae_restrict_mem WeakH1.disk.isOpen.measurableSet] with z hz hzd
    rw [hz, (heq z hzd).fderiv_eq]
  have hdy : dyCLM (hemisphereGermH1 f hf) =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)]
      (fun z => fderiv ℝ G z Complex.I) := by
    filter_upwards [hemisphereGermH1_dy f hf,
      ae_restrict_mem WeakH1.disk.isOpen.measurableSet] with z hz hzd
    rw [hz, (heq z hzd).fderiv_eq]
  apply C2_spherical_eigen_weak (surfacePotential k) lam G hG
    (hemisphereGermH1 f hf) hval hdx hdy _ v hv
  intro z hz
  have h := sphericalChart_eigen_pde k lam (f ∘ sphereChart) z (he z hz)
  rw [KsIndex.JacobiFamily.laplacian_congr (heq z hz), (heq z hz).self_of_nhds] at h
  exact h
lemma hemisphereGermH1_zeroTrace (f : Sphere → ℂ)
    (hf : ∀ p : Sphere, p.val 2 ≤ 0 → HasSmoothClosedHemisphereGerm f p)
    (hb : ∀ p : Sphere, p.val 2 = 0 → f p = 0) :
    hemisphereGermH1 f hf ∈ zeroTraceDomain Set.univ := by
  apply (mem_fullZeroTrace_iff _).mpr
  apply Lp.ext
  filter_upwards [hemisphereGermH1_trace f hf, Lp.coeFn_zero ℂ 2 circleMeasure] with w hw hz
  rw [hw, hz]
  apply hb
  have hn : ‖(w : ℂ)‖ = 1 := by
    simpa only [Circle₁, mem_sphere, dist_zero_right] using w.property
  change (‖(w : ℂ)‖ ^ 2 - 1) / (1 + ‖(w : ℂ)‖ ^ 2) = 0
  simp [hn]

lemma hemisphereGermH1_ne_zero (f : Sphere → ℂ)
    (hf : ∀ p : Sphere, p.val 2 ≤ 0 → HasSmoothClosedHemisphereGerm f p)
    (hne : ∃ z ∈ (WeakH1.disk : Set ℂ), f (sphereChart z) ≠ 0) :
    hemisphereGermH1 f hf ≠ 0 := by
  intro hz
  obtain ⟨z, hzd, hzf⟩ := hne
  have hv := hemisphereGermH1_value f hf
  rw [hz, map_zero] at hv
  have ha : (f ∘ sphereChart) =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] (fun _ => 0) :=
    hv.symm.trans (Lp.coeFn_zero ℂ 2 _)
  exact hzf (Measure.eqOn_open_of_ae_eq ha WeakH1.disk.isOpen
    (hemisphere_germs_chart_smooth f hf).continuousOn continuousOn_const hzd)

local instance : CompleteSpace (zeroTraceDomain Set.univ) :=
  (isClosed_zeroTraceDomain Set.univ).completeSpace_coe

/-- A nonzero classical Dirichlet eigenfunction smooth up to the equator has
nonnegative eigenvalue. Positivity follows from the vertical ground state
and compact-core density. -/
theorem hemisphere_classical_dirichlet_nonnegative {k : ℕ} (hk : 3 ≤ k)
    (lam : ℝ) (f : Sphere → ℂ)
    (hf : ∀ p : Sphere, p.val 2 ≤ 0 → HasSmoothClosedHemisphereGerm f p)
    (hb : ∀ p : Sphere, p.val 2 = 0 → f p = 0)
    (hne : ∃ z ∈ (WeakH1.disk : Set ℂ), f (sphereChart z) ≠ 0)
    (he : ∀ z ∈ (WeakH1.disk : Set ℂ),
      sphericalChartJacobiOperator k (f ∘ sphereChart) z = -(lam : ℂ) * f (sphereChart z)) :
    0 ≤ lam := by
  apply KsIndex.Spectral.fullDirichlet_eigenvalue_nonnegative hk lam
    ⟨hemisphereGermH1 f hf, hemisphereGermH1_zeroTrace f hf hb⟩
  · intro h
    exact hemisphereGermH1_ne_zero f hf hne (congrArg Subtype.val h)
  · apply (KsIndex.Spectral.mem_diskWeakEigenspace_all _ _ _ _).mpr
    intro v
    exact hemisphere_classical_weak_eigen k lam f hf he v v.property
end KsIndex.Spherical
