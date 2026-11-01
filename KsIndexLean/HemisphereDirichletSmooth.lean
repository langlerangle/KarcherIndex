module

public import KsIndexLean.HemisphereDirichletSpectrum
public import KsIndexLean.HemisphereIntrinsicSmooth

@[expose] public section


/-! Explicit smooth representatives for the zero Dirichlet eigenspace on the
lower hemisphere, including smooth ambient germs at its equatorial boundary. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ContDiff
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spectral KsIndex.ModeDiag KsIndex.JacobiMode

/-- Every weak zero Dirichlet field has an explicit representative smooth up to
all points of the closed hemisphere. -/
theorem hemisphereDirichlet_zero_smooth {k : ℕ} (hk : 2 ≤ k)
    (u : hemisphereDirichletDomain) (hu : u ∈ hemisphereDirichletEigenspace k 0) :
    ∃ c : ℂ,
      hemisphereValue u =ᵐ[(volume : Measure Ambient).toSphere.restrict
        {p : Sphere | p.val 2 < 0}]
        (fun p => c * modeU k 0 (stereoCoord p.val)) ∧
      ∀ p : Sphere, p.val 2 ≤ 0 →
        HasSmoothClosedHemisphereGerm
          (fun q => c * modeU k 0 (stereoCoord q.val)) p := by
  have hz : ∀ v : hemisphereDirichletDomain,
      hemisphereJacobi (surfacePotential k) u v = 0 := by
    intro v
    simpa only [Complex.ofReal_zero, zero_mul] using
      (mem_hemisphereDirichletEigenspace k 0 u).mp hu v
  obtain ⟨c, hc⟩ := (hemisphereDirichlet_kernel_iff hk u).mp hz
  refine ⟨c, ?_, ?_⟩
  · apply (hemisphere_ae_eq_iff _ _).mpr
    simp only [hemisphereValue, sphereWeakValue_pullback]
    simp only [sphereChart, stereoCoord_stereoPoint, hc, map_smul]
    have he := globalSmoothH1_value (modeU k 0) (modeU_contDiff (by omega) 0)
    filter_upwards [Lp.coeFn_smul c (valueCLM (radialDirichletH1 hk)), he] with z hs he
    rw [hs]
    exact congrArg (fun x : ℂ => c * x) he
  · have hG : ContDiff ℝ ∞ (fun z => c * modeU k 0 z) :=
      contDiff_const.mul (modeU_contDiff (by omega) 0)
    apply closedHemisphere_smooth_of_coordinate hG.contDiffOn
    intro w _
    exact ⟨_, hG.contDiffAt, Eventually.of_forall (fun _ _ => rfl)⟩

end KsIndex.Spherical
