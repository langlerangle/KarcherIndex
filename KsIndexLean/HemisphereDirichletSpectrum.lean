module

public import KsIndexLean.HemisphereDirichletKernel

@[expose] public section


/-! The canonical hemisphere mass pairing and full weak Dirichlet eigenspaces.
The stereographic coordinate equivalence preserves the integral eigenvalue
equation, including zero, and transfers the least-eigenvalue and simplicity results. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spectral

/-- Canonical lower-hemisphere mass pairing, conjugate-linear in its first slot. -/
def hemisphereMassPair (u v : HemisphereChartSpace) : ℂ :=
  ∫ p in {p : Sphere | p.val 2 < 0},
    (starRingEnd ℂ) (hemisphereValue u p) * hemisphereValue v p
      ∂(volume : Measure Ambient).toSphere

lemma hemisphereMassPair_eq (u v : HemisphereChartSpace) :
    hemisphereMassPair u v =
      inner ℂ (weightedDiskValueCLM (hemisphereCoordinates u))
        (weightedDiskValueCLM (hemisphereCoordinates v)) := by
  rw [hemisphereMassPair, ← sphereChart_disk_eq_lower, canonicalArea_restrict,
    Set.preimage_image_eq _ sphereChart_injective,
    measurableEmbedding_sphereChart.integral_map, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sphericalBulkMap_ae (valueCLM (hemisphereCoordinates u)),
    sphericalBulkMap_ae (valueCLM (hemisphereCoordinates v))] with z hu hv
  change (starRingEnd ℂ) (sphereWeakValue (hemisphereCoordinates u) (sphereChart z)) *
    sphereWeakValue (hemisphereCoordinates v) (sphereChart z) = _
  rw [sphereWeakValue_pullback, sphereWeakValue_pullback]
  change (starRingEnd ℂ) (valueCLM (hemisphereCoordinates u) z) *
    valueCLM (hemisphereCoordinates v) z =
    inner ℂ (sphericalBulkMap (valueCLM (hemisphereCoordinates u)) z)
      (sphericalBulkMap (valueCLM (hemisphereCoordinates v)) z)
  rw [hu, hv, RCLike.inner_apply, mul_comm]


local instance dirichletSpectralComplete : CompleteSpace (zeroTraceDomain Set.univ) :=
  (isClosed_zeroTraceDomain Set.univ).completeSpace_coe

/-- The full Dirichlet eigenspace in the actual lower-hemisphere carrier.
The integral equation characterizing this submodule is proved separately. -/
def hemisphereDirichletEigenspace (k : ℕ) (lam : ℝ) :
    Submodule ℂ hemisphereDirichletDomain :=
  (diskWeakEigenspace (zeroTraceDomain Set.univ) (surfacePotential k) lam).comap
    (hemisphereDomainEquiv (zeroTraceDomain Set.univ)).symm.toLinearMap

lemma mem_hemisphereDirichletEigenspace (k : ℕ) (lam : ℝ)
    (u : hemisphereDirichletDomain) :
    u ∈ hemisphereDirichletEigenspace k lam ↔
      ∀ v : hemisphereDirichletDomain,
        hemisphereJacobi (surfacePotential k) u v =
          (lam : ℂ) * hemisphereMassPair u v := by
  change (hemisphereDomainEquiv (zeroTraceDomain Set.univ)).symm u ∈
    diskWeakEigenspace (zeroTraceDomain Set.univ) (surfacePotential k) lam ↔ _
  rw [mem_diskWeakEigenspace_all]
  constructor
  · intro h v
    have hh := h ((hemisphereDomainEquiv (zeroTraceDomain Set.univ)).symm v)
    rw [hemisphereJacobi_eq, hemisphereMassPair_eq]
    exact hh
  · intro h v
    have hh := h (hemisphereDomainEquiv (zeroTraceDomain Set.univ) v)
    rw [hemisphereJacobi_eq, hemisphereMassPair_eq] at hh
    change weakJacobi (surfacePotential k) (hemisphereCoordinates u)
      (hemisphereCoordinates (hemisphereCoordinates.symm (v : ComplexH1))) =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM (hemisphereCoordinates u))
        (weightedDiskValueCLM
          (hemisphereCoordinates (hemisphereCoordinates.symm (v : ComplexH1)))) at hh
    rw [LinearIsometryEquiv.apply_symm_apply] at hh
    exact hh

/-- Zero is least among the full weak Dirichlet eigenvalues on the hemisphere. -/
theorem hemisphereDirichlet_zero_isLeast {k : ℕ} (hk : 3 ≤ k) :
    IsLeast {lam : ℝ | ∃ u : hemisphereDirichletDomain, u ≠ 0 ∧
      u ∈ hemisphereDirichletEigenspace k lam} 0 := by
  let e := hemisphereDomainEquiv (zeroTraceDomain Set.univ)
  obtain ⟨⟨w, hw, he⟩, hleast⟩ := fullDirichlet_zero_isLeast_eigenvalue hk
  constructor
  · refine ⟨e w, ?_, ?_⟩
    · intro h
      exact hw (e.injective (h.trans e.map_zero.symm))
    · change e.symm (e w) ∈ diskWeakEigenspace _ _ 0
      simpa only [LinearEquiv.symm_apply_apply] using he
  · rintro lam ⟨u, hu, he⟩
    apply hleast
    refine ⟨e.symm u, ?_, he⟩
    intro h
    exact hu (e.symm.injective (h.trans e.symm.map_zero.symm))

/-- The hemisphere and disk weak eigenspaces are linearly equivalent. -/
def hemisphereDirichletEigenspaceEquiv (k : ℕ) (lam : ℝ) :
    hemisphereDirichletEigenspace k lam ≃ₗ[ℂ]
      diskWeakEigenspace (zeroTraceDomain Set.univ) (surfacePotential k) lam :=
  (hemisphereDomainEquiv (zeroTraceDomain Set.univ)).symm.ofSubmodule'
    (diskWeakEigenspace (zeroTraceDomain Set.univ) (surfacePotential k) lam)

/-- The zero Dirichlet eigenspace on the hemisphere is simple. -/
theorem hemisphereDirichlet_zero_finrank {k : ℕ} (hk : 2 ≤ k) :
    Module.finrank ℂ (hemisphereDirichletEigenspace k 0) = 1 := by
  rw [(hemisphereDirichletEigenspaceEquiv k 0).finrank_eq]
  exact fullDirichlet_zero_eigenspace_finrank hk

/-- Every member of the zero eigenspace is invariant under all spherical rotations. -/
theorem hemisphereDirichlet_zero_rotation {k : ℕ} (hk : 2 ≤ k)
    (u : hemisphereDirichletDomain) (hu : u ∈ hemisphereDirichletEigenspace k 0)
    (θ : ℝ) :
    (fun p => hemisphereValue u (rotateSphere θ p))
      =ᵐ[(volume : Measure Ambient).toSphere.restrict
        {p : Sphere | p.val 2 < 0}] (hemisphereValue u) := by
  apply hemisphereDirichlet_kernel_rotation hk u
  intro v
  have h := (mem_hemisphereDirichletEigenspace k 0 u).mp hu v
  simpa only [Complex.ofReal_zero, zero_mul] using h

end KsIndex.Spherical
