module

public import KsIndexLean.HemisphereWeakDomains
public import KsIndexLean.GeneralDirichletLowest

@[expose] public section


/-! Nonnegativity and the vertical zero kernel of the actual single-hemisphere
Dirichlet form. These form statements do not by themselves assert a classical
spectral realization or boundary regularity for nonzero eigenvalues. -/
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spectral

/-- The actual single-hemisphere Dirichlet form is nonnegative. -/
theorem hemisphereDirichlet_form_nonnegative {k : ℕ} (hk : 3 ≤ k)
    (u : hemisphereDirichletDomain) :
    0 ≤ (hemisphereJacobi (surfacePotential k) u u).re := by
  rw [hemisphereJacobi_eq]
  exact fullDirichlet_form_nonnegative hk _ u.property

/-- The zero kernel on the actual lower hemisphere consists of vertical fields. -/
theorem hemisphereDirichlet_kernel_iff {k : ℕ} (hk : 2 ≤ k)
    (u : hemisphereDirichletDomain) :
    (∀ v : hemisphereDirichletDomain,
      hemisphereJacobi (surfacePotential k) u v = 0) ↔
      ∃ c : ℂ, hemisphereCoordinates u = c • radialDirichletH1 hk := by
  constructor
  · intro h
    have hu : hemisphereCoordinates u ∈ zeroTraceDomain Set.univ := u.property
    apply generalDirichlet_kernel_span hk (hemisphereCoordinates u) hu
    intro v hv
    have hh := h (hemisphereDomainEquiv (zeroTraceDomain Set.univ) ⟨v, hv⟩)
    rw [hemisphereJacobi_eq] at hh
    change weakJacobi (surfacePotential k) (hemisphereCoordinates u)
      (hemisphereCoordinates (hemisphereCoordinates.symm v)) = 0 at hh
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hh
  · rintro ⟨c, hc⟩ v
    have hv : hemisphereCoordinates v ∈ zeroTraceDomain Set.univ := v.property
    have hz := radialDirichletH1_weak hk (hemisphereCoordinates v) hv
    rw [hemisphereJacobi_eq, hc, weakJacobi_smul_left, hz, mul_zero]

/-- Every zero Dirichlet field is invariant under every spherical rotation. -/
theorem hemisphereDirichlet_kernel_rotation {k : ℕ} (hk : 2 ≤ k)
    (u : hemisphereDirichletDomain)
    (hu : ∀ v : hemisphereDirichletDomain,
      hemisphereJacobi (surfacePotential k) u v = 0) (θ : ℝ) :
    (fun p => hemisphereValue u (rotateSphere θ p))
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure Ambient).toSphere.restrict
        {p : Sphere | p.val 2 < 0}] (hemisphereValue u) := by
  obtain ⟨c, hc⟩ := (hemisphereDirichlet_kernel_iff hk u).mp hu
  have hh : hemisphereCoordinates u ∈ weakCharacterDomain θ 1 := by
    rw [mem_weakCharacterDomain, hc, map_smul, radialDirichletH1_rotation, one_smul]
  simpa using (hemisphere_character_iff θ 1 u).mp hh
end KsIndex.Spherical
