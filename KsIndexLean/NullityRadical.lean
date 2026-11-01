module

public import KsIndexLean.NullityGreen
public import KsIndexLean.VerticalWeakGreen
public import KsIndexLean.D5DensityAssembly
public import KsIndexLean.SlitReflectionNullity
public import KsIndexLean.JacobiRadicalRealization
public import KsIndexLean.NamedDomainSpectrum

@[expose] public section


/-!
# Sector restriction into the mixed-domain Jacobi radical

For `k ≥ 2` and reflection indices `s₁, s₀ < 2`, the copy-`0` restriction of a
bounded Jacobi sector field pairs to zero with every vector of
`mixedCharacterDomain k r (decide (s₁ = 0)) (decide (s₀ = 0))`.
The natural-core pairing identity extends to the whole domain by density and
continuity of the weak Jacobi form with its left argument fixed.

The restriction therefore defines an injective linear map into the form radical.
Finite-dimensionality of that radical implies finite-dimensionality of the sector
and bounds its rank, converted to `ℕ∞`, by the disk weak nullity. This gives an
upper bound; surjectivity of the restriction is not asserted here.
-/

noncomputable section
namespace KsIndex.NullityDecomp
open KsIndex.Surface KsIndex.SurfaceSym KsIndex.SurfaceForm KsIndex.WeakH1 KsIndex.Trace
open KsIndex.FaithfulInjection Complex MeasureTheory Filter Topology
open KsIndex.FormIndex KsIndex.Spectral
open scoped ContDiff

variable {k r s₁ s₀ : ℕ}

/-- The sector pairing vanishes against every mixed-domain test of
the matched flags, by continuity of the fixed-left weak form through the dense natural core. -/
lemma sector_weakJacobi_zero (hk : 2 ≤ k) (hs₁ : s₁ < 2) (hs₀ : s₀ < 2)
    (W : ↥(boundedJacobiSector k r s₁ s₀))
    (v : mixedCharacterDomain k r (decide (s₁ = 0)) (decide (s₀ = 0))) :
    weakJacobi (surfacePotential k) (sectorRestrictFun hk W) ↑v = 0 := by
  have hk1 : 1 ≤ k := by omega
  have hc1 : Continuous
      (fun v : mixedCharacterDomain k r (decide (s₁ = 0)) (decide (s₀ = 0)) =>
        weakJacobi (surfacePotential k) (sectorRestrictFun hk W) ↑v) :=
    (continuous_weakJacobi_fixed_left (surfacePotential k)
      (sectorRestrictFun hk W)).comp continuous_subtype_val
  have hc2 : Continuous
      (fun _ : mixedCharacterDomain k r (decide (s₁ = 0)) (decide (s₀ = 0)) =>
        (0 : ℂ)) := continuous_const
  have he := (naturalCharacterToMixed_denseRange hk1 r (decide (s₁ = 0))
      (decide (s₀ = 0))).equalizer hc1 hc2 (by
    funext f
    change weakJacobi (surfacePotential k) (sectorRestrictFun hk W)
      (naturalCoreH1 hk1 ⟨f.val, f.property.1⟩) = 0
    exact sector_pairing_zero hk hk1 hs₁ hs₀ W ⟨f.val, f.property.1⟩)
  exact congrFun he v

/-- Each joint symmetry sector injects into
the radical of its mixed-domain Jacobi form, so its rank is at most the disk weak nullity
of that domain. -/
theorem sector_rank_le_nullity (hk : 2 ≤ k) (hs₁ : s₁ < 2) (hs₀ : s₀ < 2) :
    Cardinal.toENat (Module.rank ℂ ↥(boundedJacobiSector k r s₁ s₀)) ≤
      (diskWeakNullity (mixedCharacterDomain k r (decide (s₁ = 0)) (decide (s₀ = 0)))
        (surfacePotential k) : ℕ∞) := by
  set D := mixedCharacterDomain k r (decide (s₁ = 0)) (decide (s₀ = 0)) with hD
  -- the sector-to-domain map
  let f₁ : ↥(boundedJacobiSector k r s₁ s₀) →ₗ[ℂ] ↥D :=
    (sectorRestrict hk).codRestrict D (fun W => sectorRestrict_mem hk hs₁ hs₀ W)
  -- it lands in the radical
  have hrad : ∀ W, f₁ W ∈ @formRadical ↥D inferInstance (diskDomain_innerProductSpace D)
      (domainJacobiForm D (surfacePotential k)) := by
    intro W
    rw [mem_formRadical]
    intro v
    exact sector_weakJacobi_zero hk hs₁ hs₀ W v
  let Φ : ↥(boundedJacobiSector k r s₁ s₀) →ₗ[ℂ]
      ↥(@formRadical ↥D inferInstance (diskDomain_innerProductSpace D)
        (domainJacobiForm D (surfacePotential k))) :=
    f₁.codRestrict _ hrad
  have hinj : Function.Injective Φ := by
    intro W₁ W₂ h
    apply sectorRestrict_injective hk
    have h1 : (Φ W₁ : ↥D) = (Φ W₂ : ↥D) := congrArg Subtype.val h
    exact congrArg Subtype.val h1
  have hfinR : FiniteDimensional ℂ
      ↥(@formRadical ↥D inferInstance (diskDomain_innerProductSpace D)
        (domainJacobiForm D (surfacePotential k))) :=
    diskRadical_finiteDimensional D (surfacePotential k)
  have hfd : FiniteDimensional ℂ ↥(boundedJacobiSector k r s₁ s₀) :=
    FiniteDimensional.of_injective Φ hinj
  have hle : Module.finrank ℂ ↥(boundedJacobiSector k r s₁ s₀) ≤
      Module.finrank ℂ
        ↥(@formRadical ↥D inferInstance (diskDomain_innerProductSpace D)
          (domainJacobiForm D (surfacePotential k))) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  have hcalc : Cardinal.toENat (Module.rank ℂ ↥(boundedJacobiSector k r s₁ s₀)) =
      (Module.finrank ℂ ↥(boundedJacobiSector k r s₁ s₀) : ℕ∞) := by
    rw [← Module.finrank_eq_rank ℂ ↥(boundedJacobiSector k r s₁ s₀)]
    simp
  rw [hcalc]
  have hdw : diskWeakNullity D (surfacePotential k) =
      Module.finrank ℂ ↥(@formRadical ↥D inferInstance (diskDomain_innerProductSpace D)
        (domainJacobiForm D (surfacePotential k))) := rfl
  rw [hdw]
  exact_mod_cast hle

end KsIndex.NullityDecomp
