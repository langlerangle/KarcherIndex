module

public import KsIndexLean.HemisphereWeakDomains
public import KsIndexLean.MixedCharacterPunctureRemoval

@[expose] public section


/-! Mixed trace domains and puncture removal for the canonical lower-hemisphere
Jacobi integral. Neighborhoods of the boundary punctures are expressed in the
stereographic coordinate; their vanishing condition uses spherical area. -/
noncomputable section
open Set MeasureTheory Filter
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1 KsIndex.FormIndex

/-- Mixed boundary conditions in the actual hemisphere carrier. The first
flag concerns arc 1; `true` leaves the trace unrestricted. -/
def hemisphereMixedCharacterDomain (k j : ℕ) (b1 b0 : Bool) :
    Submodule ℂ HemisphereChartSpace :=
  hemisphereDomain (mixedCharacterDomain k j b1 b0)

lemma mem_hemisphereMixedCharacterDomain (k j : ℕ) (b1 b0 : Bool)
    (u : HemisphereChartSpace) :
    u ∈ hemisphereMixedCharacterDomain k j b1 b0 ↔
      (b1 = false → (diskTraceCLM (hemisphereCoordinates u) : Circle₁ → ℂ)
        =ᵐ[circleMeasure.restrict (boundaryArc k 1)] 0) ∧
      (b0 = false → (diskTraceCLM (hemisphereCoordinates u) : Circle₁ → ℂ)
        =ᵐ[circleMeasure.restrict (boundaryArc k 0)] 0) ∧
      (fun p => hemisphereValue u (rotateSphere (-(2 * Real.pi) / k) p))
        =ᵐ[(volume : Measure Ambient).toSphere.restrict {p : Sphere | p.val 2 < 0}]
      (fun p => zeta k ^ j * hemisphereValue u p) := by
  rw [← hemisphere_character_iff]
  change ((hemisphereCoordinates u ∈ naturalArcDomain k 1 b1) ∧
    (hemisphereCoordinates u ∈ naturalArcDomain k 0 b0)) ∧
    (hemisphereCoordinates u ∈ weakCharacterDomain _ _) ↔ _
  rw [mem_naturalArcDomain, mem_naturalArcDomain, and_assoc]

/-- Stereographic coordinates preserve arbitrary almost-everywhere predicates
between disk area and canonical lower-hemisphere area. -/
lemma hemisphere_ae_iff (P : Sphere → Prop) :
    (∀ᵐ p ∂(volume : Measure Ambient).toSphere.restrict {p : Sphere | p.val 2 < 0}, P p) ↔
      ∀ᵐ z ∂volume.restrict (disk : Set ℂ), P (sphereChart z) := by
  rw [← sphereChart_disk_eq_lower, canonicalArea_restrict,
    Set.preimage_image_eq _ sphereChart_injective]
  rw [measurableEmbedding_sphereChart.ae_map_iff]
  rw [ae_restrict_iff' disk.isOpen.measurableSet, ae_stereoAreaMeasure_iff]
  exact (ae_restrict_iff' disk.isOpen.measurableSet).symm

/-- A hemisphere weak field vanishes on a stereographic neighborhood of every
boundary puncture, almost everywhere for canonical spherical area. -/
def HemisphereVanishesNearPunctures (k : ℕ) (u : HemisphereChartSpace) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧
    ∀ᵐ q ∂(volume : Measure Ambient).toSphere.restrict {q : Sphere | q.val 2 < 0},
      (∃ p ∈ Surface.punctures k, ‖stereoCoord q.val - p‖ ≤ ρ) → hemisphereValue u q = 0

lemma hemisphereVanishesNearPunctures_iff (k : ℕ) (u : HemisphereChartSpace) :
    HemisphereVanishesNearPunctures k u ↔
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ᵐ z ∂volume.restrict disk,
        (∃ p ∈ Surface.punctures k, ‖z - p‖ ≤ ρ) →
          valueCLM (hemisphereCoordinates u) z = 0 := by
  simp only [HemisphereVanishesNearPunctures, hemisphere_ae_iff,
    hemisphereValue, sphereWeakValue, sphereChart, stereoCoord_stereoPoint]

/-- Tests supported away from the boundary punctures determine the entire
mixed weak Jacobi equation on the lower hemisphere. In particular, flags
`true, false` give the paper's Dirichlet-on-arc-0 domain. -/
theorem hemisphereMixed_puncture_removal {k : ℕ} (hk : 1 ≤ k)
    (j : ℕ) (b1 b0 : Bool) (V : BoundedRealPotential) (u : HemisphereChartSpace)
    (h : ∀ v : hemisphereMixedCharacterDomain k j b1 b0,
      HemisphereVanishesNearPunctures k v.val → hemisphereJacobi V u v.val = 0)
    (v : hemisphereMixedCharacterDomain k j b1 b0) : hemisphereJacobi V u v.val = 0 := by
  rw [hemisphereJacobi_eq]
  apply mixedCharacter_puncture_removal hk j b1 b0 V (hemisphereCoordinates u)
    (v := ⟨hemisphereCoordinates v.val, v.property⟩)
  intro w hw
  let w' := hemisphereDomainEquiv (mixedCharacterDomain k j b1 b0) w
  have hc : hemisphereCoordinates w'.val = w.val :=
    hemisphereCoordinates.apply_symm_apply w.val
  have hz : HemisphereVanishesNearPunctures k w'.val := by
    rw [hemisphereVanishesNearPunctures_iff, hc]
    exact hw
  simpa only [hemisphereJacobi_eq, hc] using h w' hz

end KsIndex.Spherical
