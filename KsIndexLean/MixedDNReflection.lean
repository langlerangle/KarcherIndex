module

public import KsIndexLean.MixedReflectionRegularity
public import KsIndexLean.PuncturedBoundaryPartition

@[expose] public section


/-! Local smooth representatives and boundary conditions for the paper's DN radical.
Arc 0 is Dirichlet and arc 1 is Neumann. No assertion at the junctions is made. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Surface KsIndex.FormIndex

theorem dn_radical_dirichlet_arc_classical {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (u : ComplexH1) (hu : u ∈ mixedCharacterDomain k j true false)
    (hQ : ∀ v ∈ mixedCharacterDomain k j true false,
      weakJacobi (surfacePotential k) u v = 0) :
    ∃ F : ℂ → ℂ,
      ContDiffOn ℝ (⊤ : ℕ∞) F
        (seamDomain (boundaryArc k 0) (isOpen_boundaryArc k 0) : Set ℂ) ∧
      joinedDiskValue u u (-1) =ᵐ[volume.restrict
        (seamDomain (boundaryArc k 0) (isOpen_boundaryArc k 0) : Set ℂ)] F ∧
      (∀ z ∈ seamDomain (boundaryArc k 0) (isOpen_boundaryArc k 0),
        laplacian F z + (potV k z : ℂ) * F z = 0) ∧
      ∀ z ∈ arc k 0, F z = 0 := by
  obtain ⟨F, hF, ha, he⟩ := mixed_odd_reflection_classical hk j true false u hu.2 hQ
    (isOpen_boundaryArc k 0) hu.1.2
  refine ⟨F, hF, ha, he, ?_⟩
  intro z hz
  exact odd_joined_boundary_zero_on (isOpen_boundaryArc k 0) u hF.continuousOn ha
    hz.1 (arc_mem_seamDomain hz)

theorem dn_radical_neumann_arc_classical {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (u : ComplexH1) (hu : u ∈ mixedCharacterDomain k j true false)
    (hQ : ∀ v ∈ mixedCharacterDomain k j true false,
      weakJacobi (surfacePotential k) u v = 0) :
    ∃ F : ℂ → ℂ,
      ContDiffOn ℝ (⊤ : ℕ∞) F
        (seamDomain (boundaryArc k 1) (isOpen_boundaryArc k 1) : Set ℂ) ∧
      joinedDiskValue u u 1 =ᵐ[volume.restrict
        (seamDomain (boundaryArc k 1) (isOpen_boundaryArc k 1) : Set ℂ)] F ∧
      (∀ z ∈ seamDomain (boundaryArc k 1) (isOpen_boundaryArc k 1),
        laplacian F z + (potV k z : ℂ) * F z = 0) ∧
      ∀ z ∈ arc k 1, fderiv ℝ F z z = 0 := by
  obtain ⟨F, hF, ha, he⟩ := mixed_even_reflection_classical hk j true false u hu.2 hQ
    (isOpen_boundaryArc k 1) (by simp) (fun _ => (boundaryArc_disjoint k).symm)
  refine ⟨F, hF, ha, he, ?_⟩
  intro z hz
  exact even_joined_boundary_normal_zero_on (isOpen_boundaryArc k 1) u hF ha
    hz.1 (arc_mem_seamDomain hz)

end KsIndex.Trace
