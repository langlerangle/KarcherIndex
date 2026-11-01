module

public import KsIndexLean.MixedReflectionTests
public import KsIndexLean.LocalReflectionBoundary

@[expose] public section


/-!
# Local classical reflection for mixed weak solutions

Odd reflection is classical on open arcs where the trace vanishes. Even
reflection is classical on open arcs disjoint from every Dirichlet arc.
The junction points are excluded from these conclusions.
-/
noncomputable section
open Set MeasureTheory
open scoped Distributions
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Surface KsIndex.FormIndex

/-- Local even-reflection tests satisfy the mixed trace restrictions. -/
lemma mixed_seam_test_admissible {k : ℕ} (b1 b0 : Bool)
    {A : Set Circle₁} (hA : IsOpen A)
    (h1 : b1 = false → Disjoint A (boundaryArc k 1))
    (h0 : b0 = false → Disjoint A (boundaryArc k 0))
    (ψ : 𝓓(seamDomain A hA, ℂ)) :
    globalSmoothH1 ψ ψ.contDiff ∈ mixedTraceDomain k b1 b0 ∧
      globalSmoothH1 (fun z => ψ (Bracket.σ z))
        (straddle_pull_smooth ψ.contDiff (seam_test_inner_zero hA ψ)
          (seam_test_outer_zero hA ψ)) ∈ mixedTraceDomain k b1 b0 := by
  have hv1 : b1 = false → ∀ w ∈ boundaryArc k 1, ψ (w : ℂ) = 0 := by
    intro hb w hw
    exact seam_test_unmatched_zero hA ψ w
      (fun ha => Set.disjoint_left.mp (h1 hb) ha hw)
  have hv0 : b0 = false → ∀ w ∈ boundaryArc k 0, ψ (w : ℂ) = 0 := by
    intro hb w hw
    exact seam_test_unmatched_zero hA ψ w
      (fun ha => Set.disjoint_left.mp (h0 hb) ha hw)
  exact ⟨globalSmoothH1_mem_mixedTraceDomain k b1 b0 ψ.contDiff hv1 hv0,
    globalSmoothH1_reflection_mem_mixedTraceDomain k b1 b0 ψ.contDiff
      (seam_test_inner_zero hA ψ) (seam_test_outer_zero hA ψ) hv1 hv0⟩

theorem mixed_odd_reflection_weak_equation {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (b1 b0 : Bool) (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v ∈ mixedCharacterDomain k j b1 b0,
      weakJacobi (surfacePotential k) u v = 0)
    {A : Set Circle₁} (hA : IsOpen A) :
    Weq.InteriorWeakEquation (seamDomain A hA)
      (fun z => joinedDiskJet u u (-1) z 1)
      (fun z => joinedDiskJet u u (-1) z Complex.I)
      (fun z => (potV k z : ℂ) * joinedDiskValue u u (-1) z) := by
  apply Weq.interiorWeakEquation_of_sesquilinear
  intro ψ
  have he := reflection_integrals_split k hk hA u (-1) ψ
  rw [mixed_character_odd_reflection_halves hk j b1 b0 u hu hQ ψ.contDiff
    (seam_test_inner_zero hA ψ) (seam_test_outer_zero hA ψ)] at he
  exact sub_eq_zero.mp he

theorem mixed_odd_reflection_classical {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (b1 b0 : Bool) (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v ∈ mixedCharacterDomain k j b1 b0,
      weakJacobi (surfacePotential k) u v = 0)
    {A : Set Circle₁} (hA : IsOpen A)
    (hzero : u ∈ zeroTraceDomain A) :
    ∃ F : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) F (seamDomain A hA : Set ℂ) ∧
      joinedDiskValue u u (-1) =ᵐ[volume.restrict (seamDomain A hA : Set ℂ)] F ∧
      ∀ z ∈ seamDomain A hA, laplacian F z + (potV k z : ℂ) * F z = 0 := by
  apply joined_classical_representative_general k hk hA u u (-1)
  · change arcTrace A u = 0 at hzero
    rw [hzero, smul_zero]
  · exact mixed_odd_reflection_weak_equation hk j b1 b0 u hu hQ hA

theorem mixed_even_reflection_weak_equation {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (b1 b0 : Bool) (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v ∈ mixedCharacterDomain k j b1 b0,
      weakJacobi (surfacePotential k) u v = 0)
    {A : Set Circle₁} (hA : IsOpen A)
    (h1 : b1 = false → Disjoint A (boundaryArc k 1))
    (h0 : b0 = false → Disjoint A (boundaryArc k 0)) :
    Weq.InteriorWeakEquation (seamDomain A hA)
      (fun z => joinedDiskJet u u 1 z 1)
      (fun z => joinedDiskJet u u 1 z Complex.I)
      (fun z => (potV k z : ℂ) * joinedDiskValue u u 1 z) := by
  apply Weq.interiorWeakEquation_of_sesquilinear
  intro ψ
  obtain ⟨ht, hr⟩ := mixed_seam_test_admissible b1 b0 hA h1 h0 ψ
  have he := reflection_integrals_split k hk hA u 1 ψ
  rw [mixed_character_even_reflection_halves hk j b1 b0 u hu hQ ψ.contDiff
    (seam_test_inner_zero hA ψ) (seam_test_outer_zero hA ψ) ht hr] at he
  exact sub_eq_zero.mp he

theorem mixed_even_reflection_classical {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (b1 b0 : Bool) (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v ∈ mixedCharacterDomain k j b1 b0,
      weakJacobi (surfacePotential k) u v = 0)
    {A : Set Circle₁} (hA : IsOpen A)
    (h1 : b1 = false → Disjoint A (boundaryArc k 1))
    (h0 : b0 = false → Disjoint A (boundaryArc k 0)) :
    ∃ F : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) F (seamDomain A hA : Set ℂ) ∧
      joinedDiskValue u u 1 =ᵐ[volume.restrict (seamDomain A hA : Set ℂ)] F ∧
      ∀ z ∈ seamDomain A hA, laplacian F z + (potV k z : ℂ) * F z = 0 := by
  apply joined_classical_representative_general k hk hA u u 1
  · exact (one_smul ℂ _).symm
  · exact mixed_even_reflection_weak_equation hk j b1 b0 u hu hQ hA h1 h0

end KsIndex.Trace
