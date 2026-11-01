module

public import KsIndexLean.GeneralReflectionAnnulus
public import KsIndexLean.PaperSeamClassical

@[expose] public section


/-!
# Classical odd and even reflections of weak radical vectors

The input is the actual character-restricted weak radical condition.
Full tests, the joined weak equation, and the smooth classical representative
are derived here. No boundary regularity hypothesis is assumed.
-/
noncomputable section
open Set MeasureTheory
open scoped Distributions
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Surface KsIndex.FormIndex

lemma reflection_integrals_split (k : ℕ) (hk : 2 ≤ k) {A : Set Circle₁} (hA : IsOpen A)
    (u : ComplexH1) (c : ℂ) (ψ : 𝓓(seamDomain A hA, ℂ)) :
    (∫ z, jetPairing (joinedDiskJet u u c) ψ z) -
      (∫ z, (potV k z : ℂ) * starRingEnd ℂ (joinedDiskValue u u c z) * ψ z) =
    reflectionHalfResidual k u c ψ innerHalfAnnulus +
      reflectionHalfResidual k u c ψ outerHalfAnnulus := by
  have hz (z : ℂ) (hn : z ∉ annulusSet (1 / 2 : ℝ) 2) : z ∉ seamDomain A hA :=
    fun h => hn h.1
  have hJ := integral_split_of_annular_support
    (joined_jet_test_integrable hA u u c ψ).integrableOn
    (fun z hn => by
      have hx := seam_test_zero_of_not_mem hA (Weq.derivTest ψ 1) (hz z hn)
      have hy := seam_test_zero_of_not_mem hA (Weq.derivTest ψ Complex.I) (hz z hn)
      change fderiv ℝ (ψ : ℂ → ℂ) z 1 = 0 at hx
      change fderiv ℝ (ψ : ℂ → ℂ) z Complex.I = 0 at hy
      simp only [jetPairing, hx, hy, mul_zero, add_zero])
  have hV := integral_split_of_annular_support
    (joined_potential_test_integrable_general k hk hA u u c ψ).integrableOn
    (fun z hn => by rw [seam_test_zero_of_not_mem hA ψ (hz z hn), mul_zero])
  rw [hJ, hV]
  unfold reflectionHalfResidual
  ring


/-- The odd reflection of a Dirichlet character radical solves the weak
Jacobi equation across the whole unit circle. -/
theorem dirichlet_radical_reflection_weak_equation {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ ⊓
      weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) →
      weakJacobi (surfacePotential k) u v = 0) :
    Weq.InteriorWeakEquation (seamDomain Set.univ isOpen_univ)
      (fun z => joinedDiskJet u u (-1) z 1)
      (fun z => joinedDiskJet u u (-1) z Complex.I)
      (fun z => (potV k z : ℂ) * joinedDiskValue u u (-1) z) := by
  apply Weq.interiorWeakEquation_of_sesquilinear
  intro ψ
  have he := reflection_integrals_split k hk isOpen_univ u (-1) ψ
  rw [dirichlet_radical_reflection_halves hk j u hu hQ ψ.contDiff
    (seam_test_inner_zero _ ψ) (seam_test_outer_zero _ ψ)] at he
  exact sub_eq_zero.mp he

/-- The even reflection of a Neumann character radical solves the weak
Jacobi equation across the whole unit circle. -/
theorem neumann_radical_reflection_weak_equation {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v : ComplexH1,
      v ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) →
      weakJacobi (surfacePotential k) u v = 0) :
    Weq.InteriorWeakEquation (seamDomain Set.univ isOpen_univ)
      (fun z => joinedDiskJet u u 1 z 1)
      (fun z => joinedDiskJet u u 1 z Complex.I)
      (fun z => (potV k z : ℂ) * joinedDiskValue u u 1 z) := by
  apply Weq.interiorWeakEquation_of_sesquilinear
  intro ψ
  have he := reflection_integrals_split k hk isOpen_univ u 1 ψ
  rw [neumann_radical_reflection_halves hk j u hu hQ ψ.contDiff
    (seam_test_inner_zero _ ψ) (seam_test_outer_zero _ ψ)] at he
  exact sub_eq_zero.mp he

/-- The Dirichlet radical yields a smooth classical odd-reflected field. -/
theorem dirichlet_radical_reflection_classical {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (u : ComplexH1) (hzero : u ∈ zeroTraceDomain Set.univ)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ ⊓
      weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) →
      weakJacobi (surfacePotential k) u v = 0) :
    ∃ F : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) F
        (seamDomain Set.univ isOpen_univ : Set ℂ) ∧
      joinedDiskValue u u (-1) =ᵐ[volume.restrict
        (seamDomain Set.univ isOpen_univ : Set ℂ)] F ∧
      ∀ z ∈ seamDomain Set.univ isOpen_univ,
        laplacian F z + (potV k z : ℂ) * F z = 0 := by
  apply joined_classical_representative_general k hk isOpen_univ u u (-1)
  · change arcTrace Set.univ u = 0 at hzero
    rw [hzero, smul_zero]
  · exact dirichlet_radical_reflection_weak_equation hk j u hu hQ

/-- The Neumann radical yields a smooth classical even-reflected field. -/
theorem neumann_radical_reflection_classical {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v : ComplexH1,
      v ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) →
      weakJacobi (surfacePotential k) u v = 0) :
    ∃ F : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) F
        (seamDomain Set.univ isOpen_univ : Set ℂ) ∧
      joinedDiskValue u u 1 =ᵐ[volume.restrict
        (seamDomain Set.univ isOpen_univ : Set ℂ)] F ∧
      ∀ z ∈ seamDomain Set.univ isOpen_univ,
        laplacian F z + (potV k z : ℂ) * F z = 0 := by
  apply joined_classical_representative_general k hk isOpen_univ u u 1
  · exact (one_smul ℂ _).symm
  · exact neumann_radical_reflection_weak_equation hk j u hu hQ

end KsIndex.Trace
