module

public import KsIndexLean.GeneralDiskClassical
public import KsIndexLean.PaperSlitTestTransport
public import KsIndexLean.GeneralCharacterTestExtension
public import KsIndexLean.GeneralDirichletRegularityBase

@[expose] public section


/-!
# Interior classical representatives from full weak Dirichlet testing

The full test equation implies both real weak equations, then supplies a
single smooth representative on the disk. Character testing is upgraded
by cyclic averaging before applying the interior theorem.
-/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Weq
open KsIndex.Trace KsIndex.WeakH1 KsIndex.PaperSlitTransport KsIndex.FormIndex

theorem characterDirichlet_tests_classical {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v ∈ zeroTraceDomain Set.univ ⊓
      weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j),
      weakJacobi (surfacePotential k) u v = 0) :
    ∃ f : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) f (disk : Set ℂ) ∧
      valueCLM u =ᵐ[volume.restrict (disk : Set ℂ)] f ∧
      ∀ z ∈ (disk : Set ℂ), Surface.laplacian f z + (Surface.potV k z : ℂ) * f z = 0 :=
  fullDirichlet_tests_classical hk u
    (generalDirichlet_character_tests_extend (by omega) j u hu hQ)

/-- The actual mixed-boundary character radical has a smooth classical interior representative. -/
theorem mixedCharacter_radical_classical {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (b1 b0 : Bool) (u : mixedCharacterDomain k j b1 b0)
    (hQ : ∀ v : mixedCharacterDomain k j b1 b0,
      weakJacobi (surfacePotential k) u v = 0) :
    ∃ f : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) f (disk : Set ℂ) ∧
      valueCLM u =ᵐ[volume.restrict (disk : Set ℂ)] f ∧
      ∀ z ∈ (disk : Set ℂ), Surface.laplacian f z + (Surface.potV k z : ℂ) * f z = 0 := by
  apply characterDirichlet_tests_classical hk j u u.property.2
  intro v hv
  have ht : diskTraceCLM v = 0 := (mem_fullZeroTrace_iff v).mp hv.1
  have hz (A : Set Circle₁) : v ∈ zeroTraceDomain A := by
    change arcTrace A v = 0
    simp only [arcTrace, ContinuousLinearMap.comp_apply, ht, map_zero]
  have ha (n : ℕ) (b : Bool) : v ∈ naturalArcDomain k n b := by
    cases b
    · exact hz _
    · exact Submodule.mem_top
  exact hQ ⟨v, ⟨⟨ha 1 b1, ha 0 b0⟩, hv.2⟩⟩

end KsIndex.Weq
