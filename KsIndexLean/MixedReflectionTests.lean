module

public import KsIndexLean.MixedCharacterUniqueness
public import KsIndexLean.GeneralReflectionRegularity

@[expose] public section


/-!
# Mixed character tests and reflection identities

Cyclic averaging extends character testing to the entire mixed trace domain.
Odd reflection uses zero-trace test differences. Even reflection requires both
restricted tests to satisfy the mixed trace conditions. These integral identities
are separate from identifying the reflected weak derivative across a boundary arc.
-/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Surface KsIndex.FormIndex

/-- Pointwise vanishing on the Dirichlet arcs makes a smooth test admissible. -/
theorem globalSmoothH1_mem_mixedTraceDomain (k : ℕ) (b1 b0 : Bool)
    {ψ : ℂ → ℂ} (hs : ContDiff ℝ ∞ ψ)
    (h1 : b1 = false → ∀ w ∈ boundaryArc k 1, ψ (w : ℂ) = 0)
    (h0 : b0 = false → ∀ w ∈ boundaryArc k 0, ψ (w : ℂ) = 0) :
    globalSmoothH1 ψ hs ∈ mixedTraceDomain k b1 b0 := by
  constructor
  · cases b1 with
    | false => exact globalSmoothH1_zeroTrace_of_vanish (measurableSet_boundaryArc k 1) hs (h1 rfl)
    | true => trivial
  · cases b0 with
    | false => exact globalSmoothH1_zeroTrace_of_vanish (measurableSet_boundaryArc k 0) hs (h0 rfl)
    | true => trivial

/-- Inversion fixes the boundary circle, so preserves admissibility of smooth tests. -/
theorem globalSmoothH1_reflection_mem_mixedTraceDomain (k : ℕ) (b1 b0 : Bool)
    {ψ : ℂ → ℂ} (hs : ContDiff ℝ ∞ ψ)
    (hi : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (ho : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0)
    (h1 : b1 = false → ∀ w ∈ boundaryArc k 1, ψ (w : ℂ) = 0)
    (h0 : b0 = false → ∀ w ∈ boundaryArc k 0, ψ (w : ℂ) = 0) :
    globalSmoothH1 (fun z => ψ (Bracket.σ z)) (straddle_pull_smooth hs hi ho) ∈
      mixedTraceDomain k b1 b0 := by
  apply globalSmoothH1_mem_mixedTraceDomain k b1 b0
  · intro hb w hw
    rw [Bracket.σ_self (mem_sphere_zero_iff_norm.mp w.property)]
    exact h1 hb w hw
  · intro hb w hw
    rw [Bracket.σ_self (mem_sphere_zero_iff_norm.mp w.property)]
    exact h0 hb w hw

theorem mixed_character_tests_extend {k : ℕ} (hk : 0 < k) (j : ℕ)
    (b1 b0 : Bool) (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v ∈ mixedCharacterDomain k j b1 b0,
      weakJacobi (surfacePotential k) u v = 0) :
    ∀ v ∈ mixedTraceDomain k b1 b0, weakJacobi (surfacePotential k) u v = 0 :=
  surfaceJacobi_cyclic_tests_suffice hk j _
    (mixedTraceDomain_cyclic_rotation hk b1 b0) u hu hQ

theorem mixed_character_dirichlet_tests {k : ℕ} (hk : 0 < k) (j : ℕ)
    (b1 b0 : Bool) (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v ∈ mixedCharacterDomain k j b1 b0,
      weakJacobi (surfacePotential k) u v = 0) :
    ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v = 0 :=
  fun v hv => mixed_character_tests_extend hk j b1 b0 u hu hQ v
    (fullZeroTrace_le_mixed k b1 b0 hv)

theorem mixed_character_odd_reflection_halves {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (b1 b0 : Bool) (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v ∈ mixedCharacterDomain k j b1 b0,
      weakJacobi (surfacePotential k) u v = 0)
    {ψ : ℂ → ℂ} (hs : ContDiff ℝ ∞ ψ)
    (hi : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (ho : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0) :
    reflectionHalfResidual k u (-1) ψ innerHalfAnnulus +
      reflectionHalfResidual k u (-1) ψ outerHalfAnnulus = 0 := by
  apply dirichlet_radical_reflection_halves hk j u hu
    (fun v hv => hQ v ⟨fullZeroTrace_le_mixed k b1 b0 hv.1, hv.2⟩) hs hi ho

theorem mixed_character_even_reflection_halves {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (b1 b0 : Bool) (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v ∈ mixedCharacterDomain k j b1 b0,
      weakJacobi (surfacePotential k) u v = 0)
    {ψ : ℂ → ℂ} (hs : ContDiff ℝ ∞ ψ)
    (hi : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (ho : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0)
    (ht : globalSmoothH1 ψ hs ∈ mixedTraceDomain k b1 b0)
    (hr : globalSmoothH1 (fun z => ψ (Bracket.σ z))
      (straddle_pull_smooth hs hi ho) ∈ mixedTraceDomain k b1 b0) :
    reflectionHalfResidual k u 1 ψ innerHalfAnnulus +
      reflectionHalfResidual k u 1 ψ outerHalfAnnulus = 0 := by
  apply reflection_halves_of_tests hk u 1
    (mixed_character_dirichlet_tests (by omega) j b1 b0 u hu hQ) hs hi ho
  rw [mixed_character_tests_extend (by omega) j b1 b0 u hu hQ _ ht,
    mixed_character_tests_extend (by omega) j b1 b0 u hu hQ _ hr]
  simp

end KsIndex.Trace
