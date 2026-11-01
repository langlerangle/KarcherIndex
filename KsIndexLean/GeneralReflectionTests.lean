module

public import KsIndexLean.GeneralCharacterTestExtension
public import KsIndexLean.SeamStraddleTest

@[expose] public section


/-!
# Full boundary tests for odd and even reflection

Cyclic character testing is extended before using arbitrary smooth tests
that straddle the unit circle. The odd test difference has zero trace
because inversion fixes the circle pointwise. The even test sum is
admissible in the unrestricted Neumann form domain.
-/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.FormIndex

/-- Neumann character testing implies testing against every H¹ function. -/
lemma generalNeumann_character_tests_extend {k : ℕ} (hk : 0 < k) (j : ℕ)
    (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v : ComplexH1,
      v ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) →
      weakJacobi (surfacePotential k) u v = 0) :
    ∀ v : ComplexH1, weakJacobi (surfacePotential k) u v = 0 := by
  have h := surfaceJacobi_cyclic_tests_suffice hk j (⊤ : Submodule ℂ ComplexH1)
    (fun _ _ => Submodule.mem_top) u hu (fun v hv => hQ v hv.2)
  exact fun v => h v Submodule.mem_top

/-- The inner test minus its inverted outer half has zero full boundary trace. -/
lemma straddle_difference_zeroTrace {ψ : ℂ → ℂ} (hs : ContDiff ℝ ∞ ψ)
    (hi : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (ho : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0) :
    globalSmoothH1 ψ hs -
      globalSmoothH1 (fun z => ψ (Bracket.σ z)) (straddle_pull_smooth hs hi ho) ∈
      zeroTraceDomain Set.univ := by
  change arcTrace Set.univ (_ - _) = 0
  rw [map_sub, sub_eq_zero]
  apply globalSmoothH1_arcTrace_congr Set.univ hs (straddle_pull_smooth hs hi ho)
  intro w
  rw [Bracket.σ_self (mem_sphere_zero_iff_norm.mp w.property)]

/-- The odd-reflection test identity follows from the actual Dirichlet
character radical; the test itself need not belong to a character space. -/
theorem dirichlet_radical_straddle_tests {k : ℕ} (hk : 0 < k) (j : ℕ)
    (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ ⊓
      weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) →
      weakJacobi (surfacePotential k) u v = 0)
    {ψ : ℂ → ℂ} (hs : ContDiff ℝ ∞ ψ)
    (hi : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (ho : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0) :
    weakJacobi (surfacePotential k) u (globalSmoothH1 ψ hs) -
      weakJacobi (surfacePotential k) u
        (globalSmoothH1 (fun z => ψ (Bracket.σ z)) (straddle_pull_smooth hs hi ho)) = 0 := by
  have h := generalDirichlet_character_tests_extend hk j u hu hQ _
    (straddle_difference_zeroTrace hs hi ho)
  rw [sub_eq_add_neg, show -globalSmoothH1 (fun z => ψ (Bracket.σ z))
      (straddle_pull_smooth hs hi ho) = (-1 : ℂ) •
      globalSmoothH1 (fun z => ψ (Bracket.σ z))
        (straddle_pull_smooth hs hi ho) by simp,
    weakJacobi_add_right, weakJacobi_smul_right] at h
  simpa only [neg_one_mul, sub_eq_add_neg] using h

/-- The even-reflection test identity follows from the actual Neumann
character radical. No boundary trace constraint is imposed on the test. -/
theorem neumann_radical_straddle_tests {k : ℕ} (hk : 0 < k) (j : ℕ)
    (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v : ComplexH1,
      v ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) →
      weakJacobi (surfacePotential k) u v = 0)
    {ψ : ℂ → ℂ} (hs : ContDiff ℝ ∞ ψ)
    (hi : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (ho : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0) :
    weakJacobi (surfacePotential k) u (globalSmoothH1 ψ hs) +
      weakJacobi (surfacePotential k) u
        (globalSmoothH1 (fun z => ψ (Bracket.σ z)) (straddle_pull_smooth hs hi ho)) = 0 := by
  rw [generalNeumann_character_tests_extend hk j u hu hQ,
    generalNeumann_character_tests_extend hk j u hu hQ, add_zero]

end KsIndex.Trace
