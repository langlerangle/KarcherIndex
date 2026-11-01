module

public import KsIndexLean.PaperSlitInteriorSmooth
public import KsIndexLean.GeneralReflectionTests
public import KsIndexLean.GeneralRadicalRegularity
public import KsIndexLean.SeamStraddleIdentity
public import KsIndexLean.JoinedSeamPairing

@[expose] public section


/-!
# Annular weak identities for reflected radical vectors

The field is represented by its actual joined Sobolev value and jet.
Interior regularity and derivative identification are derived from the
full Dirichlet test equation, rather than assumed at the boundary.
-/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Surface KsIndex.PaperSlitTransport KsIndex.FormIndex

/-- The Jacobi residual of a field joined to its own reflected multiple. -/
def reflectionHalfResidual (k : ℕ) (u : ComplexH1) (c : ℂ)
    (ψ : ℂ → ℂ) (s : Set ℂ) : ℂ :=
  (∫ z in s, jetPairing (joinedDiskJet u u c) ψ z) -
    ∫ z in s, (potV k z : ℂ) * starRingEnd ℂ (joinedDiskValue u u c z) * ψ z

/-- A reflected test identity converts to the two actual half-annulus
integrals. No classical representative is supplied by the caller. -/
theorem reflection_halves_of_tests {k : ℕ} (hk : 2 ≤ k)
    (u : ComplexH1) (c : ℂ)
    (hD : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v = 0)
    {ψ : ℂ → ℂ} (hs : ContDiff ℝ ∞ ψ)
    (hi : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (ho : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0)
    (ht : weakJacobi (surfacePotential k) u (globalSmoothH1 ψ hs) +
      starRingEnd ℂ c * weakJacobi (surfacePotential k) u
        (globalSmoothH1 (fun z => ψ (Bracket.σ z)) (straddle_pull_smooth hs hi ho)) = 0) :
    reflectionHalfResidual k u c ψ innerHalfAnnulus +
      reflectionHalfResidual k u c ψ outerHalfAnnulus = 0 := by
  obtain ⟨f, hf, ha, _⟩ := Weq.fullDirichlet_tests_classical hk u hD
  obtain ⟨hfx, hfy⟩ := Weq.disk_smooth_representative_derivatives u hf ha
  have hsub : innerHalfAnnulus ⊆ (WeakH1.disk : Set ℂ) := by
    intro z hz
    exact Metric.mem_ball.mpr (by simpa only [dist_zero_right] using hz.2)
  have hm := ae_mono (Measure.restrict_mono (μ := (volume : Measure ℂ)) hsub le_rfl)
  rw [weakJacobi_inner_localized_general k u hs (fun z hz => hi z hz.le)
    (ha.filter_mono hm) (hfx.filter_mono hm) (hfy.filter_mono hm)] at ht
  rw [weakJacobi_straddle_outer_rep_general k hk u hs hi ho
    (fun z hz => (hf.contDiffAt (WeakH1.disk.isOpen.mem_nhds (hsub hz))).differentiableAt (by simp))
    (ha.filter_mono hm) (hfx.filter_mono hm) (hfy.filter_mono hm)] at ht
  unfold reflectionHalfResidual
  rw [joined_pairing_inner_general k u u c hf ha,
    joined_pairing_outer_general k u u c hf ha]
  exact ht

/-- Actual Dirichlet character radicals satisfy the odd-reflection identity. -/
theorem dirichlet_radical_reflection_halves {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ ⊓
      weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) →
      weakJacobi (surfacePotential k) u v = 0)
    {ψ : ℂ → ℂ} (hs : ContDiff ℝ ∞ ψ)
    (hi : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (ho : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0) :
    reflectionHalfResidual k u (-1) ψ innerHalfAnnulus +
      reflectionHalfResidual k u (-1) ψ outerHalfAnnulus = 0 := by
  apply reflection_halves_of_tests hk u (-1)
    (generalDirichlet_character_tests_extend (by omega) j u hu hQ) hs hi ho
  simpa only [map_neg, map_one, neg_one_mul, sub_eq_add_neg] using
    dirichlet_radical_straddle_tests (by omega) j u hu hQ hs hi ho

/-- Actual Neumann character radicals satisfy the even-reflection identity. -/
theorem neumann_radical_reflection_halves {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v : ComplexH1,
      v ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) →
      weakJacobi (surfacePotential k) u v = 0)
    {ψ : ℂ → ℂ} (hs : ContDiff ℝ ∞ ψ)
    (hi : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (ho : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0) :
    reflectionHalfResidual k u 1 ψ innerHalfAnnulus +
      reflectionHalfResidual k u 1 ψ outerHalfAnnulus = 0 := by
  apply reflection_halves_of_tests hk u 1
    (fun v _ => generalNeumann_character_tests_extend (by omega) j u hu hQ v) hs hi ho
  simpa only [map_one, one_mul] using
    neumann_radical_straddle_tests (by omega) j u hu hQ hs hi ho

end KsIndex.Trace
