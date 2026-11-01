module

public import KsIndexLean.A1PunctureWiring
public import KsIndexLean.ReflectedWeakLocalization
public import KsIndexLean.BoundaryMollifierCore

@[expose] public section


/-!
# Smooth-core membership for a localized reflected field

For `k ≥ 1`, a field `u : ComplexH1` with the prescribed arc-1 trace symmetry
and almost-everywhere vanishing in a fixed neighborhood of the punctures is
localized by a smooth, compactly supported, reflection-invariant cutoff `χ`
whose support lies in the seam domain. The resulting whole-plane field
`v = χ • joinedDiskValue u u s` has square-integrable values, compact support,
and an almost-everywhere vanishing neighborhood of each puncture.

`reflected_piece_seam1_core` combines these facts with
`seam1_mollifier_reflected_core`: for all sufficiently large indices, the
closed-disk restriction of the mollified, reflection-averaged field belongs to
`IsSmoothR k s s0`. This theorem asserts eventual core membership; it does not
assert convergence of the approximants. The separate variable `v` and equality
`hvdef` keep the composite field from unfolding during elaboration.
-/

open Set MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket

/-- With `s² = 1`, the arc-1 trace symmetry, puncture vanishing and the stated
cutoff conditions, the mollified reflected average of `v = χ • joinedDiskValue u u s`
eventually belongs to `IsSmoothR k s s0`. The parameter `s0` is unrestricted here. -/
theorem reflected_piece_seam1_core {k : ℕ} (hk : 1 ≤ k) (u : ComplexH1) (s s0 : ℂ)
    (hsign : s ^ 2 = 1)
    (hm : arcTrace (boundaryArc k 1) u = s • arcTrace (boundaryArc k 1) u)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hvz : ∀ᵐ z ∂volume.restrict (disk : Set ℂ),
      (∃ p ∈ Surface.punctures k, ‖z - p‖ ≤ ρ) → valueCLM u z = 0)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (seamDomain (boundaryArc k 1) (isOpen_boundaryArc k 1) : Set ℂ))
    (hi : ∀ z, χ (σ z) = χ z)
    (v : ℂ → ℂ) (hvdef : v = fun z => χ z • joinedDiskValue u u s z) :
    ∀ᶠ n in atTop, KsIndex.TwistSwap.IsSmoothR k s s0
      (closedDiskRestriction (reflectionAverage s
        (compactMollify (shrinkingMollifier n) v))) := by
  -- Use the value-integrability component of reflected localization.
  obtain ⟨_, hvmem0, _, _, _⟩ :=
    reflected_weak_localization (isOpen_boundaryArc k 1) u s hsign hm hχ hc hs hi
  have hvmem : MemLp v 2 volume := by rw [hvdef]; exact hvmem0
  -- Compact support follows from the cutoff.
  have hvc : HasCompactSupport v := by rw [hvdef]; exact hc.smul_right
  -- seam-domain support: tsupport v ⊆ tsupport χ ⊆ seamDomain
  have hvs : tsupport v ⊆ (seamDomain (boundaryArc k 1) (isOpen_boundaryArc k 1) : Set ℂ) := by
    rw [hvdef]; exact (tsupport_smul_subset_left χ _).trans hs
  -- Multiplication by the cutoff preserves puncture vanishing.
  have hvP : ∀ p ∈ Surface.punctures k, ∃ R : ℝ, 0 < R ∧
      ∀ᵐ w ∂(volume : Measure ℂ), dist w p < R → v w = 0 := by
    intro p hp
    obtain ⟨R, hR, hRz⟩ := joinedDiskValue_puncture_hP hk hρ hvz s p hp
    refine ⟨R, hR, ?_⟩
    filter_upwards [hRz] with w hw hwp
    rw [hvdef]
    simp only [hw hwp, smul_zero]
  -- Apply the seam-1 reflected mollifier theorem to the named field v.
  exact seam1_mollifier_reflected_core hk s s0 hsign hvmem hvc hvs hvP

end KsIndex.Trace
