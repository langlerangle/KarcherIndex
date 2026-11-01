module

public import KsIndexLean.FiniteWeakPartition

@[expose] public section


/-!
# Zero extension across an arc with zero trace

For `u : ComplexH1`, `joinedDiskValue u 0 0` agrees with `valueCLM u` on
the closed unit disk and is zero outside. If the trace of `u` vanishes on
an open set `A` of the circle, `zero_join_weak_gluing` supplies its weak
derivative on `seamDomain A hA` by specializing the seam-gluing theorem.

A globally smooth real cutoff with compact support contained in that seam
domain yields a whole-plane localized function with L² value and directional
weak derivatives. Its derivative is the full product-rule expression
`χ • joinedDiskJet + (Dχ).smulRight joinedDiskValue`, including the derivative
of the cutoff. No reflection invariance or parity assumption is required.
The final lemmas establish pointwise vanishing of both localized value and
jet outside the closed disk.
-/

open Set MeasureTheory TopologicalSpace
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket

/-- The zero join vanishes identically outside the closed disk. -/
lemma joinedDiskValue_zero_of_one_lt (u : ComplexH1) {z : ℂ}
    (hz : 1 < ‖z‖) : joinedDiskValue u 0 0 z = 0 := by
  simp [joinedDiskValue, radialJoin, ite_eq_right (not_le.mpr hz)]

/-- The zero join's jet vanishes identically outside the closed disk: both
polar component fields die on the outside branch (`0 • _`), and the
Cartesian reconstruction is pointwise linear in them. -/
lemma joinedDiskJet_zero_of_one_lt (u : ComplexH1) {z : ℂ}
    (hz : 1 < ‖z‖) : joinedDiskJet u 0 0 z = 0 := by
  have hr : joinedDiskRadial u 0 0 z = 0 := by
    simp [joinedDiskRadial, radialJoin, ite_eq_right (not_le.mpr hz)]
  have ha : joinedDiskAngular u 0 0 z = 0 := by
    simp [joinedDiskAngular, radialJoin, ite_eq_right (not_le.mpr hz)]
  simp [joinedDiskJet, reconstructedJet, reconstructedX, reconstructedY, hr, ha]

/-- On the closed disk the zero join is the original carrier. -/
lemma joinedDiskValue_zero_of_le_one (u : ComplexH1) {z : ℂ}
    (hz : ‖z‖ ≤ 1) : joinedDiskValue u 0 0 z = valueCLM u z := by
  simp only [joinedDiskValue, radialJoin, ite_eq_left hz]

/-- Trace-zero rewrites to the gluing hypothesis at `v = 0`, `c = 0`. -/
lemma arcTrace_zero_join_hyp {A : Set Circle₁} {u : ComplexH1}
    (hm : arcTrace A u = 0) :
    arcTrace A u = (0 : ℂ) • arcTrace A (0 : ComplexH1) := by
  simpa using hm

/-- For an open circle set `A` and zero trace on `A`, the zero join has the
specified weak derivative on the seam domain. -/
theorem zero_join_weak_gluing {A : Set Circle₁} (hA : IsOpen A)
    (u : ComplexH1) (hm : arcTrace A u = 0) :
    TauCeti.HasWeakFDerivOn volume (seamDomain A hA)
      (joinedDiskValue u 0 0) (joinedDiskJet u 0 0) :=
  seamDomain_weak_gluing hA u 0 0 (arcTrace_zero_join_hyp hm)

/-- A smooth, compactly supported cutoff whose support lies in the seam domain
produces a whole-plane weak derivative, an L² value and L² derivatives in every
direction. The derivative includes both terms of the product rule. -/
theorem zero_join_weak_localization {A : Set Circle₁} (hA : IsOpen A)
    (u : ComplexH1) (hm : arcTrace A u = 0) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (seamDomain A hA : Set ℂ)) :
    let v := fun z => χ z • joinedDiskValue u 0 0 z
    let J := fun z => χ z • joinedDiskJet u 0 0 z +
      (fderiv ℝ χ z).smulRight (joinedDiskValue u 0 0 z)
    TauCeti.HasWeakFDerivOn volume ⊤ v J ∧ MemLp v 2 volume ∧
      (∀ d, MemLp (fun z => J z d) 2 volume) := by
  dsimp only
  have hL d : MemLp (fun z => joinedDiskJet u 0 0 z d) 2
      (volume.restrict (seamDomain A hA : Set ℂ)) :=
    (seamDomain_jet_memLp hA u 0 0).continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ ℂ d)
  exact weakH1_localization hχ hc hs (zero_join_weak_gluing hA u hm)
    (seamDomain_value_memLp hA u 0 0) hL

/-- The localized zero-extended piece vanishes outside the closed disk —
the pointwise fact the dilation step will push into an in-disk neighborhood
of the arc. -/
lemma localized_zero_join_vanish (u : ComplexH1) (χ : ℂ → ℝ) {z : ℂ}
    (hz : 1 < ‖z‖) : χ z • joinedDiskValue u 0 0 z = 0 := by
  rw [joinedDiskValue_zero_of_one_lt u hz, smul_zero]

/-- The localized jet vanishes outside the closed disk. -/
lemma localized_zero_join_jet_vanish (u : ComplexH1) (χ : ℂ → ℝ)
    {z : ℂ} (hz : 1 < ‖z‖) :
    χ z • joinedDiskJet u 0 0 z +
      (fderiv ℝ χ z).smulRight (joinedDiskValue u 0 0 z) = 0 := by
  rw [joinedDiskJet_zero_of_one_lt u hz, joinedDiskValue_zero_of_one_lt u hz]
  simp

end KsIndex.Trace
