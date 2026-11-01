module

public import KsIndexLean.BoundarySmoothCore
public import KsIndexLean.FiniteMollificationHoles

@[expose] public section


open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket KsIndex.WeakH1 KsIndex.SingleDisk

/-- Support exclusion removes the inversion singularity from the actual averaged function. -/
lemma reflectionAverage_smooth_of_zero_not_support (s : ℂ) {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (h0 : (0 : ℂ) ∉ tsupport (reflectionAverage s f)) :
    ContDiff ℝ ∞ (reflectionAverage s f) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    have he : reflectionAverage s f =ᶠ[𝓝 (0 : ℂ)] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp h0
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact reflectionAverage_contDiffAt s hz hf.contDiffAt hf.contDiffAt

/-- Actual reflected mollifiers of an arc-1 piece eventually satisfy the exact paper core. -/
theorem seam1_mollifier_reflected_core {k : ℕ} (hk : 1 ≤ k) (s1 s0 : ℂ)
    (hs1 : s1 ^ 2 = 1) {u : ℂ → ℂ} (hu : MemLp u 2 volume)
    (hc : HasCompactSupport u)
    (hs : tsupport u ⊆ seamDomain (boundaryArc k 1) (isOpen_boundaryArc k 1))
    (hP : ∀ p ∈ KsIndex.Surface.punctures k, ∃ R : ℝ, 0 < R ∧
      ∀ᵐ w ∂volume, dist w p < R → u w = 0) :
    ∀ᶠ n in atTop, KsIndex.TwistSwap.IsSmoothR k s1 s0
      (closedDiskRestriction (reflectionAverage s1 (compactMollify (shrinkingMollifier n) u))) := by
  filter_upwards [reflected_mollifier_support_seam s1 (isOpen_boundaryArc k 1) hc hs,
    reflected_mollifier_suppAwayP1 k hk s1 hP] with n hn hp
  apply seam1_smooth_reflected_core k s1 s0 _ hn
    (reflectionAverage_parity s1 hs1 _) hp
  exact reflectionAverage_smooth_of_zero_not_support s1 (compactMollify_smooth _ hu)
    (fun h => zero_notMem_seamDomain (isOpen_boundaryArc k 1) (hn h))

/-- Actual reflected mollifiers of an arc-0 piece eventually satisfy the exact paper core. -/
theorem seam0_mollifier_reflected_core {k : ℕ} (hk : 1 ≤ k) (s1 s0 : ℂ)
    (hs0 : s0 ^ 2 = 1) {u : ℂ → ℂ} (hu : MemLp u 2 volume)
    (hc : HasCompactSupport u)
    (hs : tsupport u ⊆ seamDomain (boundaryArc k 0) (isOpen_boundaryArc k 0))
    (hP : ∀ p ∈ KsIndex.Surface.punctures k, ∃ R : ℝ, 0 < R ∧
      ∀ᵐ w ∂volume, dist w p < R → u w = 0) :
    ∀ᶠ n in atTop, KsIndex.TwistSwap.IsSmoothR k s1 s0
      (closedDiskRestriction (reflectionAverage s0 (compactMollify (shrinkingMollifier n) u))) := by
  filter_upwards [reflected_mollifier_support_seam s0 (isOpen_boundaryArc k 0) hc hs,
    reflected_mollifier_suppAwayP1 k hk s0 hP] with n hn hp
  apply seam0_smooth_reflected_core k s1 s0 _ hn
    (reflectionAverage_parity s0 hs0 _) hp
  exact reflectionAverage_smooth_of_zero_not_support s0 (compactMollify_smooth _ hu)
    (fun h => zero_notMem_seamDomain (isOpen_boundaryArc k 0) (hn h))

end KsIndex.Trace
