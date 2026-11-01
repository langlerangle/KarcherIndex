module

public import KsIndexLean.BoundaryMollifierCore
public import KsIndexLean.SingleCcSlitClearance

@[expose] public section


/-!
# Reflected arc-1 approximants in the single-disk core

The reflected mollifier core supplies four of the six `IsSmoothS` conditions.
For the arc-0 condition, the smooth averaged function gives a one-sided
extension when `b₀ = true`, while `suppAwaySlit1_of_seam1_support` gives slit
clearance when `b₀ = false`. For the odd arc-1 flag, the reflection average
vanishes at points of the unit circle because inversion fixes those points.
-/

open Set MeasureTheory Filter Topology Metric
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket KsIndex.SingleDisk

/-- Reflected mollifications of an arc-1 seam piece eventually lie
in the mixed-flag single-disk core, for either slit flag. -/
theorem seam1_mollifier_singleCc {k : ℕ} (hk : 1 ≤ k) (b₁ b₀ : Bool)
    {u : ℂ → ℂ} (hu : MemLp u 2 volume) (hc : HasCompactSupport u)
    (hs : tsupport u ⊆
      (seamDomain (boundaryArc k 1) (isOpen_boundaryArc k 1) : Set ℂ))
    (hP : ∀ p ∈ Surface.punctures k, ∃ R : ℝ, 0 < R ∧
      ∀ᵐ w ∂(volume : Measure ℂ), dist w p < R → u w = 0) :
    ∀ᶠ n in atTop, closedDiskRestriction (reflectionAverage (sgn b₁)
      (compactMollify (shrinkingMollifier n) u)) ∈ SingleCc k b₁ b₀ := by
  have hsgn : sgn b₁ ^ 2 = 1 := by cases b₁ <;> norm_num [sgn]
  have hR := seam1_mollifier_reflected_core hk (sgn b₁) (sgn b₀) hsgn hu hc hs hP
  have hsupp := reflected_mollifier_support_seam (sgn b₁)
    (isOpen_boundaryArc k 1) hc hs
  filter_upwards [hR, hsupp] with n hRn hsn
  set g := reflectionAverage (sgn b₁)
    (compactMollify (shrinkingMollifier n) u) with hgdef
  obtain ⟨h1, h2, _, h4, h5, _⟩ := hRn
  have hgsm : ContDiff ℝ ∞ g :=
    reflectionAverage_smooth_of_zero_not_support (sgn b₁)
      (compactMollify_smooth _ hu)
      (fun h => zero_notMem_seamDomain (isOpen_boundaryArc k 1) (hsn h))
  have hts : tsupport (closedDiskRestriction g) ⊆ tsupport g := by
    apply closure_mono
    intro z hz
    simp only [Function.mem_support, closedDiskRestriction] at hz ⊢
    intro h0
    apply hz
    split_ifs
    · exact h0
    · rfl
  refine ⟨h1, h2, ?_, h4, ?_, h5⟩
  · cases b₀
    · -- Dirichlet slit: uniform clearance from arc-1 support
      apply suppAwaySlit1_of_seam1_support
      · refine HasCompactSupport.of_support_subset_isCompact
          (isCompact_closedBall (0 : ℂ) 2) ?_
        intro z hz
        have hz2 := hsn (hts (subset_closure hz))
        have hcol := hz2.1
        simp only [Metric.mem_closedBall, dist_zero_right]
        exact hcol.2.le
      · exact hts.trans hsn
    · -- Neumann slit: the trivial one-sided extension by the smooth g
      intro w _
      refine ⟨g, hgsm.contDiffAt, Eventually.of_forall fun z hz => ?_⟩
      exact ite_eq_left (KsIndex.SurfaceForm.mem_disk_iff.mp hz).le
  · -- odd-case circle vanishing: the (−1)-average dies at σ-fixed points
    intro hb w hw
    have hcdr : closedDiskRestriction g w = g w := ite_eq_left hw.le
    rw [hcdr, hgdef]
    subst hb
    simp only [reflectionAverage, sgn, Bool.false_eq_true, ite_false, σ_self hw]
    ring

end KsIndex.Trace
