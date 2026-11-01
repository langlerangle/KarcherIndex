module

public import KsIndexLean.SingleCcSeam1

@[expose] public section


/-!
# Arc-0 approximants with the Neumann slit flag

Even reflected mollifications of an arc-0 seam piece eventually belong to
`SingleCc k b₁ true`. The reflected core supplies smoothness and support
conditions, and the smooth averaged function supplies the one-sided extension.
When `b₁ = false`, the additional hypothesis `hodd` requires the input to
vanish in an annulus around the unit circle. Once the mollifier radius is
smaller than that annulus width, the mollification and its even reflection
average vanish on the circle. The Dirichlet slit flag is handled separately
by `SingleCcDirichlet`, which provides vanishing near the slit.
-/

open Set MeasureTheory Filter Topology Metric
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket KsIndex.SingleDisk

/-- Common assembly: an arc-0-seam `IsSmoothR` package plus smoothness of
the pre-restriction plus the circle clause gives mixed-core membership at
`b₀ = true`. -/
private lemma singleCc_true_of_isSmoothR {k : ℕ} {b₁ : Bool} {g : ℂ → ℂ}
    (hRn : KsIndex.TwistSwap.IsSmoothR k (sgn b₁) (sgn true)
      (closedDiskRestriction g))
    (hgsm : ContDiff ℝ ∞ g)
    (hcirc : b₁ = false → ∀ w : ℂ, ‖w‖ = 1 → closedDiskRestriction g w = 0) :
    closedDiskRestriction g ∈ SingleCc k b₁ true := by
  obtain ⟨h1, h2, _, h4, h5, _⟩ := hRn
  exact ⟨h1, h2, fun w _ => ⟨g, hgsm.contDiffAt,
    Eventually.of_forall fun z hz =>
      ite_eq_left (KsIndex.SurfaceForm.mem_disk_iff.mp hz).le⟩,
    h4, hcirc, h5⟩

/-- Even reflected mollifications of an arc-0 seam
piece eventually lie in the mixed-flag core at `b₀ = true`; the odd case
requires the explicit annular-vanishing hypothesis `hodd`. -/
theorem seam0_mollifier_singleCc {k : ℕ} (hk : 1 ≤ k) (b₁ : Bool)
    {u : ℂ → ℂ} (hu : MemLp u 2 volume) (hc : HasCompactSupport u)
    (hs : tsupport u ⊆
      (seamDomain (boundaryArc k 0) (isOpen_boundaryArc k 0) : Set ℂ))
    (hP : ∀ p ∈ Surface.punctures k, ∃ R : ℝ, 0 < R ∧
      ∀ᵐ w ∂(volume : Measure ℂ), dist w p < R → u w = 0)
    (hodd : b₁ = false → ∃ ε : ℝ, 0 < ε ∧
      ∀ w : ℂ, 1 - ε < ‖w‖ → ‖w‖ < 1 + ε → u w = 0) :
    ∀ᶠ n in atTop, closedDiskRestriction (reflectionAverage (sgn true)
      (compactMollify (shrinkingMollifier n) u)) ∈ SingleCc k b₁ true := by
  have hsgn : sgn true ^ 2 = 1 := by norm_num [sgn]
  have hR := seam0_mollifier_reflected_core hk (sgn b₁) (sgn true) hsgn
    hu hc hs hP
  have hsupp := reflected_mollifier_support_seam (sgn true)
    (isOpen_boundaryArc k 0) hc hs
  have hgsm : ∀ n, tsupport (reflectionAverage (sgn true)
      (compactMollify (shrinkingMollifier n) u)) ⊆
        (seamDomain (boundaryArc k 0) (isOpen_boundaryArc k 0) : Set ℂ) →
      ContDiff ℝ ∞ (reflectionAverage (sgn true)
        (compactMollify (shrinkingMollifier n) u)) := fun n hsn =>
    reflectionAverage_smooth_of_zero_not_support _
      (compactMollify_smooth _ hu)
      (fun h => zero_notMem_seamDomain (isOpen_boundaryArc k 0) (hsn h))
  cases b₁ with
  | true =>
    filter_upwards [hR, hsupp] with n hRn hsn
    exact singleCc_true_of_isSmoothR hRn (hgsm n hsn)
      (fun hb => absurd hb (by simp))
  | false =>
    obtain ⟨ε, hε, hu0⟩ := hodd rfl
    have hrad := shrinkingMollifier_radius.eventually (gt_mem_nhds hε)
    filter_upwards [hR, hsupp, hrad] with n hRn hsn hrn
    apply singleCc_true_of_isSmoothR hRn (hgsm n hsn)
    intro _ w hw
    -- the mollification dies on the circle: its support is r-thickened
    -- around a set that clears the ε-annulus, and r < ε
    have hMw : compactMollify (shrinkingMollifier n) u w = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      have h1 := compactMollify_tsupport_subset (shrinkingMollifier n) u hm
      rw [mem_cthickening_iff] at h1
      have hcl : tsupport u ⊆ {z : ℂ | 1 - ε < ‖z‖ ∧ ‖z‖ < 1 + ε}ᶜ := by
        apply closure_minimal _ (((isOpen_lt continuous_const
          continuous_norm).inter (isOpen_lt continuous_norm
            continuous_const)).isClosed_compl)
        intro z hz hmem
        exact hz (hu0 z hmem.1 hmem.2)
      have h2 : ENNReal.ofReal ε ≤ infEDist w (tsupport u) := by
        apply le_infEDist.mpr
        intro x hx
        rw [edist_dist]
        apply ENNReal.ofReal_le_ofReal
        have hxann := hcl hx
        simp only [mem_compl_iff, mem_ofPred_eq, not_and, not_lt] at hxann
        by_cases hxl : 1 - ε < ‖x‖
        · -- then ‖x‖ ≥ 1 + ε
          have hxe := hxann hxl
          have hn1 : ε ≤ ‖x‖ - ‖w‖ := by rw [hw]; linarith
          calc ε ≤ ‖x‖ - ‖w‖ := hn1
            _ ≤ ‖x - w‖ := norm_sub_norm_le x w
            _ = dist w x := by rw [dist_comm, dist_eq_norm]
        · -- ‖x‖ ≤ 1 − ε
          push Not at hxl
          have hn1 : ε ≤ ‖w‖ - ‖x‖ := by rw [hw]; linarith
          calc ε ≤ ‖w‖ - ‖x‖ := hn1
            _ ≤ ‖w - x‖ := norm_sub_norm_le w x
            _ = dist w x := (dist_eq_norm w x).symm
      have h3 := le_trans h2 h1
      rw [ENNReal.ofReal_le_ofReal_iff (shrinkingMollifier n).rOut_pos.le] at h3
      linarith
    have hcdr : closedDiskRestriction (reflectionAverage (sgn true)
        (compactMollify (shrinkingMollifier n) u)) w =
        reflectionAverage (sgn true)
          (compactMollify (shrinkingMollifier n) u) w := ite_eq_left hw.le
    rw [hcdr]
    simp [reflectionAverage, σ_self hw, hMw]

end KsIndex.Trace
