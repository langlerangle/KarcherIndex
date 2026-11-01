module

public import KsIndexLean.SeamMollificationSupport
public import KsIndexLean.TwistTransport

@[expose] public section


open Set Filter Topology Metric
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket KsIndex.SingleDisk

lemma closedDiskRestriction_smoothOn {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞ (closedDiskRestriction f) disk := by
  apply hf.contDiffOn.congr
  intro z hz
  exact ite_eq_left (KsIndex.SurfaceForm.mem_disk_iff.mp hz).le

lemma closedDiskRestriction_continuousOn {f : ℂ → ℂ} (hf : Continuous f) :
    ContinuousOn (closedDiskRestriction f) (closedBall (0 : ℂ) 1) := by
  apply hf.continuousOn.congr
  intro z hz
  exact ite_eq_left (by simpa only [mem_closedBall, dist_zero_right] using hz)

lemma refl_closedDiskRestriction_of_parity (s : ℂ) {f : ℂ → ℂ}
    (hp : ∀ z, s * f (σ z) = f z) : refl s (closedDiskRestriction f) = f := by
  funext z
  by_cases hz : ‖z‖ ≤ 1
  · simp only [KsIndex.SingleDisk.refl, closedDiskRestriction, ite_eq_left hz]
  · have hn : 0 < ‖z‖ := lt_trans zero_lt_one (lt_of_not_ge hz)
    have hi : ‖σ z‖ ≤ 1 := by
      rw [norm_σ]
      exact (inv_le_one₀ hn).mpr (le_of_lt (lt_of_not_ge hz))
    simp only [KsIndex.SingleDisk.refl, ite_eq_right hz, closedDiskRestriction, ite_eq_left hi]
    exact hp z

lemma restricted_reflection_zero_germ (s : ℂ) {f : ℂ → ℂ} {p : ℂ}
    (hp : ‖p‖ = 1) (hn : p ∉ tsupport f) :
    ContDiffAt ℝ ∞ (refl s (closedDiskRestriction f)) p := by
  have he : f =ᶠ[𝓝 p] 0 := notMem_tsupport_iff_eventuallyEq.mp hn
  have hd : closedDiskRestriction f =ᶠ[𝓝 p] 0 := by
    filter_upwards [he] with z hz
    simp [closedDiskRestriction, hz]
  have hp0 : p ≠ 0 := by intro h; simp [h] at hp
  have ht : Tendsto σ (𝓝 p) (𝓝 p) := by
    simpa only [σ_self hp] using (continuousAt_σ hp0).tendsto
  have hh : refl s (closedDiskRestriction f) =ᶠ[𝓝 p] 0 := by
    filter_upwards [hd, ht.eventually hd] with z hz hi
    simp [KsIndex.SingleDisk.refl, hz, hi]
  exact contDiffAt_const.congr_of_eventuallyEq hh

lemma seam_support_excludes_arc {k j n : ℕ} {f : ℂ → ℂ}
    (hs : tsupport f ⊆ seamDomain (boundaryArc k j) (isOpen_boundaryArc k j))
    (hd : Disjoint (boundaryArc k j) (boundaryArc k n)) {p : ℂ}
    (hp : p ∈ KsIndex.Surface.arc k n) : p ∉ tsupport f := by
  intro h
  have hm := (mem_seamDomain_iff (isOpen_boundaryArc k j) p).mp (hs h)
  let w : Circle₁ := ⟨p, mem_sphere_zero_iff_norm.mpr hp.1⟩
  have hj : w ∈ boundaryArc k j := hm.2 w rfl
  have hn : w ∈ boundaryArc k n := hp
  exact Set.disjoint_left.mp hd hj hn

/-- A supported arc-1 piece satisfies both exact reflected boundary conditions. -/
theorem seam1_smooth_reflected_core (k : ℕ) (s1 s0 : ℂ) {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f)
    (hs : tsupport f ⊆ seamDomain (boundaryArc k 1) (isOpen_boundaryArc k 1))
    (hp : ∀ z, s1 * f (σ z) = f z) (hP : SuppAwayP1 k (closedDiskRestriction f)) :
    KsIndex.TwistSwap.IsSmoothR k s1 s0 (closedDiskRestriction f) := by
  refine ⟨closedDiskRestriction_smoothOn hf, ?_, ?_, ?_, hP,
    closedDiskRestriction_continuousOn hf.continuous⟩
  · intro p _
    rw [refl_closedDiskRestriction_of_parity s1 hp]
    exact hf.contDiffAt
  · intro p hp0
    exact restricted_reflection_zero_germ s0 hp0.1
      (seam_support_excludes_arc hs (boundaryArc_disjoint k).symm hp0)
  · intro z hz
    exact ite_eq_right (not_le_of_gt hz)

/-- A supported arc-0 piece satisfies both exact reflected boundary conditions. -/
theorem seam0_smooth_reflected_core (k : ℕ) (s1 s0 : ℂ) {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f)
    (hs : tsupport f ⊆ seamDomain (boundaryArc k 0) (isOpen_boundaryArc k 0))
    (hp : ∀ z, s0 * f (σ z) = f z) (hP : SuppAwayP1 k (closedDiskRestriction f)) :
    KsIndex.TwistSwap.IsSmoothR k s1 s0 (closedDiskRestriction f) := by
  refine ⟨closedDiskRestriction_smoothOn hf, ?_, ?_, ?_, hP,
    closedDiskRestriction_continuousOn hf.continuous⟩
  · intro p hp1
    exact restricted_reflection_zero_germ s1 hp1.1
      (seam_support_excludes_arc hs (boundaryArc_disjoint k) hp1)
  · intro p _
    rw [refl_closedDiskRestriction_of_parity s0 hp]
    exact hf.contDiffAt
  · intro z hz
    exact ite_eq_right (not_le_of_gt hz)

end KsIndex.Trace
