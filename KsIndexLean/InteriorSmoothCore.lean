module

public import KsIndexLean.InteriorRemainderWeak
public import KsIndexLean.MollificationSupport
public import KsIndexLean.SingleDiskNat
public import KsIndexLean.TwistTransport
public import KsIndexLean.JacobiFamily

@[expose] public section


open Set Filter Topology MeasureTheory Metric
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket KsIndex.SingleDisk

lemma disk_supported_zero_near_circle {f : ℂ → ℂ} (hs : tsupport f ⊆ disk) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℂ, ‖p‖ = 1 → ∀ w, ‖w - p‖ < δ → f w = 0 := by
  obtain ⟨r, hr, hsub⟩ := exists_pos_lt_subset_ball
    (by norm_num : (0 : ℝ) < 1) isClosed_closure hs
  refine ⟨1 - r, sub_pos.mpr hr.2, ?_⟩
  intro p hp w hw
  apply image_eq_zero_of_notMem_tsupport
  intro hm
  have hn : ‖w‖ < r := by simpa only [mem_ball, dist_zero_right] using hsub hm
  have ht : ‖p‖ ≤ ‖w - p‖ + ‖w‖ := by
    have hh := norm_add_le (p - w) w
    simpa only [sub_add_cancel, norm_sub_rev] using hh
  linarith

lemma disk_supported_reflection_germ (s : ℂ) {f : ℂ → ℂ} (hs : tsupport f ⊆ disk)
    {p : ℂ} (hp : ‖p‖ = 1) : ContDiffAt ℝ ∞ (refl s f) p := by
  have hn : p ∉ tsupport f := by
    intro h
    have hh := KsIndex.SurfaceForm.mem_disk_iff.mp (hs h)
    linarith
  have he : f =ᶠ[𝓝 p] 0 := notMem_tsupport_iff_eventuallyEq.mp hn
  have hp0 : p ≠ 0 := by intro h; simp [h] at hp
  have ht : Tendsto σ (𝓝 p) (𝓝 p) := by
    simpa only [σ_self hp] using (continuousAt_σ hp0).tendsto
  have hz : refl s f =ᶠ[𝓝 p] 0 := by
    filter_upwards [he, ht.eventually he] with z hz hi
    simp [KsIndex.SingleDisk.refl, hz, hi]
  exact contDiffAt_const.congr_of_eventuallyEq hz

lemma smooth_disk_supported_natural {k : ℕ} (hk : 1 ≤ k) (b1 b0 : Bool)
    {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ disk) :
    IsSmoothNat k b1 b0 f := by
  obtain ⟨δ, hδ, hz⟩ := disk_supported_zero_near_circle hs
  have hside (p : ℂ) : OneSided f p :=
    ⟨f, hf.contDiffAt, Eventually.of_forall fun _ _ => rfl⟩
  have hcond (A S : Set ℂ) (hS : ∀ p ∈ S, ‖p‖ = 1) (b : Bool) : ArcCond A S b f := by
    cases b
    · exact ⟨δ, hδ, fun w ⟨p, hp, hw⟩ => hz p (hS p hp) w hw⟩
    · exact fun p _ => hside p
  refine ⟨hf.contDiffOn, hcond _ _ (fun _ hp => hp.1) b1,
    hcond _ _ (fun _ hp => hp.1) b0, ?_, ?_⟩
  · intro w hw
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have hh := KsIndex.SurfaceForm.mem_disk_iff.mp (hs hm)
    linarith
  · exact ⟨δ, hδ, fun w ⟨p, hp, hw⟩ =>
      hz p (KsIndex.JacobiFamily.punctures_norm_eq_one hk hp) w hw⟩

lemma smooth_disk_supported_reflected {k : ℕ} (hk : 1 ≤ k) (s1 s0 : ℂ)
    {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ disk) :
    KsIndex.TwistSwap.IsSmoothR k s1 s0 f := by
  have hn := smooth_disk_supported_natural hk true true hf hs
  exact ⟨hf.contDiffOn, fun _ hp => disk_supported_reflection_germ s1 hs hp.1,
    fun _ hp => disk_supported_reflection_germ s0 hs hp.1,
    hn.2.2.2.1, hn.2.2.2.2, hf.continuous.continuousOn⟩

/-- Actual interior mollifications eventually lie in both exact paper smooth-core encodings. -/
theorem interior_mollifier_smooth_cores {k : ℕ} (hk : 1 ≤ k)
    (b1 b0 : Bool) (s1 s0 : ℂ) {u : ℂ → ℂ}
    (hu : MemLp u 2 volume) (hc : HasCompactSupport u) (hs : tsupport u ⊆ disk) :
    ∀ᶠ n in atTop,
      IsSmoothNat k b1 b0 (compactMollify (shrinkingMollifier n) u) ∧
      KsIndex.TwistSwap.IsSmoothR k s1 s0 (compactMollify (shrinkingMollifier n) u) := by
  filter_upwards [mollifier_support_open hc disk.isOpen hs] with n hn
  exact ⟨smooth_disk_supported_natural hk b1 b0 (compactMollify_smooth _ hu) hn,
    smooth_disk_supported_reflected hk s1 s0 (compactMollify_smooth _ hu) hn⟩

end KsIndex.Trace
