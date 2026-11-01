module

public import KsIndexLean.InteriorSmoothCore
public import KsIndexLean.SingleCcSlitClearance

@[expose] public section


/-!
# Interior approximants in the single-disk core

A smooth function whose topological support lies in the open disk belongs to
`SingleCc k b₁ b₀` for either boundary flag. Uniform clearance from the unit
circle supplies the zero reflection germ, Dirichlet slit clearance, puncture
clearance, and circle vanishing. The smooth function itself supplies the
one-sided extension for the Neumann flag. Support propagation then places
interior mollifications in the core for all sufficiently large indices.
-/

open Set MeasureTheory Filter Topology Metric
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket KsIndex.SingleDisk

/-- Smooth disk-supported functions lie in every mixed-flag single-disk
core. -/
lemma smooth_disk_supported_singleCc {k : ℕ} (hk : 1 ≤ k) (b₁ b₀ : Bool)
    {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ disk) :
    IsSmoothS k b₁ b₀ f := by
  obtain ⟨δ, hδ, hz⟩ := disk_supported_zero_near_circle hs
  refine ⟨hf.contDiffOn, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun w hw => disk_supported_reflection_germ (sgn b₁) hs hw.1
  · cases b₀
    · exact ⟨δ, hδ, fun w ⟨p, hp, hwp⟩ => hz p hp.1 w hwp⟩
    · exact fun w _ => ⟨f, hf.contDiffAt, Eventually.of_forall fun _ _ => rfl⟩
  · intro w hw
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have hlt := KsIndex.SurfaceForm.mem_disk_iff.mp (hs hm)
    linarith
  · intro _ w hw
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have hlt := KsIndex.SurfaceForm.mem_disk_iff.mp (hs hm)
    linarith
  · exact ⟨δ, hδ, fun w ⟨p, hp, hwp⟩ =>
      hz p (KsIndex.JacobiFamily.punctures_norm_eq_one hk hp) w hwp⟩

/-- Interior mollifications eventually lie in every mixed-flag
single-disk core. -/
theorem interior_mollifier_singleCc {k : ℕ} (hk : 1 ≤ k) (b₁ b₀ : Bool)
    {u : ℂ → ℂ} (hu : MemLp u 2 volume) (hc : HasCompactSupport u)
    (hs : tsupport u ⊆ disk) :
    ∀ᶠ n in atTop,
      compactMollify (shrinkingMollifier n) u ∈ SingleCc k b₁ b₀ := by
  filter_upwards [mollifier_support_open hc disk.isOpen hs] with n hn
  exact smooth_disk_supported_singleCc hk b₁ b₀ (compactMollify_smooth _ hu) hn

end KsIndex.Trace
