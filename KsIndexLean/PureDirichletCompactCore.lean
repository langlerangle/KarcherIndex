module

public import KsIndexLean.SeamPureD
public import KsIndexLean.OpenSetCompactSupport

@[expose] public section


/-! The pure Dirichlet natural disk core is exactly the smooth test functions
whose support is compactly contained in the open disk. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
open KsIndex.Surface KsIndex.SurfaceForm
namespace KsIndex.SingleDisk

lemma dd_tsupport_subset_disk {k : ℕ} {f : ℂ → ℂ}
    (hf : f ∈ NatCc k false false) : tsupport f ⊆ disk := by
  obtain ⟨ε,hε,hvan⟩ := dd_vanish_near_circle hf
  intro z hz
  by_contra hn
  have hn' : 1 ≤ ‖z‖ := le_of_not_gt (fun hh => hn (mem_disk_iff.mpr hh))
  have he : f =ᶠ[𝓝 z] 0 := by
    rcases eq_or_lt_of_le hn' with heq | hgt
    · filter_upwards [Metric.ball_mem_nhds z hε] with w hw
      exact hvan z heq.symm w hw
    · have hopen : IsOpen {w : ℂ | 1 < ‖w‖} := isOpen_lt continuous_const continuous_norm
      filter_upwards [hopen.mem_nhds hgt] with w hw
      exact (mem_NatCc.mp hf).2.2.2.1 w hw
  exact (notMem_tsupport_iff_eventuallyEq.mpr he) hz

lemma hasCompactSupport_of_tsupport_subset_disk {f : ℂ → ℂ}
    (hf : tsupport f ⊆ disk) : HasCompactSupport f :=
  (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset (isClosed_tsupport f)
    (fun _ hz => Metric.ball_subset_closedBall (hf hz))

lemma suppAwaySet_of_disk_support {f : ℂ → ℂ} (hf : tsupport f ⊆ disk)
    {S : Set ℂ} (hS : S ⊆ diskᶜ) : SuppAwaySet S f := by
  have hc := hasCompactSupport_of_tsupport_subset_disk hf
  obtain ⟨ε,hε,hth⟩ := hc.exists_cthickening_subset_open Metric.isOpen_ball hf
  refine ⟨ε,hε,fun w ⟨p,hp,hwp⟩ => ?_⟩
  by_contra hn
  have hw : w ∈ tsupport f := subset_tsupport f hn
  have hp' : p ∈ Metric.cthickening ε (tsupport f) := by
    apply Metric.mem_cthickening_of_dist_le p w ε _ hw
    rw [dist_eq_norm,norm_sub_rev]
    exact hwp.le
  exact (hS hp) (hth hp')

lemma mem_NatCc_DD_iff_compact_core {k : ℕ} (hk : 1 ≤ k) (f : ℂ → ℂ) :
    f ∈ NatCc k false false ↔ ContDiff ℝ ∞ f ∧ tsupport f ⊆ disk := by
  constructor
  · intro hf
    exact ⟨dd_contDiff hf,dd_tsupport_subset_disk hf⟩
  · rintro ⟨hsm,hs⟩
    apply mem_NatCc.mpr
    refine ⟨hsm.contDiffOn,?_,?_,?_,?_⟩
    · apply suppAwaySet_of_disk_support hs
      intro p hp hd
      have hp1 : ‖p‖ = 1 := hp.1
      have hd1 := mem_disk_iff.mp hd
      linarith
    · apply suppAwaySet_of_disk_support hs
      intro p hp hd
      have hp1 : ‖p‖ = 1 := hp.1
      have hd1 := mem_disk_iff.mp hd
      linarith
    · intro w hw
      apply image_eq_zero_of_notMem_tsupport
      intro ht
      have hh := mem_disk_iff.mp (hs ht)
      linarith
    · apply suppAwaySet_of_disk_support hs
      intro p hp hd
      have hp1 := (punctures_subset_slitC hk hp).1
      have hd1 := mem_disk_iff.mp hd
      linarith

lemma zeroExtendSet_mem_NatCc_DD_iff {k : ℕ} (hk : 1 ≤ k) (f : disk → ℂ) :
    zeroExtendSet disk f ∈ NatCc k false false ↔
      HasCompactSupport f ∧ ContDiffOn ℝ ∞ (zeroExtendSet disk f) disk := by
  have hc : IsCompact (closure disk) := by
    change IsCompact (closure (Metric.ball (0 : ℂ) 1))
    exact (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset isClosed_closure
      (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall)
  constructor
  · intro hf
    have hs := dd_tsupport_subset_disk hf
    have hh := hasCompactSupport_restrict_of_tsupport_subset
      (hasCompactSupport_of_tsupport_subset_disk hs) hs
    have he : (fun q : disk => zeroExtendSet disk f q.val) = f := by
      funext q
      simp [zeroExtendSet,q.property]
    rw [he] at hh
    exact ⟨hh,(mem_NatCc.mp hf).1⟩
  · rintro ⟨hf,hsm⟩
    have hs := tsupport_zeroExtendSet_subset Metric.isOpen_ball hc hf
    apply (mem_NatCc_DD_iff_compact_core hk _).mpr
    refine ⟨?_,hs⟩
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ disk
    · exact hsm.contDiffAt (Metric.isOpen_ball.mem_nhds hz)
    · have hn : z ∉ tsupport (zeroExtendSet disk f) := fun ht => hz (hs ht)
      exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.mp hn)

end KsIndex.SingleDisk
