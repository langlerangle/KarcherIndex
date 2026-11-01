module

public import KsIndexLean.NullityGreen

@[expose] public section


/-! Continuous representatives of natural disk tests. Raw boundary values
are immaterial to the natural core; the representative instead takes the
unique boundary limits of the interior function. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.Bracket
namespace KsIndex.SingleDisk

/-- Interior germ equality extends to the closed side when both functions
are continuous there. The extension is still smooth at the boundary point. -/
lemma oneSided_closed_of_continuous {G : ℂ → ℂ} (hG : Continuous G)
    {w : ℂ} (h : OneSided G w) :
    ∃ F : ℂ → ℂ, ContDiffAt ℝ ∞ F w ∧
      ∀ᶠ z in 𝓝 w, ‖z‖ ≤ 1 → G z = F z := by
  obtain ⟨F,hF,he⟩ := h
  have hc : ∀ᶠ z in 𝓝 w, ContinuousAt F z :=
    ((hF.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).eventually (by simp)).mono
      (fun _ hz => hz.continuousAt)
  refine ⟨F,hF,?_⟩
  filter_upwards [hc,eventually_eventually_nhds.mpr he] with z hz hez hn
  have : (nhdsWithin z (disk : Set ℂ)).NeBot := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    change z ∈ closure (Metric.ball (0 : ℂ) 1)
    rw [closure_ball (0 : ℂ) one_ne_zero,Metric.mem_closedBall,dist_zero_right]
    exact hn
  have he' : G =ᶠ[nhdsWithin z (disk : Set ℂ)] F := by
    filter_upwards [hez.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with y hy hd
    exact hy hd
  have ht : Tendsto F (nhdsWithin z (disk : Set ℂ)) (𝓝 (G z)) :=
    hG.continuousAt.continuousWithinAt.tendsto.congr' he'
  exact tendsto_nhds_unique ht hz.continuousWithinAt.tendsto

/-- Every natural test has a continuous representative with smooth closed-side
boundary germs and vanishing near the punctures on the closed disk. Only
interior agreement with the original raw function is asserted. -/
lemma exists_closed_representative {k : ℕ} (hk : 1 ≤ k) {b₁ b₀ : Bool}
    {f : ℂ → ℂ} (hf : f ∈ NatCc k b₁ b₀) :
    ∃ G : ℂ → ℂ, Continuous G ∧ ContDiffOn ℝ ∞ G disk ∧
      EqOn f G disk ∧
      (∀ w : ℂ, ‖w‖ = 1 → ∃ F : ℂ → ℂ, ContDiffAt ℝ ∞ F w ∧
        ∀ᶠ z in 𝓝 w, ‖z‖ ≤ 1 → G z = F z) ∧
      (∃ ε > 0, ∀ z : ℂ, ‖z‖ ≤ 1 →
        (∃ p ∈ punctures k, ‖z-p‖ < ε) → G z = 0) := by
  obtain ⟨G,hG,he⟩ := KsIndex.SeamUpper.natCc_extension hk hf
  obtain ⟨hsm,h1,h0,hout,hP⟩ := mem_NatCc.mp hf
  refine ⟨G,hG.continuous,hsm.congr (fun z hz => (he z hz).symm),he,?_,?_⟩
  · intro w hw
    apply oneSided_closed_of_continuous hG.continuous
    have hlocal : OneSided f w := by
      by_cases hp : w ∈ punctures k
      · obtain ⟨ε,hε,hv⟩ := hP
        refine ⟨0,contDiffAt_const,?_⟩
        filter_upwards [Metric.ball_mem_nhds w hε] with z hz hd
        exact hv z ⟨w,hp,by simpa only [Metric.mem_ball,dist_eq_norm] using hz⟩
      · rcases mem_arc_of_not_puncture hw hp with ha | ha
        · exact KsIndex.SeamUpper.arcCond_local_ext h0 arc_zero_subset_slit ha
        · exact KsIndex.SeamUpper.arcCond_local_ext h1 arc_one_subset_slitC ha
    obtain ⟨F,hF,hfF⟩ := hlocal
    refine ⟨F,hF,?_⟩
    filter_upwards [hfF] with z hz hd
    exact (he z hd).symm.trans (hz hd)
  · obtain ⟨ε,hε,hv⟩ := hP
    exact ⟨ε/2,by positivity,fun z hz hp =>
      KsIndex.NullityDecomp.C1rep_vanishes_near hε hG.continuous he hv hz hp⟩

end KsIndex.SingleDisk
