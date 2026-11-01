module

public import KsIndexLean.PureSectorClassicalExtension

@[expose] public section


/-! Agreement of classical representatives with actual sector fields on
nonpunctured boundary arcs. The chain's assigned puncture values are excluded. -/
noncomputable section
open Set MeasureTheory Filter
namespace KsIndex.NullityDecomp
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Surface KsIndex.SurfaceSym

/-- Interior agreement determines a boundary value whenever the original
function has a continuous extension from the closed-disk side. -/
lemma boundary_eq_of_inner_eq {f F H : ℂ → ℂ} {w : ℂ} (hw : ‖w‖ = 1)
    (hF : ContinuousAt F w) (hH : ContinuousAt H w)
    (hside : ∀ᶠ z in nhds w, ‖z‖ ≤ 1 → f z = F z)
    (hinner : EqOn f H (WeakH1.disk : Set ℂ)) : f w = H w := by
  have : (nhdsWithin w (WeakH1.disk : Set ℂ)).NeBot := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    change w ∈ closure (Metric.ball (0 : ℂ) 1)
    rw [closure_ball (0 : ℂ) one_ne_zero, Metric.mem_closedBall, dist_zero_right, hw]
  have he : F =ᶠ[nhdsWithin w (WeakH1.disk : Set ℂ)] H := by
    filter_upwards [hside.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hd
    have hn : ‖z‖ < 1 := by simpa only [dist_zero_right] using (Metric.mem_ball.mp hd)
    exact (hz hn.le).symm.trans (hinner hd)
  have hlim : Tendsto H (nhdsWithin w (WeakH1.disk : Set ℂ)) (nhds (F w)) :=
    hF.continuousWithinAt.tendsto.congr' he
  have hv : F w = H w := tendsto_nhds_unique hlim hH.continuousWithinAt.tendsto
  exact (hside.self_of_nhds hw.le).trans hv

/-- A continuous representative agreeing with a sector field in the disk
also agrees on every nonpunctured circle point. -/
theorem sector_boundary_eq_of_disk_eq {k r s₁ s₀ : ℕ}
    (W : boundedJacobiSector k r s₁ s₀) {H : ℂ → ℂ}
    (hH : ContinuousOn H (Metric.ball (0 : ℂ) 2))
    (hinner : EqOn ((uncurryE 2).symm W.val 0) H (WeakH1.disk : Set ℂ))
    {w : ℂ} (hw : ‖w‖ = 1) (hp : w ∉ punctures k) :
    (uncurryE 2).symm W.val 0 w = H w := by
  have hre : (w ^ k).re ≠ 0 := fun h => hp (puncture_of_re_pow_zero hw h)
  have hH' : ContinuousAt H w := hH.continuousAt
    (Metric.isOpen_ball.mem_nhds (by simpa only [Metric.mem_ball, dist_zero_right, hw] using
      (by norm_num : (1 : ℝ) < 2)))
  rcases lt_or_gt_of_ne hre with hneg | hpos
  · have ha : w ∈ arc k 0 := ⟨hw, by simpa using hneg⟩
    obtain ⟨F, hF, hs, _⟩ := sector_extension_arc0 W.property ha
    exact boundary_eq_of_inner_eq hw hF.continuousAt hH' hs hinner
  · have ha : w ∈ arc k 1 := ⟨hw, by simp only [pow_one, neg_one_mul]; linarith⟩
    obtain ⟨F, hF, hs, _⟩ := sector_extension_arc1 W.property ha
    exact boundary_eq_of_inner_eq hw hF.continuousAt hH' hs hinner

/-- Equality extends to the actual closed punctured disk, with no claim
about the carrier's artificial values at punctures. -/
theorem sector_closed_punctured_disk_eq {k r s₁ s₀ : ℕ}
    (W : boundedJacobiSector k r s₁ s₀) {H : ℂ → ℂ}
    (hH : ContinuousOn H (Metric.ball (0 : ℂ) 2))
    (hinner : EqOn ((uncurryE 2).symm W.val 0) H (WeakH1.disk : Set ℂ)) :
    EqOn ((uncurryE 2).symm W.val 0) H
      (Metric.closedBall (0 : ℂ) 1 \ punctures k) := by
  intro w hw
  have hn : ‖w‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hw.1
  rcases lt_or_eq_of_le hn with hlt | heq
  · exact hinner (Metric.mem_ball.mpr (by simpa only [dist_zero_right] using hlt))
  · exact sector_boundary_eq_of_disk_eq W hH hinner heq hw.2

end KsIndex.NullityDecomp
