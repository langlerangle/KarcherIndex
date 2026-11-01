module

public import KsIndexLean.HalfDiskFiniteEnergy

@[expose] public section


/-! Equality of classical half-disk fields is determined by their weak values.
Exterior values and values at deleted punctures play no role. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace KsIndex.Trace.ClassicalHalfDiskJacobi
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.WeakH1
variable {k : ℕ} {b c : Bool}

/-- Interior equality extends to every nonpunctured boundary point using the
one-sided smooth germs; no continuity of exterior values is required. -/
lemma closed_eq_of_disk_eq (u : ClassicalHalfDiskJacobi k b)
    (v : ClassicalHalfDiskJacobi k c) (hi : EqOn u.value v.value (Surface.disk : Set ℂ)) :
    EqOn u.value v.value (Metric.closedBall (0 : ℂ) 1 \ punctures k) := by
  intro w hw
  have hn : ‖w‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hw.1
  rcases lt_or_eq_of_le hn with hlt | he
  · exact hi (mem_disk_iff.mpr hlt)
  · obtain ⟨F,hF,hs,_⟩ := u.boundary w he hw.2
    obtain ⟨G,hG,ht,_⟩ := v.boundary w he hw.2
    have : (nhdsWithin w (Surface.disk : Set ℂ)).NeBot := by
      apply mem_closure_iff_nhdsWithin_neBot.mp
      change w ∈ closure (Metric.ball (0 : ℂ) 1)
      rw [closure_ball (0 : ℂ) one_ne_zero, Metric.mem_closedBall, dist_zero_right, he]
    have hFG : F =ᶠ[nhdsWithin w (Surface.disk : Set ℂ)] G := by
      filter_upwards [hs.filter_mono nhdsWithin_le_nhds,
        ht.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hz' hd
      have hz1 : ‖z‖ ≤ 1 := (mem_disk_iff.mp hd).le
      exact (hz hz1).symm.trans ((hi hd).trans (hz' hz1))
    have hlim : Tendsto G (nhdsWithin w (Surface.disk : Set ℂ)) (nhds (F w)) :=
      hF.continuousAt.continuousWithinAt.tendsto.congr' hFG
    have hval : F w = G w :=
      tendsto_nhds_unique hlim hG.continuousAt.continuousWithinAt.tendsto
    exact (hs.self_of_nhds he.le).trans (hval.trans (ht.self_of_nhds he.le).symm)

/-- The Sobolev map identifies precisely those data records that define the
same classical field on the punctured closed disk. -/
theorem toH1_eq_iff_closed (u : ClassicalHalfDiskJacobi k b)
    (v : ClassicalHalfDiskJacobi k c) (hk : 2 ≤ k) :
    u.toH1 hk = v.toH1 hk ↔
      EqOn u.value v.value (Metric.closedBall (0 : ℂ) 1 \ punctures k) := by
  constructor
  · intro he
    apply closed_eq_of_disk_eq
    have ha := u.toH1_value_ae hk
    rw [he] at ha
    exact Measure.eqOn_open_of_ae_eq (ha.symm.trans (v.toH1_value_ae hk))
      Metric.isOpen_ball u.smooth.continuousOn v.smooth.continuousOn
  · intro he
    apply valueCLM_injective
    apply Lp.ext
    filter_upwards [u.toH1_value_ae hk, v.toH1_value_ae hk,
      ae_restrict_mem Metric.isOpen_ball.measurableSet] with w hu hv hw
    rw [hu,hv]
    apply he
    exact ⟨Metric.ball_subset_closedBall hw, punctures_notMem_disk (by omega) hw⟩

end KsIndex.Trace.ClassicalHalfDiskJacobi
