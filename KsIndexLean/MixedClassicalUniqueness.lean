module

public import KsIndexLean.MixedRadicalClassical
public import KsIndexLean.WeakSmoothCharacter

@[expose] public section


/-! Uniqueness on the physical half disk and rotation characters of the
classical representative. Exterior and deleted-point values are not constrained. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace KsIndex.Trace
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.WeakH1 KsIndex.FormIndex

namespace ClassicalMixedHalfDiskJacobi
variable {k : ℕ} {b1 b0 : Bool}

lemma continuousOn_puncturedClosedDisk (U : ClassicalMixedHalfDiskJacobi k b1 b0) :
    ContinuousOn U.value (Metric.closedBall (0 : ℂ) 1 \ punctures k) := by
  intro w hw
  have hn : ‖w‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hw.1
  rcases lt_or_eq_of_le hn with hi | he
  · exact (U.smooth.contDiffAt (Metric.isOpen_ball.mem_nhds
      (mem_disk_iff.mpr hi))).continuousAt.continuousWithinAt
  · obtain ⟨F, hF, hs, _⟩ := U.boundary w he hw.2
    refine hF.continuousAt.continuousWithinAt.congr_of_eventuallyEq ?_ (hs.self_of_nhds hn)
    filter_upwards [hs.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hd
    exact hz (by simpa only [Metric.mem_closedBall, dist_zero_right] using hd.1)

/-- Equality of the weak classes determines all values on the physical
closed half disk; arbitrary exterior/deleted-point extensions are irrelevant. -/
theorem eqOn_of_toH1_eq (hk : 2 ≤ k) (U V : ClassicalMixedHalfDiskJacobi k b1 b0)
    (he : U.toH1 hk = V.toH1 hk) :
    EqOn U.value V.value (Metric.closedBall (0 : ℂ) 1 \ punctures k) := by
  have ha : U.value =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] V.value := by
    have hu := U.toH1_value_ae hk
    rw [he] at hu
    exact hu.symm.trans (V.toH1_value_ae hk)
  have hi : EqOn U.value V.value (Surface.disk : Set ℂ) :=
    Measure.eqOn_open_of_ae_eq ha WeakH1.disk.isOpen U.smooth.continuousOn V.smooth.continuousOn
  apply hi.of_subset_closure U.continuousOn_puncturedClosedDisk
    V.continuousOn_puncturedClosedDisk
  · intro z hz
    exact ⟨Metric.ball_subset_closedBall hz, punctures_notMem_disk (by omega) hz⟩
  · change Metric.closedBall (0 : ℂ) 1 \ punctures k ⊆ closure (Metric.ball 0 1)
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact sdiff_subset

end ClassicalMixedHalfDiskJacobi

/-- The inverse representative retains the exact paper rotation character
on the open disk, in addition to recovering the original Sobolev element. -/
theorem dn_radical_classical_character {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (u : ComplexH1) (hu : u ∈ mixedCharacterDomain k j true false)
    (hQ : ∀ v ∈ mixedCharacterDomain k j true false,
      weakJacobi (surfacePotential k) u v = 0) :
    ∃ U : ClassicalMixedHalfDiskJacobi k true false, U.toH1 hk = u ∧
      ∀ z ∈ (Surface.disk : Set ℂ),
        U.value (planeRotation (-(2 * Real.pi) / k) z) = zeta k ^ j * U.value z := by
  obtain ⟨U, he⟩ := dn_radical_toH1_surjective hk j u hu hQ
  refine ⟨U, he, continuous_representative_character u _ _ hu.2 U.smooth.continuousOn ?_⟩
  have ha := U.toH1_value_ae hk
  rw [he] at ha
  exact ha

end KsIndex.Trace
