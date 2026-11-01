module

public import KsIndexLean.SphericalInversionAE

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

lemma sphereJoinedValue_reconstruct_north (F : Sphere → ℂ) (u v : ComplexH1)
    (hn : (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
      (fun z => F (sphereChart z)))
    (hs : (valueCLM v : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
      (fun z => F (southChart z))) :
    (fun z => sphereJoinedValue u v (sphereChart z)) =ᵐ[volume]
      (fun z => F (sphereChart z)) := by
  have hn' := (ae_restrict_iff' disk.isOpen.measurableSet).mp hn
  have hs' := ae_comp_sigma ((ae_restrict_iff' disk.isOpen.measurableSet).mp hs)
  filter_upwards [hn', hs', ae_norm_ne_one] with z hnz hsz hne
  rw [sphereJoinedValue_north, joinedDiskValue_sigma_formula]
  by_cases h : ‖z‖ ≤ 1
  · rw [ite_eq_left h]
    exact hnz (by simpa [disk, Metric.mem_ball, dist_zero_right] using lt_of_le_of_ne h hne)
  · rw [ite_eq_right h, one_smul]
    have hz : z ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one (lt_of_not_ge h))
    have hi : Bracket.σ z ∈ disk := by
      change dist (Bracket.σ z) 0 < 1
      rw [dist_zero_right, Bracket.norm_σ]
      exact (inv_lt_one₀ (norm_pos_iff.mpr hz)).mpr (lt_of_not_ge h)
    rw [hsz hi, ← sphereChart_eq_southChart_sigma hz]

lemma sphereJoinedValue_reconstruct_south (F : Sphere → ℂ) (u v : ComplexH1)
    (hn : (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
      (fun z => F (sphereChart z)))
    (hs : (valueCLM v : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
      (fun z => F (southChart z))) :
    (fun z => sphereJoinedValue u v (southChart z)) =ᵐ[volume]
      (fun z => F (southChart z)) := by
  filter_upwards [ae_comp_sigma (sphereJoinedValue_reconstruct_north F u v hn hs),
    volume.ae_ne (0 : ℂ)] with z he hz
  simpa only [← southChart_eq_sigma hz] using he

/-- Chartwise finite energy forces ordinary transmission for the recovered disk data. -/
theorem sphere_chart_reconstruction {A : Set Circle₁} (hA : IsOpen A) (F : Sphere → ℂ)
    (hn : ChartH1 (extendedSeamDomain A hA) (fun z => F (sphereChart z)))
    (hs : ChartH1 (extendedSeamDomain A hA) (fun z => F (southChart z))) :
    ∃ u v : ComplexH1, arcTrace A u = arcTrace A v ∧
      ((fun z => sphereJoinedValue u v (sphereChart z)) =ᵐ[volume]
        (fun z => F (sphereChart z))) ∧
      ((fun z => sphereJoinedValue u v (southChart z)) =ᵐ[volume]
        (fun z => F (southChart z))) := by
  obtain ⟨⟨u, hu, _⟩, ⟨v, hv, _⟩⟩ := sphere_chart_disk_carriers hA F hn hs
  have he := sphereJoinedValue_reconstruct_north F u v hu hv
  have her := he.filter_mono
    (ae_mono (Measure.restrict_le_self : volume.restrict
      (extendedSeamDomain A hA : Set ℂ) ≤ volume))
  exact ⟨u, v, (sphereJoinedValue_north_H1_iff hA u v).mp
    ((chartH1_congr_ae her).mpr hn), he, sphereJoinedValue_reconstruct_south F u v hu hv⟩

end KsIndex.Spherical
