module

public import KsIndexLean.ExtendedSeamChart

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma memLp_two_union {E : Type*} [NormedAddCommGroup E] {f : ℂ → E} {s t : Set ℂ}
    (hs : MemLp f 2 (volume.restrict s)) (ht : MemLp f 2 (volume.restrict t)) :
    MemLp f 2 (volume.restrict (s ∪ t)) := by
  apply (memLp_two_iff_integrable_sq_norm
    (aestronglyMeasurable_union_iff.mpr ⟨hs.aestronglyMeasurable, ht.aestronglyMeasurable⟩)).mpr
  exact IntegrableOn.union ((memLp_two_iff_integrable_sq_norm hs.aestronglyMeasurable).mp hs)
    ((memLp_two_iff_integrable_sq_norm ht.aestronglyMeasurable).mp ht)

lemma joinedDiskValue_disk_ae (u v : ComplexH1) (c : ℂ) :
    joinedDiskValue u v c =ᵐ[volume.restrict (disk : Set ℂ)] valueCLM u := by
  filter_upwards [ae_restrict_mem disk.isOpen.measurableSet] with z hz
  have hn : ‖z‖ < 1 := by simpa [disk, Metric.mem_ball, dist_zero_right] using hz
  simp [joinedDiskValue, radialJoin, hn.le]

lemma memLp_joinedDiskJet_disk (u v : ComplexH1) (c : ℂ) :
    MemLp (joinedDiskJet u v c) 2 (volume.restrict (disk : Set ℂ)) := by
  have hD : MemLp (Dxy (dxLp u) (dyLp u)) 2 (volume.restrict (disk : Set ℂ)) :=
    ((Lp.memLp (dxLp u)).continuousLinearMap_comp
      (ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.reCLM)).add
      ((Lp.memLp (dyLp u)).continuousLinearMap_comp
        (ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.imCLM))
  have hc : TauCeti.HasWeakFDerivOn volume disk (valueCLM u) (Dxy (dxLp u) (dyLp u)) :=
    carrier_hasJet u
  exact MemLp.ae_eq
    ((hc.congr_ae (joinedDiskValue_disk_ae u v c).symm).ae_eq (joinedDisk_inner_disk_weak u v c)) hD

lemma extendedSeamDomain_subset_disk_union {A : Set Circle₁} (hA : IsOpen A) :
    (extendedSeamDomain A hA : Set ℂ) ⊆ (disk : Set ℂ) ∪ annulusSet (1 / 2 : ℝ) 2 := by
  intro z hz
  by_cases hn : ‖z‖ < 1
  · exact Or.inl (by simpa [disk, Metric.mem_ball, dist_zero_right] using hn)
  · apply Or.inr
    exact ⟨by linarith [not_lt.mp hn], by simpa [Metric.mem_ball, dist_zero_right] using hz.1⟩

lemma extendedSeamDomain_value_memLp {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) :
    MemLp (joinedDiskValue u v c) 2 (volume.restrict (extendedSeamDomain A hA : Set ℂ)) :=
  (memLp_two_union (MemLp.ae_eq (joinedDiskValue_disk_ae u v c).symm (Lp.memLp (valueCLM u)))
    (memLp_joinedDiskValue u v c)).mono_measure
    (Measure.restrict_mono (extendedSeamDomain_subset_disk_union hA) le_rfl)

lemma extendedSeamDomain_jet_memLp {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) :
    MemLp (joinedDiskJet u v c) 2 (volume.restrict (extendedSeamDomain A hA : Set ℂ)) :=
  (memLp_two_union (memLp_joinedDiskJet_disk u v c) (memLp_joinedDiskJet u v c)).mono_measure
    (Measure.restrict_mono (extendedSeamDomain_subset_disk_union hA) le_rfl)

end KsIndex.Trace
