module

public import KsIndexLean.SphericalJoinedValue
public import KsIndexLean.SlitWeakChartCriterion

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

/-- Genuine finite-energy weak regularity of a planar chart function. -/
def ChartH1 (Ω : TopologicalSpace.Opens ℂ) (f : ℂ → ℂ) : Prop :=
  MemLp f 2 (volume.restrict (Ω : Set ℂ)) ∧
    ∃ J, TauCeti.HasWeakFDerivOn volume Ω f J ∧
      MemLp J 2 (volume.restrict (Ω : Set ℂ))

lemma chartH1_congr_ae {Ω : TopologicalSpace.Opens ℂ} {f g : ℂ → ℂ}
    (he : f =ᵐ[volume.restrict (Ω : Set ℂ)] g) : ChartH1 Ω f ↔ ChartH1 Ω g := by
  constructor
  · rintro ⟨hf, J, hJ, hL⟩
    exact ⟨MemLp.ae_eq he hf, J, hJ.congr_ae he, hL⟩
  · rintro ⟨hg, J, hJ, hL⟩
    exact ⟨MemLp.ae_eq he.symm hg, J, hJ.congr_ae he.symm, hL⟩

lemma sphereJoinedValue_north_weak {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (hm : arcTrace A u = arcTrace A v) :
    TauCeti.HasWeakFDerivOn volume (extendedSeamDomain A hA)
      (fun z => sphereJoinedValue u v (sphereChart z)) (joinedDiskJet u v 1) := by
  have he : (fun z => sphereJoinedValue u v (sphereChart z)) = joinedDiskValue u v 1 :=
    funext (sphereJoinedValue_north u v)
  rw [he]
  exact extendedSeamDomain_weak hA u v 1 (by simpa using hm)

lemma sphereJoinedValue_south_weak {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (hm : arcTrace A u = arcTrace A v) :
    TauCeti.HasWeakFDerivOn volume (extendedSeamDomain A hA)
      (fun z => sphereJoinedValue u v (southChart z)) (joinedDiskJet v u 1) := by
  have he := (sphereJoinedValue_south_ae u v).filter_mono
    (ae_mono (Measure.restrict_le_self : volume.restrict
      (extendedSeamDomain A hA : Set ℂ) ≤ volume))
  exact (extendedSeamDomain_weak hA v u 1 (by simpa using hm.symm)).congr_ae he.symm

lemma sphereJoinedValue_north_H1_iff {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) :
    ChartH1 (extendedSeamDomain A hA) (fun z => sphereJoinedValue u v (sphereChart z)) ↔
      arcTrace A u = arcTrace A v := by
  have he : (fun z => sphereJoinedValue u v (sphereChart z)) = joinedDiskValue u v 1 :=
    funext (sphereJoinedValue_north u v)
  rw [he]
  simpa [ChartH1] using extendedSeamDomain_H1_iff_trace hA u v 1

lemma sphereJoinedValue_south_H1_iff {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) :
    ChartH1 (extendedSeamDomain A hA) (fun z => sphereJoinedValue u v (southChart z)) ↔
      arcTrace A u = arcTrace A v := by
  have he := (sphereJoinedValue_south_ae u v).filter_mono
    (ae_mono (Measure.restrict_le_self : volume.restrict
      (extendedSeamDomain A hA : Set ℂ) ≤ volume))
  rw [chartH1_congr_ae he]
  simpa [ChartH1, eq_comm] using extendedSeamDomain_H1_iff_trace hA v u 1

/-- Both actual bounded charts on the slit sphere have genuine H1 pullbacks
exactly when the disk traces match on the unremoved equatorial arc. -/
theorem sphereJoinedValue_slit_H1_iff (k : ℕ) (u v : ComplexH1) :
    (ChartH1 (extendedSeamDomain (boundaryArc k 1) (isOpen_boundaryArc k 1))
        (fun z => sphereJoinedValue u v (sphereChart z)) ∧
      ChartH1 (extendedSeamDomain (boundaryArc k 1) (isOpen_boundaryArc k 1))
        (fun z => sphereJoinedValue u v (southChart z))) ↔
      arcTrace (boundaryArc k 1) u = arcTrace (boundaryArc k 1) v := by
  rw [sphereJoinedValue_north_H1_iff (isOpen_boundaryArc k 1),
    sphereJoinedValue_south_H1_iff (isOpen_boundaryArc k 1), and_self]

end KsIndex.Spherical
