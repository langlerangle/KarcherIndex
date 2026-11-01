module

public import KsIndexLean.BulkClosure
public import KsIndexLean.JacobiShiftCoercivity
public import KsIndexLean.SphericalDiskMeasureBounds

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace KsIndex.Spherical
open KsIndex.WeakH1

abbrev WeightedDiskL2 := Lp ℂ 2 (stereoAreaMeasure.restrict (disk : Set ℂ))

lemma ae_weightedDisk_iff (P : ℂ → Prop) :
    (∀ᵐ z ∂stereoAreaMeasure.restrict (disk : Set ℂ), P z) ↔
      ∀ᵐ z ∂volume.restrict (disk : Set ℂ), P z := by
  rw [ae_restrict_iff' disk.isOpen.measurableSet, ae_stereoAreaMeasure_iff,
    ae_restrict_iff' disk.isOpen.measurableSet]

/-- Identity on representatives, with the actual spherical chart measure. -/
def sphericalBulkMap (f : L2C) : WeightedDiskL2 :=
  ((memLp_stereoAreaMeasure_disk_iff f 2).mpr (Lp.memLp f)).toLp f

lemma sphericalBulkMap_ae (f : L2C) :
    sphericalBulkMap f =ᵐ[stereoAreaMeasure.restrict (disk : Set ℂ)] f :=
  MemLp.coeFn_toLp _

lemma sphericalBulkMap_add (f g : L2C) :
    sphericalBulkMap (f + g) = sphericalBulkMap f + sphericalBulkMap g := by
  apply Lp.ext
  filter_upwards [sphericalBulkMap_ae (f + g), sphericalBulkMap_ae f,
    sphericalBulkMap_ae g, (ae_weightedDisk_iff _).mpr (Lp.coeFn_add f g),
    Lp.coeFn_add (sphericalBulkMap f) (sphericalBulkMap g)] with z ha hf hg hb hc
  simp only [ha, hc, Pi.add_apply, hf, hg, hb]

lemma sphericalBulkMap_smul (c : ℂ) (f : L2C) :
    sphericalBulkMap (c • f) = c • sphericalBulkMap f := by
  apply Lp.ext
  filter_upwards [sphericalBulkMap_ae (c • f), sphericalBulkMap_ae f,
    (ae_weightedDisk_iff _).mpr (Lp.coeFn_smul c f),
    Lp.coeFn_smul c (sphericalBulkMap f)] with z ha hf hb hc
  simp only [ha, hc, Pi.smul_apply, hf, hb]

lemma sphericalBulkMap_norm_le (f : L2C) :
    ‖sphericalBulkMap f‖ ≤ ((4 : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal).toReal * ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (sphericalBulkMap_ae f)]
  have h := (eLpNorm_disk_comparison f 2).2
  simp only [smul_eq_mul] at h
  have ht : (4 : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal *
      eLpNorm f 2 (volume.restrict (disk : Set ℂ)) ≠ ∞ := by finiteness
  simpa only [ENNReal.toReal_mul] using ENNReal.toReal_mono ht h

/-- Continuous change from flat disk L2 to canonical spherical chart L2. -/
def sphericalBulkCLM : L2C →L[ℂ] WeightedDiskL2 :=
  LinearMap.mkContinuous
    { toFun := sphericalBulkMap
      map_add' := sphericalBulkMap_add
      map_smul' := sphericalBulkMap_smul }
    _ sphericalBulkMap_norm_le

lemma sphericalBulkCLM_injective : Function.Injective sphericalBulkCLM := by
  intro f g h
  apply Lp.ext
  apply (ae_weightedDisk_iff _).mp
  filter_upwards [sphericalBulkMap_ae f, sphericalBulkMap_ae g] with z hf hg
  have he : sphericalBulkMap f z = sphericalBulkMap g z := congrArg (fun a : WeightedDiskL2 => a z) h
  exact hf.symm.trans (he.trans hg)

/-- The unrestricted H1 inclusion into weighted spherical chart L2 is compact. -/
def weightedDiskValueCLM : ComplexH1 →L[ℂ] WeightedDiskL2 := sphericalBulkCLM.comp valueCLM

lemma weightedDiskValueCLM_compact : IsCompactOperator weightedDiskValueCLM :=
  valueCLM_isCompactOperator.clm_comp sphericalBulkCLM

lemma weightedDiskValueCLM_injective : Function.Injective weightedDiskValueCLM :=
  sphericalBulkCLM_injective.comp valueCLM_injective

lemma norm_le_sphericalBulkCLM (f : L2C) : ‖f‖ ≤ ‖sphericalBulkCLM f‖ := by
  change ‖f‖ ≤ ‖sphericalBulkMap f‖
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (sphericalBulkMap_ae f)]
  exact ENNReal.toReal_mono
    ((memLp_stereoAreaMeasure_disk_iff f 2).mpr (Lp.memLp f)).eLpNorm_ne_top
    (eLpNorm_disk_comparison f 2).1

/-- Coercivity against the squared norm in the actual weighted Hilbert target. -/
lemma weightedDiskJacobi_shift_coercive (V : BoundedRealPotential) (u : ComplexH1) :
    ‖u‖ ^ 2 ≤ (weakJacobi V u u).re + (V.C + 1) * ‖weightedDiskValueCLM u‖ ^ 2 := by
  apply weakJacobi_shift_coercive V u
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (norm_le_sphericalBulkCLM (valueCLM u))

/-- The weighted ambient space of an actual single-disk form domain. -/
abbrev WeightedDiskAmbient (D : Submodule ℂ ComplexH1) :=
  KsIndex.Spectral.bulkClosure (V := D) (H := WeightedDiskL2)
    (weightedDiskValueCLM.comp D.subtypeL)

abbrev weightedDiskAmbientEmbedding (D : Submodule ℂ ComplexH1) :=
  KsIndex.Spectral.closureEmbedding (V := D) (H := WeightedDiskL2)
    (weightedDiskValueCLM.comp D.subtypeL)

lemma weightedDiskAmbientEmbedding_spec (D : Submodule ℂ ComplexH1) :
    Function.Injective (weightedDiskAmbientEmbedding D) ∧
      DenseRange (weightedDiskAmbientEmbedding D) ∧
      IsCompactOperator (weightedDiskAmbientEmbedding D) :=
  ⟨KsIndex.Spectral.closureEmbedding_injective (V := D)
      (weightedDiskValueCLM_injective.comp Subtype.val_injective),
    KsIndex.Spectral.closureEmbedding_denseRange (V := D) _,
    KsIndex.Spectral.closureEmbedding_compact (V := D)
      (weightedDiskValueCLM_compact.comp_clm D.subtypeL)⟩

lemma weightedDiskAmbient_shift_coercive (D : Submodule ℂ ComplexH1)
    (V : BoundedRealPotential) (u : D) :
    ‖u‖ ^ 2 ≤ (weakJacobi V u u).re +
      (V.C + 1) * ‖weightedDiskAmbientEmbedding D u‖ ^ 2 :=
  weightedDiskJacobi_shift_coercive V u

end KsIndex.Spherical
