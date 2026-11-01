module

public import KsIndexLean.DiskExtensionDerivativeBound
public import KsIndexLean.ExtendedSeamEnergy

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket KsIndex.SingleDisk

lemma diskExtension_value_memLp (u : ComplexH1) :
    MemLp (refl 1 (valueCLM u)) 2 (volume.restrict (Metric.ball (0 : ℂ) 2)) := by
  rw [← disk_union_reflection_annulus]
  apply memLp_two_union
  · apply MemLp.ae_eq _ (Lp.memLp (valueCLM u))
    filter_upwards [ae_restrict_mem disk.isOpen.measurableSet] with z hz
    exact (full_boundary_even_eq_inner u (KsIndex.SurfaceForm.mem_disk_iff.mp hz)).symm
  · exact full_boundary_even_value_memLp u

lemma diskExtension_direction_memLp (u : ComplexH1) (d : ℂ) :
    MemLp (fun z => diskExtensionJet u z d) 2
      (volume.restrict (Metric.ball (0 : ℂ) 2)) := by
  rw [← disk_union_reflection_annulus]
  apply memLp_two_union
  · have h : MemLp (fun z => Dxy (dxLp u) (dyLp u) z d) 2
        (volume.restrict (disk : Set ℂ)) :=
      ((Lp.memLp (dxLp u)).const_smul d.re).add ((Lp.memLp (dyLp u)).const_smul d.im)
    apply MemLp.ae_eq _ h
    filter_upwards [diskExtensionJet_inner u] with z hz
    exact congrArg (fun J : ℂ →L[ℝ] ℂ => J d) hz
  · apply MemLp.ae_eq _ (full_boundary_even_direction_memLp u d)
    filter_upwards [diskExtensionJet_annulus u] with z hz
    exact congrArg (fun J : ℂ →L[ℝ] ℂ => J d) hz

/-- Quantitative outer pullback estimate in the actual L2 norm. -/
lemma toLp_sigma_outer_norm_le {f : ℂ → ℂ}
    (hf : MemLp f 2 (volume.restrict (disk : Set ℂ))) :
    ‖(memLp_sigma_outer hf).toLp (f ∘ σ)‖ ≤
      ((16 : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal).toReal * ‖hf.toLp f‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp, ← ENNReal.toReal_mul]
  apply ENNReal.toReal_mono _ (eLpNorm_sigma_outer_le hf)
  exact ENNReal.mul_ne_top (by finiteness) hf.eLpNorm_lt_top.ne

end KsIndex.Trace
