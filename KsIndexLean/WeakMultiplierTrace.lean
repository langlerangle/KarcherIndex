module

public import KsIndexLean.CircleMultiplierFamily
public import KsIndexLean.DiskTraceBound
public import KsIndexLean.WeakDiskCutoff

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.PunctureCutoff KsIndex.FaithfulInjection

lemma diskProfile_mul_ae (χ : ℂ → ℝ) (hχ : Continuous χ) {u v : ComplexH1}
    (hv : (valueCLM v : ℂ → ℂ) =ᵐ[volume.restrict disk]
      (fun z => χ z • valueCLM u z)) :
    diskProfile v =ᵐ[volume.restrict (Ioo (1 / 2 : ℝ) 1)]
      (fun r => circleMul (radialCircleMultiplier χ hχ r) (diskProfile u r)) := by
  have hc := hv.filter_mono (ae_mono (Measure.restrict_mono collar_subset_disk le_rfl))
  filter_upwards [sliceLp_coe_ae (by norm_num : (0 : ℝ) < 1 / 2)
    (collar_memLp (valueCLM v)),
    sliceLp_coe_ae (by norm_num : (0 : ℝ) < 1 / 2) (collar_memLp (valueCLM u)),
    ae_slice_ae_eq (by norm_num : (0 : ℝ) < 1 / 2) hc] with r hv hu he
  apply Lp.ext
  filter_upwards [hv, hu, he,
    circleMul_coe (radialCircleMultiplier χ hχ r) (diskProfile u r)] with w hv hu he hm
  rw [hm]
  change sliceLp (1 / 2) 1 (valueCLM v) r w =
    χ (r • (w : ℂ)) • sliceLp (1 / 2) 1 (valueCLM u) r w
  rw [hv, hu]
  exact he

/-- The genuine weak trace respects multiplication whenever the actual H1 value
classes satisfy the product relation. No smooth density is used. -/
theorem diskTrace_mul_of_value (χ : ℂ → ℝ) (hχ : Continuous χ) {u v : ComplexH1}
    (hv : (valueCLM v : ℂ → ℂ) =ᵐ[volume.restrict disk]
      (fun z => χ z • valueCLM u z)) :
    diskTraceCLM v = circleMul (radialCircleMultiplier χ hχ 1) (diskTraceCLM u) := by
  have hc : ContinuousOn
      (fun r => circleMul (radialCircleMultiplier χ hχ r) (diskRepresentative u r))
      (Icc (1 / 2 : ℝ) 1) :=
    continuous_circleMul.comp_continuousOn
      ((continuous_radialCircleMultiplier χ hχ).continuousOn.prodMk
        (diskRepresentative_continuousOn u))
  have he := eqOn_Icc_of_ae_eq (by norm_num : (1 / 2 : ℝ) < 1)
    (diskRepresentative_continuousOn v) hc
  apply he ?_ (by norm_num)
  filter_upwards [diskRepresentative_ae u, diskRepresentative_ae v,
    diskProfile_mul_ae χ hχ hv] with r hu hv hp
  rw [← hu, ← hv]
  exact hp

lemma diskCutoff_trace (k j : ℕ) (u : ComplexH1) :
    diskTraceCLM (diskCutoff k j u) =
      circleMul (radialCircleMultiplier (cutP k (cutoffEps j))
        (cutP_contDiff k (cutoffEps_pos j) (cutoffEps_lt_one j)).continuous 1) (diskTraceCLM u) :=
  diskTrace_mul_of_value _ _ (diskCutoff_value_ae k j u)

end KsIndex.Trace
