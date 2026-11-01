module

public import KsIndexLean.BoundedH1Approximation
public import KsIndexLean.WeakMultiplierTrace

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma diskProfile_comp_ae {F : ℂ → ℂ} {C : NNReal}
    (hF : LipschitzWith C F) (h0 : F 0 = 0) {u v : ComplexH1}
    (hv : (valueCLM v : ℂ → ℂ) =ᵐ[volume.restrict disk] (F ∘ valueCLM u)) :
    diskProfile v =ᵐ[volume.restrict (Ioo (1 / 2 : ℝ) 1)]
      (fun r => hF.compLp h0 (diskProfile u r)) := by
  have hc := hv.filter_mono (ae_mono (Measure.restrict_mono collar_subset_disk le_rfl))
  filter_upwards [sliceLp_coe_ae (by norm_num : (0 : ℝ) < 1 / 2)
    (collar_memLp (valueCLM v)),
    sliceLp_coe_ae (by norm_num : (0 : ℝ) < 1 / 2) (collar_memLp (valueCLM u)),
    ae_slice_ae_eq (by norm_num : (0 : ℝ) < 1 / 2) hc] with r hv hu he
  apply Lp.ext
  filter_upwards [hv, hu, he, hF.coeFn_compLp h0 (diskProfile u r)] with w hv hu he hm
  rw [hm]
  change sliceLp (1 / 2) 1 (valueCLM v) r w = F (sliceLp (1 / 2) 1 (valueCLM u) r w)
  rw [hv, hu]
  exact he

/-- The actual weak disk trace commutes with zero-fixing Lipschitz composition whenever
the composed value has an H1 realization. The proof does not use smooth density. -/
theorem diskTrace_comp_of_value {F : ℂ → ℂ} {C : NNReal}
    (hF : LipschitzWith C F) (h0 : F 0 = 0) {u v : ComplexH1}
    (hv : (valueCLM v : ℂ → ℂ) =ᵐ[volume.restrict disk] (F ∘ valueCLM u)) :
    diskTraceCLM v = hF.compLp h0 (diskTraceCLM u) := by
  have hc : ContinuousOn (fun r => hF.compLp h0 (diskRepresentative u r))
      (Icc (1 / 2 : ℝ) 1) :=
    (hF.continuous_compLp h0).comp_continuousOn (diskRepresentative_continuousOn u)
  have he := eqOn_Icc_of_ae_eq (by norm_num : (1 / 2 : ℝ) < 1)
    (diskRepresentative_continuousOn v) hc
  apply he ?_ (by norm_num)
  filter_upwards [diskRepresentative_ae u, diskRepresentative_ae v,
    diskProfile_comp_ae hF h0 hv] with r hu hv hp
  rw [← hu, ← hv]
  exact hp

lemma diskRadial_trace (t : ℝ) (ht : 0 ≤ t) (u : ComplexH1) :
    diskTraceCLM (diskRadial t ht u) =
      (radialTruncate_lipschitz ht).compLp (radialTruncate_zero t) (diskTraceCLM u) :=
  diskTrace_comp_of_value (radialTruncate_lipschitz ht) (radialTruncate_zero t)
    (diskRadial_value_ae t ht u)

end KsIndex.Trace
