module

public import KsIndexLean.JacobiWeakTrace
public import KsIndexLean.DiskTraceCovariance

@[expose] public section


/-! Linear and rotation compatibility of the existing smooth disk embedding. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma globalSmoothH1_add {f g : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    globalSmoothH1 (f + g) (hf.add hg) = globalSmoothH1 f hf + globalSmoothH1 g hg := by
  apply valueCLM_injective
  rw [map_add]
  apply Lp.ext
  filter_upwards [globalSmoothH1_value (f + g) (hf.add hg), globalSmoothH1_value f hf,
    globalSmoothH1_value g hg, Lp.coeFn_add (valueCLM (globalSmoothH1 f hf))
      (valueCLM (globalSmoothH1 g hg))] with z h h1 h2 ha
  rw [h, ha]
  simp only [Pi.add_apply, h1, h2]

lemma globalSmoothH1_smul (c : ℂ) {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) :
    globalSmoothH1 (c • f) (contDiff_const.smul hf) = c • globalSmoothH1 f hf := by
  apply valueCLM_injective
  rw [map_smul]
  apply Lp.ext
  filter_upwards [globalSmoothH1_value (c • f) (contDiff_const.smul hf),
    globalSmoothH1_value f hf, Lp.coeFn_smul c (valueCLM (globalSmoothH1 f hf))]
    with z h h1 hc
  rw [h, hc]
  simp only [Pi.smul_apply, h1]

lemma globalSmoothH1_rotation (θ : ℝ) {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) :
    globalSmoothH1 (fun z => f (planeRotation θ z))
      (hf.comp (planeRotation θ).contDiff) = diskRotation θ (globalSmoothH1 f hf) := by
  apply valueCLM_injective
  apply Lp.ext
  have ha := (measurePreserving_planeRotation_disk θ).quasiMeasurePreserving.ae_eq_comp
    (globalSmoothH1_value f hf)
  filter_upwards [globalSmoothH1_value (fun z => f (planeRotation θ z))
    (hf.comp (planeRotation θ).contDiff), diskRotation_value_ae θ (globalSmoothH1 f hf), ha]
    with z h h1 h2
  exact h.trans (h1.trans h2).symm

end KsIndex.Trace
