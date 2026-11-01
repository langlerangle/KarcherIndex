module

public import KsIndexLean.WeakH1Adapter
public import KsIndexLean.EnergySmooth
public import KsIndexLean.GradEnergySmooth

@[expose] public section


open Set MeasureTheory
open scoped ContDiff

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1
open KsIndex.Surface KsIndex.FaithfulInjection

lemma energySmooth_copy_memLp {k m : ℕ} (u : EnergySmooth k m) (n : ZMod (2 * m)) :
    MemLp (u.val n) 2 (volume.restrict (WeakH1.disk : Set ℂ)) := by
  apply (memLp_two_iff_integrable_sq_norm
    ((u.property.1.1 n).continuousOn.aestronglyMeasurable Metric.isOpen_ball.measurableSet)).mpr
  exact u.property.2.2.1 n

lemma energySmooth_direction_memLp {k m : ℕ} (u : GradEnergySmooth k m) (n : ZMod (2 * m)) :
    MemLp (fun z => fderiv ℝ (u.val n) z 1) 2 (volume.restrict (WeakH1.disk : Set ℂ)) ∧
    MemLp (fun z => fderiv ℝ (u.val n) z Complex.I) 2 (volume.restrict (WeakH1.disk : Set ℂ)) := by
  have h1 : AEStronglyMeasurable (fun z => fderiv ℝ (u.val n) z 1) volume :=
    (measurable_fderiv_apply_const ℝ (u.val n) (1 : ℂ)).aestronglyMeasurable
  have hI : AEStronglyMeasurable (fun z => fderiv ℝ (u.val n) z Complex.I) volume :=
    (measurable_fderiv_apply_const ℝ (u.val n) Complex.I).aestronglyMeasurable
  constructor
  · apply (memLp_two_iff_integrable_sq_norm h1.restrict).mpr
    apply (u.property.2.1 n).mono' (h1.restrict.norm.pow 2)
    filter_upwards [] with z
    simp [Surface.gradSq]
  · apply (memLp_two_iff_integrable_sq_norm hI.restrict).mpr
    apply (u.property.2.1 n).mono' (hI.restrict.norm.pow 2)
    filter_upwards [] with z
    simp [Surface.gradSq]

def energySmoothCopyData {k m : ℕ} (u : EnergySmooth k m) (n : ZMod (2 * m)) : SmoothH1Data where
  F := u.val n
  smooth := u.property.1.1 n
  value_mem := energySmooth_copy_memLp u n
  dx_mem := (energySmooth_direction_memLp (esToGrad u) n).1
  dy_mem := (energySmooth_direction_memLp (esToGrad u) n).2

def energySmoothCopy {k m : ℕ} (u : EnergySmooth k m) (n : ZMod (2 * m)) : ComplexH1 :=
  smoothToH1 (energySmoothCopyData u n)

lemma energySmoothCopy_value_ae {k m : ℕ} (u : EnergySmooth k m) (n : ZMod (2 * m)) :
    (valueCLM (energySmoothCopy u n) : ℂ → ℂ) =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] u.val n :=
  smoothToH1_value_ae _

lemma energySmoothCopy_dx_ae {k m : ℕ} (u : EnergySmooth k m) (n : ZMod (2 * m)) :
    (dxCLM (energySmoothCopy u n) : ℂ → ℂ) =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)]
      (fun z => fderiv ℝ (u.val n) z 1) := smoothToH1_dx_ae _

lemma energySmoothCopy_dy_ae {k m : ℕ} (u : EnergySmooth k m) (n : ZMod (2 * m)) :
    (dyCLM (energySmoothCopy u n) : ℂ → ℂ) =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)]
      (fun z => fderiv ℝ (u.val n) z Complex.I) := smoothToH1_dy_ae _

end KsIndex.Trace
