module

public import KsIndexLean.SeamUpper
public import KsIndexLean.WeakH1Adapter

@[expose] public section


open Set MeasureTheory
open scoped ContDiff

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.SingleDisk

lemma continuous_memLp_disk {f : ℂ → ℂ} (hf : Continuous f) :
    MemLp f 2 (volume.restrict (disk : Set ℂ)) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable.restrict).mpr
  exact ((hf.norm.pow 2).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : ℂ) 1)).mono_set Metric.ball_subset_closedBall

/-- Finite energy follows from the existing natural-core extension theorem. -/
lemma natCc_memLp_jet {k : ℕ} (hk : 1 ≤ k) {b1 b0 : Bool} {f : ℂ → ℂ}
    (hf : f ∈ NatCc k b1 b0) :
    MemLp f 2 (volume.restrict (disk : Set ℂ)) ∧
    MemLp (fun z => fderiv ℝ f z 1) 2 (volume.restrict (disk : Set ℂ)) ∧
    MemLp (fun z => fderiv ℝ f z Complex.I) 2 (volume.restrict (disk : Set ℂ)) := by
  obtain ⟨G, hG, he⟩ := KsIndex.SeamUpper.natCc_extension hk hf
  have hd : ∀ z ∈ disk, fderiv ℝ f z = fderiv ℝ G z := by
    intro z hz
    exact (Filter.EventuallyEq.fderiv_eq
      (Filter.Eventually.mono (disk.isOpen.mem_nhds hz) (fun y hy => he y hy)))
  have hv : f =ᵐ[volume.restrict (disk : Set ℂ)] G := by
    filter_upwards [ae_restrict_mem disk.isOpen.measurableSet] with z hz
    exact he z hz
  have hdir (v : ℂ) : (fun z => fderiv ℝ f z v)
      =ᵐ[volume.restrict (disk : Set ℂ)] (fun z => fderiv ℝ G z v) := by
    filter_upwards [ae_restrict_mem disk.isOpen.measurableSet] with z hz
    rw [hd z hz]
  have hc : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by norm_num)
  exact ⟨(continuous_memLp_disk hG.continuous).ae_eq hv.symm,
    (continuous_memLp_disk (hc.clm_apply continuous_const)).ae_eq (hdir 1).symm,
    (continuous_memLp_disk (hc.clm_apply continuous_const)).ae_eq (hdir Complex.I).symm⟩

def naturalCoreData {k : ℕ} (hk : 1 ≤ k) {b1 b0 : Bool} (f : NatCc k b1 b0) :
    SmoothH1Data where
  F := f.val
  smooth := f.property.1
  value_mem := (natCc_memLp_jet hk f.property).1
  dx_mem := (natCc_memLp_jet hk f.property).2.1
  dy_mem := (natCc_memLp_jet hk f.property).2.2

def naturalCoreH1 {k : ℕ} (hk : 1 ≤ k) {b1 b0 : Bool} (f : NatCc k b1 b0) : ComplexH1 :=
  smoothToH1 (naturalCoreData hk f)

lemma naturalCoreH1_value_ae {k : ℕ} (hk : 1 ≤ k) {b1 b0 : Bool} (f : NatCc k b1 b0) :
    (valueCLM (naturalCoreH1 hk f) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f.val :=
  smoothToH1_value_ae _

lemma naturalCoreH1_dx_ae {k : ℕ} (hk : 1 ≤ k) {b1 b0 : Bool} (f : NatCc k b1 b0) :
    (dxCLM (naturalCoreH1 hk f) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
      (fun z => fderiv ℝ f.val z 1) := smoothToH1_dx_ae _

lemma naturalCoreH1_dy_ae {k : ℕ} (hk : 1 ≤ k) {b1 b0 : Bool} (f : NatCc k b1 b0) :
    (dyCLM (naturalCoreH1 hk f) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
      (fun z => fderiv ℝ f.val z Complex.I) := smoothToH1_dy_ae _

end KsIndex.Trace
