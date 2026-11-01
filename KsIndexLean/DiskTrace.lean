module

public import KsIndexLean.PolarSliceAlgebra
public import KsIndexLean.WeakEndpointEstimate
public import KsIndexLean.WeakH1Adapter
public import KsIndexLean.SmoothEndpointAgreement

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma collar_subset_disk : annulusSet (1 / 2 : ℝ) 1 ⊆ (disk : Set ℂ) := by
  intro z hz
  simpa [disk, Metric.mem_ball, dist_zero_right] using hz.2

lemma collar_memLp (f : L2C) : MemLp f 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 1)) :=
  (Lp.memLp f).mono_measure (Measure.restrict_mono collar_subset_disk le_rfl)

def diskProfile (u : ComplexH1) : ℝ → Lp ℂ 2 circleMeasure :=
  sliceLp (1 / 2) 1 (valueCLM u)

def diskRadialProfile (u : ComplexH1) : ℝ → Lp ℂ 2 circleMeasure :=
  sliceLp (1 / 2) 1 (radialField (Dxy (dxLp u) (dyLp u)))

lemma disk_weak_polar (u : ComplexH1) :
    IntervalIntegrable (diskProfile u) volume (1 / 2) 1 ∧
    IntervalIntegrable (diskRadialProfile u) volume (1 / 2) 1 ∧
    TauCeti.HasWeakLineDerivOn volume (intervalOpens (1 / 2) 1)
      (diskProfile u) (diskRadialProfile u) 1 := by
  apply weak_polar_pullback (by norm_num) (by norm_num)
    ((carrier_hasJet u).mono collar_subset_disk) (collar_memLp (valueCLM u))
  · simpa using collar_memLp (dxLp u)
  · simpa using collar_memLp (dyLp u)

def diskRepresentative (u : ComplexH1) : ℝ → Lp ℂ 2 circleMeasure :=
  representative (by norm_num : (1 / 2 : ℝ) < 1) (diskProfile u) (diskRadialProfile u)

def diskTrace (u : ComplexH1) : Lp ℂ 2 circleMeasure := diskRepresentative u 1

lemma diskRepresentative_continuousOn (u : ComplexH1) :
    ContinuousOn (diskRepresentative u) (Icc (1 / 2 : ℝ) 1) :=
  representative_continuousOn (by norm_num) _ (disk_weak_polar u).2.1

lemma diskRepresentative_ae (u : ComplexH1) :
    diskProfile u =ᵐ[volume.restrict (Ioo (1 / 2 : ℝ) 1)] diskRepresentative u :=
  representative_ae_eq (by norm_num) (disk_weak_polar u).2.2 (disk_weak_polar u).2.1

lemma diskProfile_add_ae (u v : ComplexH1) :
    diskProfile (u + v) =ᵐ[volume.restrict (Ioo (1 / 2 : ℝ) 1)] diskProfile u + diskProfile v := by
  have h := Lp.coeFn_add (valueCLM u) (valueCLM v)
  have hc := h.filter_mono (ae_mono (Measure.restrict_mono collar_subset_disk le_rfl))
  dsimp [diskProfile]
  rw [map_add]
  filter_upwards [sliceLp_congr_ae (by norm_num : (0 : ℝ) < 1 / 2) hc,
    sliceLp_add_ae (by norm_num) (collar_memLp (valueCLM u))
      (collar_memLp (valueCLM v))] with t ht hs
  exact ht.trans hs

lemma diskProfile_smul_ae (c : ℂ) (u : ComplexH1) :
    diskProfile (c • u) =ᵐ[volume.restrict (Ioo (1 / 2 : ℝ) 1)] c • diskProfile u := by
  have h := Lp.coeFn_smul c (valueCLM u)
  have hc := h.filter_mono (ae_mono (Measure.restrict_mono collar_subset_disk le_rfl))
  dsimp [diskProfile]
  rw [map_smul]
  filter_upwards [sliceLp_congr_ae (by norm_num : (0 : ℝ) < 1 / 2) hc,
    sliceLp_smul_ae (by norm_num) c (collar_memLp (valueCLM u))] with t ht hs
  exact ht.trans hs

lemma diskTrace_add (u v : ComplexH1) : diskTrace (u + v) = diskTrace u + diskTrace v := by
  have he := eqOn_Icc_of_ae_eq (by norm_num : (1 / 2 : ℝ) < 1)
    (diskRepresentative_continuousOn (u + v))
    ((diskRepresentative_continuousOn u).add (diskRepresentative_continuousOn v))
  apply he ?_ (by norm_num)
  filter_upwards [diskRepresentative_ae (u + v), diskRepresentative_ae u,
    diskRepresentative_ae v, diskProfile_add_ae u v] with t hs hu hv ha
  rw [← hs, Pi.add_apply, ← hu, ← hv]
  exact ha

lemma diskTrace_smul (c : ℂ) (u : ComplexH1) : diskTrace (c • u) = c • diskTrace u := by
  have he := eqOn_Icc_of_ae_eq (by norm_num : (1 / 2 : ℝ) < 1)
    (diskRepresentative_continuousOn (c • u))
    ((diskRepresentative_continuousOn u).const_smul c)
  apply he ?_ (by norm_num)
  filter_upwards [diskRepresentative_ae (c • u), diskRepresentative_ae u,
    diskProfile_smul_ae c u] with t hs hu hc
  rw [← hs, Pi.smul_apply, ← hu]
  exact hc

end KsIndex.Trace
