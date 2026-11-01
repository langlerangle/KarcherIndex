module

public import KsIndexLean.FourierRadialFTC

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma interiorAnnulus_subset_disk {a b : ℝ} (hb : b ≤ 1) :
    annulusSet a b ⊆ (disk : Set ℂ) := by
  intro z hz
  have h := hz.2.trans_le hb
  simpa [disk, Metric.mem_ball, dist_zero_right] using h

lemma interiorAnnulus_memLp {a b : ℝ} (hb : b ≤ 1) (f : L2C) :
    MemLp f 2 (volume.restrict (annulusSet a b)) :=
  (Lp.memLp f).mono_measure (Measure.restrict_mono (interiorAnnulus_subset_disk hb) le_rfl)

def interiorDiskProfile (a b : ℝ) (u : ComplexH1) := sliceLp a b (valueCLM u)
def interiorDiskRadialProfile (a b : ℝ) (u : ComplexH1) :=
  sliceLp a b (radialField (Dxy (dxLp u) (dyLp u)))

lemma interiorDisk_weak_polar {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (u : ComplexH1) :
    IntervalIntegrable (interiorDiskProfile a b u) volume a b ∧
    IntervalIntegrable (interiorDiskRadialProfile a b u) volume a b ∧
    TauCeti.HasWeakLineDerivOn volume (intervalOpens a b)
      (interiorDiskProfile a b u) (interiorDiskRadialProfile a b u) 1 := by
  apply weak_polar_pullback ha hab
    ((carrier_hasJet u).mono (interiorAnnulus_subset_disk hb)) (interiorAnnulus_memLp hb (valueCLM u))
  · simpa using interiorAnnulus_memLp hb (dxLp u)
  · simpa using interiorAnnulus_memLp hb (dyLp u)

def interiorDiskRepresentative {a b : ℝ} (hab : a < b) (u : ComplexH1) :=
  representative hab (interiorDiskProfile a b u) (interiorDiskRadialProfile a b u)

lemma interiorDiskRepresentative_continuousOn {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (u : ComplexH1) :
    ContinuousOn (interiorDiskRepresentative hab u) (Icc a b) :=
  representative_continuousOn hab _ (interiorDisk_weak_polar ha hab hb u).2.1

lemma interiorDiskRepresentative_ae {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (u : ComplexH1) :
    interiorDiskProfile a b u =ᵐ[volume.restrict (Ioo a b)] interiorDiskRepresentative hab u :=
  representative_ae_eq hab (interiorDisk_weak_polar ha hab hb u).2.2
    (interiorDisk_weak_polar ha hab hb u).2.1

def interiorDiskMode {a b : ℝ} (hab : a < b) (u : ComplexH1) (n : ℤ) (r : ℝ) : ℂ :=
  circleCoefficientCLM n (interiorDiskRepresentative hab u r)

def interiorDiskRadialMode (a b : ℝ) (u : ComplexH1) (n : ℤ) (r : ℝ) : ℂ :=
  circleCoefficientCLM n (interiorDiskRadialProfile a b u r)

lemma interiorDiskMode_continuousOn {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (u : ComplexH1) (n : ℤ) :
    ContinuousOn (interiorDiskMode hab u n) (Icc a b) :=
  (circleCoefficientCLM n).continuous.comp_continuousOn
    (interiorDiskRepresentative_continuousOn ha hab hb u)

lemma interiorDiskMode_sub_eq_integral {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (u : ComplexH1) (n : ℤ)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    interiorDiskMode hab u n t - interiorDiskMode hab u n s =
      ∫ r in s..t, interiorDiskRadialMode a b u n r := by
  have hg := (interiorDisk_weak_polar ha hab hb u).2.1
  have hsub : uIcc s t ⊆ uIcc a b := by
    rw [uIcc_of_le hab.le]
    exact uIcc_subset_Icc hs ht
  have h := representative_sub_eq_integral hab (interiorDiskProfile a b u) hg hs ht
  change interiorDiskRepresentative hab u t - interiorDiskRepresentative hab u s = _ at h
  change circleCoefficientCLM n (interiorDiskRepresentative hab u t) -
    circleCoefficientCLM n (interiorDiskRepresentative hab u s) = _
  rw [← map_sub, h, ← (circleCoefficientCLM n).intervalIntegral_comp_comm (hg.mono_set hsub)]
  rfl

lemma interiorDiskMode_collar (u : ComplexH1) (n : ℤ) :
    interiorDiskMode (by norm_num : (1 / 2 : ℝ) < 1) u n = diskMode u n := rfl

/-- Nested annuli give the same representative, including their endpoints. -/
lemma interiorDiskRepresentative_nested {a b c d : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b) (u : ComplexH1) :
    EqOn (interiorDiskRepresentative hab u) (interiorDiskRepresentative hcd u) (Icc c d) := by
  have hc : 0 < c := ha.trans_le hac
  have hd : d ≤ 1 := hdb.trans hb
  have hs : Ioo c d ⊆ Ioo a b := Ioo_subset_Ioo hac hdb
  apply eqOn_Icc_of_ae_eq hcd
    ((interiorDiskRepresentative_continuousOn ha hab hb u).mono (Icc_subset_Icc hac hdb))
    (interiorDiskRepresentative_continuousOn hc hcd hd u)
  have houter := (interiorDiskRepresentative_ae ha hab hb u).filter_mono
    (ae_mono (Measure.restrict_mono hs le_rfl))
  filter_upwards [houter, interiorDiskRepresentative_ae hc hcd hd u,
    ae_restrict_mem measurableSet_Ioo] with r hr1 hr2 hr
  rw [← hr1, ← hr2]
  change sliceLp a b (valueCLM u) r = sliceLp c d (valueCLM u) r
  by_cases hm : MemLp (sliceFun (valueCLM u) r) 2 circleMeasure
  · rw [sliceLp_of_memLp (hs hr) hm, sliceLp_of_memLp hr hm]
  · simp [sliceLp, hm]

lemma interiorDiskMode_nested {a b c d : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b) (u : ComplexH1) (n : ℤ) :
    EqOn (interiorDiskMode hab u n) (interiorDiskMode hcd u n) (Icc c d) := by
  intro r hr
  exact congrArg (circleCoefficientCLM n)
    (interiorDiskRepresentative_nested ha hab hb hac hcd hdb u hr)

end KsIndex.Trace
