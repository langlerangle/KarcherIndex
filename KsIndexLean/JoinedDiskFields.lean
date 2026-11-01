module

public import KsIndexLean.RawProfileAlgebra

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

def diskRadialRaw (u : ComplexH1) : ℂ → ℂ := radialField (Dxy (dxLp u) (dyLp u))
def diskAngularRaw (u : ComplexH1) : ℂ → ℂ := angularField (Dxy (dxLp u) (dyLp u))

lemma measurable_diskRadialRaw (u : ComplexH1) : Measurable (diskRadialRaw u) := by
  change Measurable (fun z => (z.re / ‖z‖) • Dxy (dxLp u) (dyLp u) z 1 +
    (z.im / ‖z‖) • Dxy (dxLp u) (dyLp u) z Complex.I)
  simp only [Dxy_one, Dxy_I]
  exact
    ((Complex.continuous_re.measurable.div measurable_norm).smul
      (Lp.stronglyMeasurable (dxLp u)).measurable).add
    ((Complex.continuous_im.measurable.div measurable_norm).smul
      (Lp.stronglyMeasurable (dyLp u)).measurable)

lemma measurable_diskAngularRaw (u : ComplexH1) : Measurable (diskAngularRaw u) := by
  change Measurable (fun z => (-z.im) • Dxy (dxLp u) (dyLp u) z 1 +
    z.re • Dxy (dxLp u) (dyLp u) z Complex.I)
  simp only [Dxy_one, Dxy_I]
  exact
    (Complex.continuous_im.measurable.neg.smul (Lp.stronglyMeasurable (dxLp u)).measurable).add
    (Complex.continuous_re.measurable.smul (Lp.stronglyMeasurable (dyLp u)).measurable)

lemma memLp_diskRadialRaw (u : ComplexH1) :
    MemLp (diskRadialRaw u) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 1)) := by
  apply memLp_radialField (by norm_num : (0 : ℝ) < 1 / 2)
  · simpa using collar_memLp (dxLp u)
  · simpa using collar_memLp (dyLp u)

lemma memLp_diskAngularRaw (u : ComplexH1) :
    MemLp (diskAngularRaw u) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 1)) :=
  diskAngularField_memLp u

def joinedDiskValue (u v : ComplexH1) (c : ℂ) : ℂ → ℂ :=
  radialJoin 1 (valueCLM u) (fun z => c • valueCLM v (radialInversion z))

def joinedDiskRadial (u v : ComplexH1) (c : ℂ) : ℂ → ℂ :=
  radialJoin 1 (diskRadialRaw u) (fun z => c • invertedRadialField (diskRadialRaw v) z)

def joinedDiskAngular (u v : ComplexH1) (c : ℂ) : ℂ → ℂ :=
  radialJoin 1 (diskAngularRaw u) (fun z => c • diskAngularRaw v (radialInversion z))

lemma memLp_joinedDiskValue (u v : ComplexH1) (c : ℂ) :
    MemLp (joinedDiskValue u v c) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)) := by
  apply memLp_radialJoin (by norm_num) (by norm_num) (by norm_num)
    (Lp.stronglyMeasurable (valueCLM u)).measurable
    (measurable_const.smul ((Lp.stronglyMeasurable (valueCLM v)).measurable.comp
      measurable_radialInversion)) (collar_memLp (valueCLM u))
    ((memLp_raw_radialInversion (Lp.stronglyMeasurable (valueCLM v)).measurable
      (collar_memLp (valueCLM v))).const_smul c)

lemma memLp_joinedDiskRadial (u v : ComplexH1) (c : ℂ) :
    MemLp (joinedDiskRadial u v c) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)) := by
  apply memLp_radialJoin (by norm_num) (by norm_num) (by norm_num)
    (measurable_diskRadialRaw u)
    (measurable_const.smul (measurable_invertedRadialField (measurable_diskRadialRaw v)))
    (memLp_diskRadialRaw u)
    ((memLp_invertedRadialField (measurable_diskRadialRaw v) (memLp_diskRadialRaw v)).const_smul c)

lemma memLp_joinedDiskAngular (u v : ComplexH1) (c : ℂ) :
    MemLp (joinedDiskAngular u v c) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)) := by
  apply memLp_radialJoin (by norm_num) (by norm_num) (by norm_num)
    (measurable_diskAngularRaw u)
    (measurable_const.smul ((measurable_diskAngularRaw v).comp measurable_radialInversion))
    (memLp_diskAngularRaw u)
    ((memLp_raw_radialInversion (measurable_diskAngularRaw v)
      (memLp_diskAngularRaw v)).const_smul c)

lemma raw_joinedDiskValue (u v : ComplexH1) (c : ℂ) :
    ∀ᵐ r ∂volume.restrict (Ioo (1 / 2 : ℝ) 2),
      sliceFun (joinedDiskValue u v c) r =ᵐ[circleMeasure]
        (joinAt 1 (diskProfile u) (fun t => c • diskProfile v t⁻¹) r : Lp ℂ 2 circleMeasure) :=
  ae_raw_join_profile (by norm_num) (ae_raw_sliceLp (by norm_num) (collar_memLp (valueCLM u)))
    (ae_raw_smul_profile c (ae_raw_inverted_slice (collar_memLp (valueCLM v))))

lemma raw_joinedDiskRadial (u v : ComplexH1) (c : ℂ) :
    ∀ᵐ r ∂volume.restrict (Ioo (1 / 2 : ℝ) 2),
      sliceFun (joinedDiskRadial u v c) r =ᵐ[circleMeasure]
        (joinAt 1 (diskRadialProfile u)
          (fun t => c • invertedRadialDeriv (diskRadialProfile v) t) r : Lp ℂ 2 circleMeasure) :=
  ae_raw_join_profile (by norm_num) (ae_raw_sliceLp (by norm_num) (memLp_diskRadialRaw u))
    (ae_raw_smul_profile c (ae_raw_inverted_radial_slice (memLp_diskRadialRaw v)))

lemma raw_joinedDiskAngular (u v : ComplexH1) (c : ℂ) :
    ∀ᵐ r ∂volume.restrict (Ioo (1 / 2 : ℝ) 2),
      sliceFun (joinedDiskAngular u v c) r =ᵐ[circleMeasure]
        (joinAt 1 (diskAngularProfile u)
          (fun t => c • diskAngularProfile v t⁻¹) r : Lp ℂ 2 circleMeasure) :=
  ae_raw_join_profile (by norm_num) (ae_raw_sliceLp (by norm_num) (memLp_diskAngularRaw u))
    (ae_raw_smul_profile c (ae_raw_inverted_slice (memLp_diskAngularRaw v)))

end KsIndex.Trace
