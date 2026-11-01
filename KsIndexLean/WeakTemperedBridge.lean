module

public import KsIndexLean.WeakComplexTest
public import KsIndexLean.WeakH1Adapter
public import KsIndexLean.WeakH1Localization
public import Mathlib.Analysis.Distribution.Sobolev

@[expose] public section


open KsIndex.WeakH1 KsIndex.Trace MeasureTheory
open scoped SchwartzMap LineDeriv

/-! # Disk fields as tempered distributions

An `L²` disk field is extended by zero and paired with Schwartz tests using the
bilinear integral `∫ φ(x) * g(x)`, without complex conjugation of the test.
The pairing and directional-derivative formulas apply to arbitrary disk `L²` fields.

For a `ComplexH1` field localized by a smooth, real-valued, compactly supported cutoff
whose topological support lies inside the open disk, `diskDist_lineDeriv_eq` identifies
the distributional derivative with the zero extension of the Leibniz weak derivative.
The interior-support hypothesis is part of this theorem; it is not a formula for the
zero extension of an arbitrary field with nonzero boundary trace.

Contribution credit: entry and pairing contributions by Kai; weak-derivative proof
contributions by Astra. -/
namespace KsIndex.Weq

lemma measurableSet_disk : MeasurableSet (disk : Set ℂ) := by
  unfold disk; exact measurableSet_ball

noncomputable def diskExtend (g : ℂ → ℂ)
    (hg : MemLp g 2 (volume.restrict (disk : Set ℂ))) :
    Lp ℂ 2 (volume : Measure ℂ) :=
  (((memLp_indicator_iff_restrict (p := 2) (μ := (volume : Measure ℂ))
      measurableSet_disk).mpr hg)).toLp

noncomputable def diskDist (g : ℂ → ℂ)
    (hg : MemLp g 2 (volume.restrict (disk : Set ℂ))) :
    𝓢'(ℂ, ℂ) :=
  Lp.toTemperedDistribution (diskExtend g hg)

/-- The `diskExtend` function is a.e. the indicator of the disk times `g`. -/
lemma diskExtend_ae (g : ℂ → ℂ) (hg : MemLp g 2 (volume.restrict (disk : Set ℂ))) :
    (diskExtend g hg : ℂ → ℂ) =ᵐ[volume] (disk : Set ℂ).indicator g := by
  have hind : MemLp ((disk : Set ℂ).indicator g) 2 (volume : Measure ℂ) :=
    (memLp_indicator_iff_restrict (p := 2) (μ := (volume : Measure ℂ))
      measurableSet_disk).mpr hg
  exact hind.coeFn_toLp

/-- The disk distribution pairs against a Schwartz test as the
disk integral. -/
lemma diskDist_apply (g : ℂ → ℂ) (hg : MemLp g 2 (volume.restrict (disk : Set ℂ)))
    (φ : 𝓢(ℂ, ℂ)) :
    diskDist g hg φ = ∫ x in (disk : Set ℂ), φ x • g x := by
  rw [diskDist, Lp.toTemperedDistribution_apply]
  rw [← integral_indicator measurableSet_disk]
  apply integral_congr_ae
  filter_upwards [diskExtend_ae g hg] with x hx
  rw [hx]
  by_cases hxd : x ∈ (disk : Set ℂ)
  · rw [Set.indicator_of_mem hxd, Set.indicator_of_mem hxd]
  · rw [Set.indicator_of_notMem hxd, Set.indicator_of_notMem hxd, smul_zero]

/-- The directional distributional derivative of the disk distribution pairs as
minus the disk integral of the test's line derivative. -/
lemma diskDist_lineDeriv_apply (g : ℂ → ℂ)
    (hg : MemLp g 2 (volume.restrict (disk : Set ℂ))) (φ : 𝓢(ℂ, ℂ)) (m : ℂ) :
    (∂_{m} (diskDist g hg)) φ = -∫ x in (disk : Set ℂ), (∂_{m} φ) x • g x := by
  rw [TemperedDistribution.lineDerivOp_apply_apply, diskDist_apply, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with x
  rw [neg_apply, neg_smul]

/-- The distributional `m`-derivative of the cutoff field's disk distribution is the disk distribution
of the (Leibniz) weak-jet applied to `m`. Inputs from `diskH1_localization`. -/
theorem diskDist_lineDeriv_eq (u : ComplexH1) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (disk : Set ℂ)) (m : ℂ) :
    ∂_{m} (diskDist (fun z => χ z • valueCLM u z)
        ((diskH1_localization u hχ hc hs).2.1.restrict _))
      = diskDist (fun z => (χ z • Dxy (dxLp u) (dyLp u) z
          + (fderiv ℝ χ z).smulRight (valueCLM u z)) m)
        (((diskH1_localization u hχ hc hs).2.2 m).restrict _) := by
  ext φ
  rw [diskDist_lineDeriv_apply, diskDist_apply]
  have hleft : ∀ z ∉ (disk : Set ℂ), (∂_{m} φ) z • (χ z • valueCLM u z) = 0 := by
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hs h))]
    simp
  have hright : ∀ z ∉ (disk : Set ℂ),
      φ z • ((χ z • Dxy (dxLp u) (dyLp u) z +
        (fderiv ℝ χ z).smulRight (valueCLM u z)) m) = 0 := by
    intro z hz
    have hzχ : z ∉ tsupport χ := fun h => hz (hs h)
    have hd : fderiv ℝ χ z m = 0 := by
      rw [fderiv_of_notMem_tsupport ℝ hzχ]
      rfl
    simp [image_eq_zero_of_notMem_tsupport hzχ, hd]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hleft,
    setIntegral_eq_integral_of_forall_compl_eq_zero hright]
  have he := WeakComplexTest.localized_integral_lineDeriv_mul
    ((carrier_hasJet u).hasWeakLineDerivOn m) hχ hc hs (φ.smooth ⊤)
  simp only [SchwartzMap.lineDerivOp_apply, smul_eq_mul]
  change -(∫ z, lineDeriv ℝ (φ : ℂ → ℂ) z m * (χ z • valueCLM u z)) =
    ∫ z, φ z * (χ z • Dxy (dxLp u) (dyLp u) z m +
      fderiv ℝ χ z m • valueCLM u z)
  rw [he, neg_neg]

end KsIndex.Weq
