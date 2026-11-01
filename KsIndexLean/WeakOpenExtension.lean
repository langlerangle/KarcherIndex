module

public import KsIndexLean.WeakInteriorBounded
public import KsIndexLean.WeakLocalBootstrap

@[expose] public section


/-! Zero extension is used only to represent a local field as a tempered
distribution. Local cutoffs have support inside Ω; no boundary equation is asserted. -/
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped SchwartzMap
namespace KsIndex.Weq
open TemperedDistribution

def openExtend {Ω : Opens ℂ} (u : ℂ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ω : Set ℂ))) : Lp ℂ 2 (volume : Measure ℂ) :=
  ((memLp_indicator_iff_restrict Ω.isOpen.measurableSet).mpr hu).toLp

def openDist {Ω : Opens ℂ} (u : ℂ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ω : Set ℂ))) : 𝓢'(ℂ, ℂ) :=
  (openExtend u hu : 𝓢'(ℂ, ℂ))

lemma openExtend_ae {Ω : Opens ℂ} (u : ℂ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ω : Set ℂ))) :
    (openExtend u hu : ℂ → ℂ) =ᵐ[volume] (Ω : Set ℂ).indicator u :=
  ((memLp_indicator_iff_restrict Ω.isOpen.measurableSet).mpr hu).coeFn_toLp

lemma smulLeft_openDist_real_cutoff {Ω : Opens ℂ} {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (Ω : Set ℂ)))
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (Ω : Set ℂ)) :
    smulLeftCLM ℂ (fun z => (χ z : ℂ)) (openDist u hu) =
      ((KsIndex.Trace.memLp_continuous_mul_supported hχ.continuous hc hs hu).toLp :
        𝓢'(ℂ, ℂ)) := by
  have hcc := hc.comp_left (map_zero Complex.ofRealCLM)
  have hcd := Complex.ofRealCLM.contDiff.comp hχ
  have ht : (fun z => (χ z : ℂ)).HasTemperateGrowth := hcc.hasTemperateGrowth hcd
  ext φ
  rw [smulLeftCLM_apply_apply]
  change (openExtend u hu : 𝓢'(ℂ, ℂ)) (SchwartzMap.smulLeftCLM ℂ (fun z => (χ z : ℂ)) φ) = _
  rw [Lp.toTemperedDistribution_apply, toLp_distribution_apply]
  apply integral_congr_ae
  filter_upwards [openExtend_ae u hu] with z hz
  rw [SchwartzMap.smulLeftCLM_apply_apply ht, hz]
  by_cases hzo : z ∈ (Ω : Set ℂ)
  · simp [Set.indicator_of_mem hzo, Complex.real_smul, smul_eq_mul, mul_comm, mul_assoc]
  · have hzχ : χ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hzo (hs h))
    simp [Set.indicator_of_notMem hzo, hzχ]

theorem memSobolev_two_real_cutoff_openDist {Ω : Opens ℂ} {u ux uy q : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (Ω : Set ℂ)))
    (hx2 : MemLp ux 2 (volume.restrict (Ω : Set ℂ)))
    (hy2 : MemLp uy 2 (volume.restrict (Ω : Set ℂ)))
    (hq2 : MemLp q 2 (volume.restrict (Ω : Set ℂ)))
    (hx : TauCeti.HasWeakLineDerivOn volume Ω u ux 1)
    (hy : TauCeti.HasWeakLineDerivOn volume Ω u uy Complex.I)
    (heq : InteriorWeakEquation Ω ux uy q)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (Ω : Set ℂ)) :
    MemSobolev 2 2 (smulLeftCLM ℂ (fun z => (χ z : ℂ)) (openDist u hu)) := by
  rw [smulLeft_openDist_real_cutoff hu hχ hc hs]
  exact memSobolev_two_cutoff hu hx2 hy2 hq2 hx hy heq hχ hc hs

/-- A concrete weak jet and its interior divergence equation discharge the
bootstrap's local Sobolev hypothesis (in fact at order two). Complex cutoffs
are handled by real/imaginary decomposition, with the same interior support. -/
theorem localMemSobolev_two_openDist {Ω : Opens ℂ} {u ux uy q : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (Ω : Set ℂ)))
    (hx2 : MemLp ux 2 (volume.restrict (Ω : Set ℂ)))
    (hy2 : MemLp uy 2 (volume.restrict (Ω : Set ℂ)))
    (hq2 : MemLp q 2 (volume.restrict (Ω : Set ℂ)))
    (hx : TauCeti.HasWeakLineDerivOn volume Ω u ux 1)
    (hy : TauCeti.HasWeakLineDerivOn volume Ω u uy Complex.I)
    (heq : InteriorWeakEquation Ω ux uy q) :
    LocalMemSobolev (Ω : Set ℂ) 2 (openDist u hu) := by
  intro χ hχ hc hs
  have hr : ContDiff ℝ (⊤ : ℕ∞) (fun z => (χ z).re) :=
    Complex.reCLM.contDiff.comp hχ
  have hi : ContDiff ℝ (⊤ : ℕ∞) (fun z => (χ z).im) :=
    Complex.imCLM.contDiff.comp hχ
  have hrc : HasCompactSupport (fun z => (χ z).re) :=
    hc.comp_left (map_zero Complex.reCLM)
  have hic : HasCompactSupport (fun z => (χ z).im) :=
    hc.comp_left (map_zero Complex.imCLM)
  have hrs : tsupport (fun z => (χ z).re) ⊆ (Ω : Set ℂ) :=
    (tsupport_comp_subset (g := Complex.reCLM) (map_zero Complex.reCLM) χ).trans hs
  have his : tsupport (fun z => (χ z).im) ⊆ (Ω : Set ℂ) :=
    (tsupport_comp_subset (g := Complex.imCLM) (map_zero Complex.imCLM) χ).trans hs
  have hR := memSobolev_two_real_cutoff_openDist hu hx2 hy2 hq2 hx hy heq hr hrc hrs
  have hI := memSobolev_two_real_cutoff_openDist hu hx2 hy2 hq2 hx hy heq hi hic his
  have htR : (fun z => ((χ z).re : ℂ)).HasTemperateGrowth :=
    (hrc.comp_left (map_zero Complex.ofRealCLM)).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hr)
  have htI : (fun z => ((χ z).im : ℂ)).HasTemperateGrowth :=
    (hic.comp_left (map_zero Complex.ofRealCLM)).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hi)
  have htII : (Complex.I • (fun z => ((χ z).im : ℂ))).HasTemperateGrowth := by
    exact (Function.HasTemperateGrowth.const Complex.I).smul htI
  have he : χ = (fun z => ((χ z).re : ℂ)) +
      Complex.I • (fun z => ((χ z).im : ℂ)) := by
    funext z
    apply Complex.ext <;> simp
  rw [he, smulLeftCLM_add htR htII, add_apply,
    smulLeftCLM_smul htI, smul_apply]
  exact hR.add (hI.smul Complex.I)

end KsIndex.Weq
