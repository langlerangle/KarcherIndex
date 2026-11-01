module

public import KsIndexLean.WeakH1Localization
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace

/-- A compact real test, regarded as a complex global L2 class. -/
def compactRealTestL2 (φ : ℂ → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Lp ℂ 2 (volume : Measure ℂ) :=
  ((Complex.continuous_ofReal.comp hφ).memLp_of_hasCompactSupport
    (hc.comp_left Complex.ofReal_zero)).toLp (fun z => (φ z : ℂ))

lemma compactRealTestL2_coe (φ : ℂ → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    (compactRealTestL2 φ hφ hc : ℂ → ℂ) =ᵐ[volume] (fun z => (φ z : ℂ)) :=
  MemLp.coeFn_toLp _

lemma compactRealTestL2_inner (φ : ℂ → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (f : Lp ℂ 2 (volume : Measure ℂ)) :
    inner ℂ (compactRealTestL2 φ hφ hc) f = ∫ z, φ z • f z := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [compactRealTestL2_coe φ hφ hc] with z hz
  rw [hz]
  simp [RCLike.inner_apply, Complex.real_smul, mul_comm]

lemma tendsto_integral_compact_test (φ : ℂ → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    {f : ℕ → Lp ℂ 2 (volume : Measure ℂ)} {g : Lp ℂ 2 (volume : Measure ℂ)}
    (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => ∫ z, φ z • f n z) atTop (𝓝 (∫ z, φ z • g z)) := by
  simp_rw [← compactRealTestL2_inner φ hφ hc]
  have h : Continuous (fun v : Lp ℂ 2 (volume : Measure ℂ) =>
      inner ℂ (compactRealTestL2 φ hφ hc) v) := continuous_const.inner continuous_id
  exact (h.tendsto g).comp hf

end KsIndex.Trace
