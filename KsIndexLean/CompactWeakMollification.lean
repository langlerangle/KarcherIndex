module

public import KsIndexLean.WeakL2ClosureRaw
public import TauCeti.Analysis.Sobolev.Mollification
public import TauCeti.MeasureTheory.Function.Lp.MollificationBridge

@[expose] public section


open Set MeasureTheory Filter Topology ContinuousLinearMap
open scoped Convolution ContDiff
noncomputable section
namespace KsIndex.Trace

/-- The actual smooth convolution, not merely an L2 class. -/
def compactMollify (φ : ContDiffBump (0 : ℂ)) (u : ℂ → ℂ) : ℂ → ℂ :=
  φ.normed volume ⋆[lsmul ℝ ℝ, volume] u

lemma compactMollify_smooth (φ : ContDiffBump (0 : ℂ)) {u : ℂ → ℂ}
    (hu : MemLp u 2 volume) : ContDiff ℝ ∞ (compactMollify φ u) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
    (hu.locallyIntegrable (by norm_num))

lemma compactMollify_support (φ : ContDiffBump (0 : ℂ)) {u : ℂ → ℂ}
    (hc : HasCompactSupport u) : HasCompactSupport (compactMollify φ u) :=
  φ.hasCompactSupport_normed.convolution _ hc

lemma compactMollify_memLp (φ : ContDiffBump (0 : ℂ)) {u : ℂ → ℂ}
    (hu : MemLp u 2 volume) (hc : HasCompactSupport u) :
    MemLp (compactMollify φ u) 2 volume :=
  (compactMollify_smooth φ hu).continuous.memLp_of_hasCompactSupport
    (compactMollify_support φ hc)

lemma compactMollify_toLp (φ : ContDiffBump (0 : ℂ)) {u : ℂ → ℂ}
    (hu : MemLp u 2 volume) (hc : HasCompactSupport u) :
    (compactMollify_memLp φ hu hc).toLp (compactMollify φ u) =
      TauCeti.normedBumpLp (by norm_num : (2 : ENNReal) ≠ ⊤) φ volume (hu.toLp u) := by
  apply Lp.ext
  exact (compactMollify_memLp φ hu hc).coeFn_toLp.trans
    (TauCeti.normedBumpLp_ae_eq_convolution (by norm_num) φ hu hc).symm

lemma compactMollify_tendsto {φ : ℕ → ContDiffBump (0 : ℂ)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) {u : ℂ → ℂ}
    (hu : MemLp u 2 volume) (hc : HasCompactSupport u) :
    Tendsto (fun n => (compactMollify_memLp (φ n) hu hc).toLp
      (compactMollify (φ n) u)) atTop (𝓝 (hu.toLp u)) := by
  have he : (fun n => (compactMollify_memLp (φ n) hu hc).toLp
      (compactMollify (φ n) u)) =
      (fun n => TauCeti.normedBumpLp (by norm_num : (2 : ENNReal) ≠ ⊤)
        (φ n) volume (hu.toLp u)) := by
    funext n
    exact compactMollify_toLp (φ n) hu hc
  rw [he]
  exact TauCeti.tendsto_normedBumpLp (by norm_num) hφ (hu.toLp u)

/-- The smooth derivative is the convolution of the actual weak derivative. -/
lemma compactMollify_hasLineDerivAt (φ : ContDiffBump (0 : ℂ))
    {u v : ℂ → ℂ} {d : ℂ}
    (hw : TauCeti.HasWeakLineDerivOn volume ⊤ u v d) (z : ℂ) :
    HasLineDerivAt ℝ (compactMollify φ u) (compactMollify φ v z) z d := by
  have h := hw.hasLineDerivAt_convolution_right (φ.normed volume)
    φ.contDiff_normed φ.hasCompactSupport_normed z
  simp only [convolution_flip] at h
  exact h

end KsIndex.Trace
