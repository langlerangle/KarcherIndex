module

public import KsIndexLean.WeakL2Closure

@[expose] public section


open Set MeasureTheory Filter Topology TopologicalSpace
noncomputable section
namespace KsIndex.Trace

/-- Representative-level form of weak directional closure; the L2 convergence assumptions
refer to the actual classes determined by the given functions. -/
theorem weakLine_of_tendsto_toLp {Ω : Opens ℂ} (d : ℂ)
    {f g : ℕ → ℂ → ℂ} {u v : ℂ → ℂ}
    (hf : ∀ n, MemLp (f n) 2 volume) (hg : ∀ n, MemLp (g n) 2 volume)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hw : ∀ n, TauCeti.HasWeakLineDerivOn volume Ω (f n) (g n) d)
    (hft : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hu.toLp u)))
    (hgt : Tendsto (fun n => (hg n).toLp (g n)) atTop (𝓝 (hv.toLp v))) :
    TauCeti.HasWeakLineDerivOn volume Ω u v d := by
  have hw' (n : ℕ) : TauCeti.HasWeakLineDerivOn volume Ω
      ((hf n).toLp (f n)) ((hg n).toLp (g n)) d :=
    ((hw n).congr_ae (ae_restrict_of_ae (hf n).coeFn_toLp.symm)).congr_ae_deriv
      (ae_restrict_of_ae (hg n).coeFn_toLp.symm)
  have hl := weakLine_of_tendsto_L2 d hw' hft hgt
  exact (hl.congr_ae (ae_restrict_of_ae hu.coeFn_toLp)).congr_ae_deriv
    (ae_restrict_of_ae hv.coeFn_toLp)

/-- Simultaneous L2 limits preserve the full actual weak Frechet derivative,
direction by direction. -/
theorem weakF_of_tendsto_toLp {Ω : Opens ℂ}
    {f : ℕ → ℂ → ℂ} {u : ℂ → ℂ}
    {G : ℕ → ℂ → ℂ →L[ℝ] ℂ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (hf : ∀ n, MemLp (f n) 2 volume) (hu : MemLp u 2 volume)
    (hG : ∀ n d, MemLp (fun z => G n z d) 2 volume)
    (hU : ∀ d, MemLp (fun z => U z d) 2 volume)
    (hw : ∀ n, TauCeti.HasWeakFDerivOn volume Ω (f n) (G n))
    (hft : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hu.toLp u)))
    (hGt : ∀ d, Tendsto (fun n => (hG n d).toLp (fun z => G n z d)) atTop
      (𝓝 ((hU d).toLp (fun z => U z d)))) :
    TauCeti.HasWeakFDerivOn volume Ω u U := by
  rw [TauCeti.hasWeakFDerivOn_iff]
  intro d
  exact weakLine_of_tendsto_toLp d hf (fun n => hG n d) hu (hU d)
    (fun n => (hw n).hasWeakLineDerivOn d) hft (hGt d)

end KsIndex.Trace
