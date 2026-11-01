module

public import KsIndexLean.WeakRealEquation
public import KsIndexLean.WeakInteriorSmooth

@[expose] public section


/-! Smooth local representatives for the actual real W¹,² weak-solution
predicate used by puncture removal. No distributional regularity input remains. -/
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace KsIndex.Weq

/-- The weak solution supplied by puncture removal is represented by a real
smooth function near every interior point, for a smooth coordinate potential. -/
theorem exists_smooth_near_of_isWeakSolOn {Ω : Opens ℂ} {V : ℂ → ℝ}
    (u : TauCeti.W1p (volume : Measure ℂ) Ω 2)
    (hq : MemLp (fun z => V z * TauCeti.W1p.value u z) 2
      (volume.restrict (Ω : Set ℂ)))
    (he : PunctureRemoval.IsWeakSolOn V Ω u)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) {z : ℂ} (hz : z ∈ (Ω : Set ℂ)) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ (Ω : Set ℂ) ∧ ∃ g : ℂ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) g ∧
      (TauCeti.W1p.value u : ℂ → ℝ) =ᵐ[volume.restrict (Metric.ball z r)] g := by
  have hx : TauCeti.HasWeakLineDerivOn volume Ω (TauCeti.W1p.value u)
      (fun z => (TauCeti.W1p.gradient u z).re) 1 := by
    simpa only [JacobiMode.innerSL_one] using (TauCeti.W1p.hasWeakFDerivOn u).hasWeakLineDerivOn 1
  have hy : TauCeti.HasWeakLineDerivOn volume Ω (TauCeti.W1p.value u)
      (fun z => (TauCeti.W1p.gradient u z).im) Complex.I := by
    simpa only [JacobiMode.innerSL_I] using (TauCeti.W1p.hasWeakFDerivOn u).hasWeakLineDerivOn Complex.I
  have hqc : MemLp (fun z => (V z : ℂ) * (TauCeti.W1p.value u z : ℂ)) 2
      (volume.restrict (Ω : Set ℂ)) := by
    simp_rw [← Complex.ofReal_mul]
    exact hq.ofReal
  have hec : InteriorWeakEquation Ω
      (fun z => ((TauCeti.W1p.gradient u z).re : ℂ))
      (fun z => ((TauCeti.W1p.gradient u z).im : ℂ))
      (fun z => (V z : ℂ) * (TauCeti.W1p.value u z : ℂ)) := by
    simpa only [Complex.ofReal_mul] using interiorWeakEquation_of_isWeakSolOn u hq he
  obtain ⟨r, hr, hs, g, hg, ha⟩ := exists_smooth_near_of_interior_weak_jet
    (Lp.memLp (TauCeti.W1p.value u)).ofReal
    (Lp.memLp (TauCeti.W1p.gradient u)).re.ofReal
    (Lp.memLp (TauCeti.W1p.gradient u)).im.ofReal hqc
    (weakLineDeriv_ofReal hx) (weakLineDeriv_ofReal hy) hec
    (Complex.ofRealCLM.contDiff.comp hV) hz
  refine ⟨r, hr, hs, fun x => (g x).re, Complex.reCLM.contDiff.comp hg, ?_⟩
  filter_upwards [ha] with x hx'
  exact congrArg Complex.re hx'

end KsIndex.Weq
