module

public import KsIndexLean.CompactTestL2

@[expose] public section


open Set MeasureTheory Filter Topology TopologicalSpace
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace

/-- Weak differentiation survives simultaneous strong L2 limits of values and derivatives. -/
theorem weakLine_of_tendsto_L2 {Ω : Opens ℂ} (d : ℂ)
    {f g : ℕ → Lp ℂ 2 (volume : Measure ℂ)} {u v : Lp ℂ 2 (volume : Measure ℂ)}
    (hw : ∀ n, TauCeti.HasWeakLineDerivOn volume Ω (f n) (g n) d)
    (hf : Tendsto f atTop (𝓝 u)) (hg : Tendsto g atTop (𝓝 v)) :
    TauCeti.HasWeakLineDerivOn volume Ω u v d := by
  rw [TauCeti.hasWeakLineDerivOn_iff_testFunction]
  refine ⟨inferInstance, ((Lp.memLp u).locallyIntegrable (by norm_num)).locallyIntegrableOn _,
    ((Lp.memLp v).locallyIntegrable (by norm_num)).locallyIntegrableOn _, ?_⟩
  intro φ
  have hd : Continuous (fun z => fderiv ℝ (φ : ℂ → ℝ) z d) :=
    (φ.contDiff.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have he (z : ℂ) : lineDeriv ℝ (φ : ℂ → ℝ) z d = fderiv ℝ (φ : ℂ → ℝ) z d :=
    (φ.contDiff.differentiable (by simp) z).lineDeriv_eq_fderiv
  have hleft := tendsto_integral_compact_test _ hd
    (φ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) d) hf
  have hright := (tendsto_integral_compact_test _ φ.contDiff.continuous φ.hasCompactSupport hg).neg
  have hseq : (fun n => ∫ z, fderiv ℝ (φ : ℂ → ℝ) z d • f n z) =
      (fun n => -(∫ z, (φ : ℂ → ℝ) z • g n z)) := by
    funext n
    have hn := (hw n).integral_lineDeriv_smul_eq_neg_integral_smul φ
    simpa only [he] using hn
  rw [hseq] at hleft
  simp_rw [he]
  exact tendsto_nhds_unique hleft hright

end KsIndex.Trace
