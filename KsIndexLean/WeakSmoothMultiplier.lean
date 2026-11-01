module

public import KsIndexLean.WeakHigherRegularity

@[expose] public section


/-! Smooth compactly supported multiplication in integer-order Sobolev spaces. -/
noncomputable section
open MeasureTheory
open scoped SchwartzMap LineDeriv Laplacian

namespace KsIndex.Weq
open TemperedDistribution

set_option backward.isDefEq.respectTransparency false in
lemma schwartz_lineDeriv_smulLeft {χ : ℂ → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (φ : 𝓢(ℂ, ℂ)) (d : ℂ) :
    ∂_{d} (SchwartzMap.smulLeftCLM ℂ χ φ) =
      SchwartzMap.smulLeftCLM ℂ (fun z => fderiv ℝ χ z d) φ +
        SchwartzMap.smulLeftCLM ℂ χ (∂_{d} φ) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ χ z d) :=
    (contDiff_infty_iff_fderiv.mp hχ).2.clm_apply contDiff_const
  have ht := hc.hasTemperateGrowth hχ
  have hdt := (hc.fderiv_apply (𝕜 := ℝ) d).hasTemperateGrowth hd
  ext z
  rw [SchwartzMap.lineDerivOp_apply, SchwartzMap.smulLeftCLM_apply ht]
  have he : HasLineDerivAt ℝ (fun w => χ w * φ w)
      (fderiv ℝ χ z d * φ z + χ z * fderiv ℝ (φ : ℂ → ℂ) z d) z d := by
    have hh := (ContinuousLinearMap.mul ℝ ℂ).hasFDerivAt_of_bilinear
      (hχ.differentiable (by simp) z).hasFDerivAt
      ((φ.smooth ⊤).differentiable (by simp) z).hasFDerivAt
    simpa [add_comm] using hh.hasLineDerivAt d
  simpa only [add_apply, SchwartzMap.smulLeftCLM_apply_apply ht,
    SchwartzMap.smulLeftCLM_apply_apply hdt, smul_eq_mul,
    SchwartzMap.lineDerivOp_apply,
    ((φ.smooth ⊤).differentiable (by simp) z).lineDeriv_eq_fderiv] using he.lineDeriv

/-- Leibniz rule on distributions, proved by duality against Schwartz tests. -/
theorem distribution_lineDeriv_smulLeft {χ : ℂ → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (f : 𝓢'(ℂ, ℂ)) (d : ℂ) :
    ∂_{d} (smulLeftCLM ℂ χ f) = smulLeftCLM ℂ χ (∂_{d} f) +
      smulLeftCLM ℂ (fun z => fderiv ℝ χ z d) f := by
  ext φ
  simp only [lineDerivOp_apply_apply, smulLeftCLM_apply_apply, add_apply,
    schwartz_lineDeriv_smulLeft hχ hc, map_neg, map_add]
  abel

/-- Compact smooth multipliers preserve every nonnegative integer Sobolev order. -/
theorem memSobolev_nat_smulLeft (n : ℕ) (f : 𝓢'(ℂ, ℂ)) {χ : ℂ → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hf : MemSobolev n 2 f) : MemSobolev n 2 (smulLeftCLM ℂ χ f) := by
  induction n generalizing f χ with
  | zero =>
    simp only [Nat.cast_zero] at hf ⊢
    obtain ⟨u, hu⟩ := memSobolev_zero_iff.mp hf
    rw [hu]
    have hχtop := hχ.continuous.memLp_top_of_hasCompactSupport hc (volume : Measure ℂ)
    apply memSobolev_zero_iff.mpr
    exact ⟨(hχtop.toLp : Lp ℂ ⊤ (volume : Measure ℂ)) • u,
      (Lp.toTemperedDistribution_smul_eq (hc.hasTemperateGrowth hχ) hχtop u).symm⟩
  | succ n ih =>
    have hs : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; rfl
    rw [hs] at hf ⊢
    obtain ⟨hf, hx, hy⟩ := memSobolev_add_one_iff.mp hf
    apply memSobolev_add_one_iff.mpr
    refine ⟨ih f hχ hc hf, ?_, ?_⟩
    · rw [distribution_lineDeriv_smulLeft hχ hc]
      exact (ih _ hχ hc hx).add (ih f
        ((contDiff_infty_iff_fderiv.mp hχ).2.clm_apply contDiff_const)
        (hc.fderiv_apply (𝕜 := ℝ) 1) hf)
    · rw [distribution_lineDeriv_smulLeft hχ hc]
      exact (ih _ hχ hc hy).add (ih f
        ((contDiff_infty_iff_fderiv.mp hχ).2.clm_apply contDiff_const)
        (hc.fderiv_apply (𝕜 := ℝ) Complex.I) hf)

/-- The Laplace commutator with a smooth compact multiplier. -/
theorem distribution_laplacian_smulLeft {χ : ℂ → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) (f : 𝓢'(ℂ, ℂ)) :
    Δ (smulLeftCLM ℂ χ f) = smulLeftCLM ℂ χ (Δ f) +
      (smulLeftCLM ℂ (fun z => fderiv ℝ χ z 1) (∂_{(1 : ℂ)} f) +
        smulLeftCLM ℂ (fun z => fderiv ℝ χ z 1) (∂_{(1 : ℂ)} f)) +
      (smulLeftCLM ℂ (fun z => fderiv ℝ χ z Complex.I) (∂_{Complex.I} f) +
        smulLeftCLM ℂ (fun z => fderiv ℝ χ z Complex.I) (∂_{Complex.I} f)) +
      smulLeftCLM ℂ (fun z => fderiv ℝ (fun w => fderiv ℝ χ w 1) z 1) f +
      smulLeftCLM ℂ (fun z => fderiv ℝ (fun w => fderiv ℝ χ w Complex.I) z Complex.I) f := by
  have hd (d : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ χ z d) :=
    (contDiff_infty_iff_fderiv.mp hχ).2.clm_apply contDiff_const
  simp only [distribution_laplacian_complex, distribution_lineDeriv_smulLeft hχ hc,
    LineDeriv.lineDerivOp_add, distribution_lineDeriv_smulLeft (hd 1)
      (hc.fderiv_apply (𝕜 := ℝ) 1), distribution_lineDeriv_smulLeft (hd Complex.I)
      (hc.fderiv_apply (𝕜 := ℝ) Complex.I), map_add]
  abel

end KsIndex.Weq
