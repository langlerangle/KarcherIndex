module

public import KsIndexLean.WeakInteriorBounded
public import KsIndexLean.PunctureRemoval
public import KsIndexLean.JacobiMode

@[expose] public section


/-! Real weak equations supplied by puncture removal, viewed as complex equations. -/
noncomputable section
open MeasureTheory TopologicalSpace
open scoped Distributions LineDeriv BoundedContinuousFunction

namespace KsIndex.Weq

lemma weakLineDeriv_ofReal {Ω : Opens ℂ} {u v : ℂ → ℝ} {d : ℂ}
    (h : TauCeti.HasWeakLineDerivOn volume Ω u v d) :
    TauCeti.HasWeakLineDerivOn volume Ω (fun z => (u z : ℂ)) (fun z => (v z : ℂ)) d := by
  apply (TauCeti.hasWeakLineDerivOn_iff
    (Complex.ofRealCLM.locallyIntegrableOn_comp h.locallyIntegrableOn)
    (Complex.ofRealCLM.locallyIntegrableOn_comp h.locallyIntegrableOn_deriv)).mpr
  intro φ hφ hc hs
  have he := h.integral_lineDeriv_smul_eq_neg_integral_smul ⟨φ, hφ, hc, hs⟩
  change (∫ x, lineDeriv ℝ φ x d * u x) = -∫ x, φ x * v x at he
  simpa only [Function.comp_apply, Complex.ofRealCLM_apply, Complex.real_smul,
    ← Complex.ofReal_mul, integral_complex_ofReal,
    Complex.ofReal_neg] using congrArg Complex.ofReal he

lemma test_fderiv_integrable {Ω : Opens ℂ} (ψ : 𝓓(Ω, ℂ)) {f : ℂ → ℂ}
    (hf : LocallyIntegrableOn f Ω volume) (d : ℂ) :
    Integrable (fun z => fderiv ℝ (ψ : ℂ → ℂ) z d * f z) := by
  have h := (TestFunction.lineDerivCLM ℝ d ψ : 𝓓(Ω, ℂ)).integrable_bilin
    (ContinuousLinearMap.mul ℝ ℂ) hf
  convert h using 1
  ext z
  simp only [ContinuousLinearMap.mul_apply', TestFunction.lineDerivCLM_apply]
  simp [(ψ.contDiff.differentiable (by simp) z).lineDeriv_eq_fderiv]

lemma interiorWeakEquation_of_real {Ω : Opens ℂ} {ux uy q : ℂ → ℝ}
    (hx : LocallyIntegrableOn ux Ω volume) (hy : LocallyIntegrableOn uy Ω volume)
    (hq : LocallyIntegrableOn q Ω volume)
    (he : ∀ ψ : 𝓓(Ω, ℝ),
      (∫ z, fderiv ℝ (ψ : ℂ → ℝ) z 1 * ux z +
        fderiv ℝ (ψ : ℂ → ℝ) z Complex.I * uy z - ψ z * q z) = 0) :
    InteriorWeakEquation Ω (fun z => (ux z : ℂ)) (fun z => (uy z : ℂ))
      (fun z => (q z : ℂ)) := by
  intro ψ
  let ψr := TestFunction.postcompCLM Complex.reCLM ψ
  let ψi := TestFunction.postcompCLM Complex.imCLM ψ
  have hd (T : ℂ →L[ℝ] ℝ) (z d : ℂ) :
      fderiv ℝ (TestFunction.postcompCLM T ψ : ℂ → ℝ) z d =
        T (fderiv ℝ (ψ : ℂ → ℂ) z d) := by
    exact congrArg (fun L : ℂ →L[ℝ] ℝ => L d)
      (T.hasFDerivAt.comp z (ψ.contDiff.differentiable (by simp) z).hasFDerivAt).fderiv
  have hA := test_fderiv_integrable ψ (Complex.ofRealCLM.locallyIntegrableOn_comp hx) 1
  have hB := test_fderiv_integrable ψ (Complex.ofRealCLM.locallyIntegrableOn_comp hy) Complex.I
  have hC := ψ.integrable_bilin (ContinuousLinearMap.mul ℝ ℂ)
    (Complex.ofRealCLM.locallyIntegrableOn_comp hq)
  change Integrable (fun z => ψ z * (q z : ℂ)) at hC
  have hAB : Integrable (fun z => fderiv ℝ (ψ : ℂ → ℂ) z 1 * (ux z : ℂ) +
      fderiv ℝ (ψ : ℂ → ℂ) z Complex.I * (uy z : ℂ)) := hA.add hB
  have hR : Integrable (fun z => fderiv ℝ (ψ : ℂ → ℂ) z 1 * (ux z : ℂ) +
      fderiv ℝ (ψ : ℂ → ℂ) z Complex.I * (uy z : ℂ) - ψ z * (q z : ℂ)) := hAB.sub hC
  have hzero : (∫ z, fderiv ℝ (ψ : ℂ → ℂ) z 1 * (ux z : ℂ) +
      fderiv ℝ (ψ : ℂ → ℂ) z Complex.I * (uy z : ℂ) - ψ z * (q z : ℂ)) = 0 := by
    apply Complex.ext
    · have hre := Complex.reCLM.integral_comp_comm hR
      simp only [Complex.reCLM_apply] at hre
      rw [← hre]
      have hr := he ψr
      simp only [ψr] at hr
      simp_rw [hd] at hr
      simpa only [Function.comp_apply, TestFunction.postcompCLM_apply, Complex.reCLM_apply,
        Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero, Complex.zero_re] using hr
    · have him := Complex.imCLM.integral_comp_comm hR
      simp only [Complex.imCLM_apply] at him
      rw [← him]
      have hi := he ψi
      simp only [ψi] at hi
      simp_rw [hd] at hi
      simpa only [Function.comp_apply, TestFunction.postcompCLM_apply, Complex.imCLM_apply,
        Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_add, Complex.zero_im] using hi
  rw [integral_sub hAB hC, sub_eq_zero] at hzero
  exact hzero

lemma interiorWeakEquation_of_isWeakSolOn {Ω : Opens ℂ} {V : ℂ → ℝ}
    (u : TauCeti.W1p (volume : Measure ℂ) Ω 2)
    (hq : MemLp (fun z => V z * TauCeti.W1p.value u z) 2 (volume.restrict (Ω : Set ℂ)))
    (he : PunctureRemoval.IsWeakSolOn V Ω u) :
    InteriorWeakEquation Ω (fun z => ((TauCeti.W1p.gradient u z).re : ℂ))
      (fun z => ((TauCeti.W1p.gradient u z).im : ℂ))
      (fun z => (V z * TauCeti.W1p.value u z : ℝ)) := by
  apply interiorWeakEquation_of_real
    (locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp (TauCeti.W1p.gradient u)).re.locallyIntegrable (by norm_num)))
    (locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp (TauCeti.W1p.gradient u)).im.locallyIntegrable (by norm_num)))
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hq.locallyIntegrable (by norm_num)))
  intro ψ
  have h := he ψ ψ.contDiff ψ.hasCompactSupport ψ.tsupport_subset
  have hz : ∀ z ∉ (Ω : Set ℂ),
      (TauCeti.W1p.gradient u z).re * fderiv ℝ (ψ : ℂ → ℝ) z 1 +
        (TauCeti.W1p.gradient u z).im * fderiv ℝ (ψ : ℂ → ℝ) z Complex.I -
          V z * TauCeti.W1p.value u z * ψ z = 0 := by
    intro z hz
    have ht : z ∉ tsupport (ψ : ℂ → ℝ) := fun ht => hz (ψ.tsupport_subset ht)
    simp [image_eq_zero_of_notMem_tsupport ht, fderiv_of_notMem_tsupport ℝ ht]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := (volume : Measure ℂ)) (s := Ω.carrier) hz] at h
  convert h using 1
  congr 1
  ext z
  change fderiv ℝ (ψ : ℂ → ℝ) z 1 * (TauCeti.W1p.gradient u z).re +
    fderiv ℝ (ψ : ℂ → ℝ) z Complex.I * (TauCeti.W1p.gradient u z).im -
    ψ z * (V z * TauCeti.W1p.value u z) = _
  ring

/-- The precise real W¹,² predicate produced by puncture removal supplies the
bounded-representative engine, once its local potential product is in L². -/
theorem exists_boundedContinuous_cutoff_of_isWeakSolOn {Ω : Opens ℂ} {V : ℂ → ℝ}
    (u : TauCeti.W1p (volume : Measure ℂ) Ω 2)
    (hq : MemLp (fun z => V z * TauCeti.W1p.value u z) 2 (volume.restrict (Ω : Set ℂ)))
    (he : PunctureRemoval.IsWeakSolOn V Ω u)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (Ω : Set ℂ)) :
    ∃ g : ℂ →ᵇ ℂ, (fun z => χ z • (TauCeti.W1p.value u z : ℂ)) =ᵐ[volume] g := by
  have hx : TauCeti.HasWeakLineDerivOn volume Ω (TauCeti.W1p.value u)
      (fun z => (TauCeti.W1p.gradient u z).re) 1 := by
    simpa only [JacobiMode.innerSL_one] using (TauCeti.W1p.hasWeakFDerivOn u).hasWeakLineDerivOn 1
  have hy : TauCeti.HasWeakLineDerivOn volume Ω (TauCeti.W1p.value u)
      (fun z => (TauCeti.W1p.gradient u z).im) Complex.I := by
    simpa only [JacobiMode.innerSL_I] using (TauCeti.W1p.hasWeakFDerivOn u).hasWeakLineDerivOn Complex.I
  exact exists_boundedContinuous_cutoff (Lp.memLp (TauCeti.W1p.value u)).ofReal
    (Lp.memLp (TauCeti.W1p.gradient u)).re.ofReal
    (Lp.memLp (TauCeti.W1p.gradient u)).im.ofReal hq.ofReal
    (weakLineDeriv_ofReal hx) (weakLineDeriv_ofReal hy)
    (interiorWeakEquation_of_isWeakSolOn u hq he) hχ hc hs

end KsIndex.Weq
