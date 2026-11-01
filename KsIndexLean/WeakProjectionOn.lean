module

public import KsIndexLean.WeakH1Adapter

@[expose] public section


/-! Real projections of complex weak functions on arbitrary planar open domains. -/
noncomputable section
open Set MeasureTheory TopologicalSpace TauCeti
namespace KsIndex.WeakH1

lemma weakLine_project_on {Ω : Opens ℂ} (L : ℂ →L[ℝ] ℝ) {f g : ℂ → ℂ} {v : ℂ}
    (h : HasWeakLineDerivOn volume Ω f g v) :
    HasWeakLineDerivOn volume Ω (fun x => L (f x)) (fun x => L (g x)) v := by
  rw [hasWeakLineDerivOn_iff_testFunction]
  refine ⟨inferInstance, L.locallyIntegrableOn_comp h.locallyIntegrableOn,
    L.locallyIntegrableOn_comp h.locallyIntegrableOn_deriv, ?_⟩
  intro φ
  have hl := integrable_lineDeriv_smul_of_locallyIntegrableOn h.locallyIntegrableOn φ v
  have hr := integrable_smul_of_locallyIntegrableOn h.locallyIntegrableOn_deriv φ
  calc
    _ = L (∫ x, lineDeriv ℝ (φ : ℂ → ℝ) x v • f x) := by
      simpa only [map_smul] using L.integral_comp_comm hl
    _ = -L (∫ x, (φ : ℂ → ℝ) x • g x) := by
      rw [h.integral_lineDeriv_smul_eq_neg_integral_smul φ, map_neg]
    _ = _ := by rw [← L.integral_comp_comm hr]; simp only [map_smul]

lemma weakF_project_on {Ω : Opens ℂ} (L : ℂ →L[ℝ] ℝ) {f : ℂ → ℂ}
    {J : ℂ → ℂ →L[ℝ] ℂ} (h : HasWeakFDerivOn volume Ω f J) :
    HasWeakFDerivOn volume Ω (fun x => L (f x)) (fun x => L.comp (J x)) := by
  rw [hasWeakFDerivOn_iff]
  intro d
  exact weakLine_project_on L (h.hasWeakLineDerivOn d)

/-- Riesz gradient of a real projection of a complex planar derivative. -/
def projectedGradientRaw (L : ℂ →L[ℝ] ℝ) (J : ℂ → ℂ →L[ℝ] ℂ) (z : ℂ) : ℂ :=
  (L (J z 1) : ℂ) + Complex.I * (L (J z Complex.I) : ℂ)

lemma projectedGradientRaw_represents (L : ℂ →L[ℝ] ℝ) (J : ℂ → ℂ →L[ℝ] ℂ) (z : ℂ) :
    innerSL ℝ (projectedGradientRaw L J z) = L.comp (J z) := by
  ext d
  change inner ℝ (projectedGradientRaw L J z) d = L (J z d)
  rw [realLinear_coordinates (J z) d, map_add, map_smul, map_smul, real_inner_coordinates]
  simp [projectedGradientRaw, smul_eq_mul, mul_comm]

lemma projectedGradientRaw_memLp {Ω : Opens ℂ} (L : ℂ →L[ℝ] ℝ)
    {J : ℂ → ℂ →L[ℝ] ℂ}
    (hJ : ∀ d, MemLp (fun z => J z d) 2 (volume.restrict (Ω : Set ℂ))) :
    MemLp (projectedGradientRaw L J) 2 (volume.restrict (Ω : Set ℂ)) := by
  have hx := (hJ 1).continuousLinearMap_comp (Complex.ofRealCLM.comp L)
  have hy := ((hJ Complex.I).continuousLinearMap_comp (Complex.ofRealCLM.comp L)).const_smul Complex.I
  exact hx.add hy

/-- Real Sobolev realization, using the actual weak jet rather than smoothness assumptions. -/
def projectedH1On {Ω : Opens ℂ} (L : ℂ →L[ℝ] ℝ) {f : ℂ → ℂ} {J : ℂ → ℂ →L[ℝ] ℂ}
    (hw : HasWeakFDerivOn volume Ω f J)
    (hf : MemLp f 2 (volume.restrict (Ω : Set ℂ)))
    (hJ : ∀ d, MemLp (fun z => J z d) 2 (volume.restrict (Ω : Set ℂ))) :
    W1p (volume : Measure ℂ) Ω 2 := by
  let hv := hf.continuousLinearMap_comp L
  let hg := projectedGradientRaw_memLp L hJ
  apply W1p.mk (hv.toLp _) (hg.toLp _)
  apply ((weakF_project_on L hw).congr_ae hv.coeFn_toLp.symm).congr_ae_deriv
  filter_upwards [hg.coeFn_toLp] with z hz
  rw [hz, projectedGradientRaw_represents]

lemma projectedH1On_value_ae {Ω : Opens ℂ} (L : ℂ →L[ℝ] ℝ)
    {f : ℂ → ℂ} {J : ℂ → ℂ →L[ℝ] ℂ}
    (hw : HasWeakFDerivOn volume Ω f J)
    (hf : MemLp f 2 (volume.restrict (Ω : Set ℂ)))
    (hJ : ∀ d, MemLp (fun z => J z d) 2 (volume.restrict (Ω : Set ℂ))) :
    W1p.value (projectedH1On L hw hf hJ) =ᵐ[volume.restrict (Ω : Set ℂ)]
      fun z => L (f z) := by
  simpa only [projectedH1On, W1p.value_mk] using (hf.continuousLinearMap_comp L).coeFn_toLp

lemma projectedH1On_gradient_ae {Ω : Opens ℂ} (L : ℂ →L[ℝ] ℝ)
    {f : ℂ → ℂ} {J : ℂ → ℂ →L[ℝ] ℂ}
    (hw : HasWeakFDerivOn volume Ω f J)
    (hf : MemLp f 2 (volume.restrict (Ω : Set ℂ)))
    (hJ : ∀ d, MemLp (fun z => J z d) 2 (volume.restrict (Ω : Set ℂ))) :
    W1p.gradient (projectedH1On L hw hf hJ) =ᵐ[volume.restrict (Ω : Set ℂ)]
      projectedGradientRaw L J := by
  simpa only [projectedH1On, W1p.gradient_mk] using (projectedGradientRaw_memLp L hJ).coeFn_toLp

end KsIndex.WeakH1
