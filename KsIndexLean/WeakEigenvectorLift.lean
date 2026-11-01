module

public import KsIndexLean.SpectralFiniteSpan

@[expose] public section


noncomputable section
namespace KsIndex.Spectral

variable {E H ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Lift of an ambient eigenvector, normalized to preserve its bulk value. -/
def weakEigenvectorLift (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (b : ι → H) (μ : ι → ℝ) (i : ι) : E :=
  ((μ i)⁻¹ : ℂ) • formSolution B hB J (b i)

lemma weakEigenvectorLift_image (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (b : ι → H) (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (hev : ∀ i, compactFormSolution B hB J (b i) = (μ i : ℂ) • b i) (i : ι) :
    J (weakEigenvectorLift B hB J b μ i) = b i := by
  rw [weakEigenvectorLift, map_smul]
  change _ • compactFormSolution B hB J (b i) = _
  rw [hev, smul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (hμ i))), one_smul]

lemma weakEigenvectorLift_pairing (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (b : ι → H) (μ : ι → ℝ) (i : ι) (u : E) :
    B (weakEigenvectorLift B hB J b μ i) u = ((μ i)⁻¹ : ℂ) * inner ℂ (b i) (J u) := by
  rw [weakEigenvectorLift, map_smulₛₗ B]
  simp only [smul_apply, smul_eq_mul, map_inv₀, Complex.conj_ofReal, formSolution_weak]

/-- The finite-span upper estimate for the actual variational eigenvector lifts. -/
lemma weakEigenvectorLift_energy_upper (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (b : ι → H) (hb : Orthonormal ℂ b) (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (hev : ∀ i, compactFormSolution B hB J (b i) = (μ i : ℂ) • b i)
    (s : Finset ι) (a : ι → ℂ) (L : ℝ) (hL : ∀ i ∈ s, (μ i)⁻¹ ≤ L) :
    (B (∑ i ∈ s, a i • weakEigenvectorLift B hB J b μ i)
      (∑ i ∈ s, a i • weakEigenvectorLift B hB J b μ i)).re ≤
      L * ‖J (∑ i ∈ s, a i • weakEigenvectorLift B hB J b μ i)‖ ^ 2 := by
  have hv : Orthonormal ℂ (fun i => J (weakEigenvectorLift B hB J b μ i)) := by
    simpa only [weakEigenvectorLift_image B hB J b μ hμ hev] using hb
  apply finite_eigenvector_energy_upper B J _ hv (fun i => (μ i)⁻¹) _ s a L hL
  intro i u
  rw [weakEigenvectorLift_pairing, weakEigenvectorLift_image B hB J b μ hμ hev]
  simp only [Complex.ofReal_inv]

lemma weakEigenvectorLift_linearIndependent (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (b : ι → H) (hb : Orthonormal ℂ b) (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (hev : ∀ i, compactFormSolution B hB J (b i) = (μ i : ℂ) • b i) :
    LinearIndependent ℂ (weakEigenvectorLift B hB J b μ) := by
  apply LinearIndependent.of_comp J.toLinearMap
  simpa only [Function.comp_def, ContinuousLinearMap.coe_coe,
    weakEigenvectorLift_image B hB J b μ hμ hev] using hb.linearIndependent

/-- Complex dimension of a finite family of lifted spectral vectors. -/
lemma weakEigenvectorLift_span_finrank (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (b : ι → H) (hb : Orthonormal ℂ b) (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (hev : ∀ i, compactFormSolution B hB J (b i) = (μ i : ℂ) • b i) (s : Finset ι) :
    Module.finrank ℂ (Submodule.span ℂ
      (Set.range (fun i : s => weakEigenvectorLift B hB J b μ i.val))) = s.card := by
  have hi := (weakEigenvectorLift_linearIndependent B hB J b hb μ hμ hev).comp
    (fun i : s => i.val) Subtype.val_injective
  simpa only [Function.comp_def, Fintype.card_coe] using finrank_span_eq_card hi

end KsIndex.Spectral
