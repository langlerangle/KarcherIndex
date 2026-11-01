module

public import KsIndexLean.ComplexFormBessel
public import Mathlib.Analysis.InnerProductSpace.l2Space

@[expose] public section


noncomputable section
namespace KsIndex.Spectral

variable {E H ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Rescale a variational solution by the inverse square root of `μ i`.
Energy orthonormality is proved below for orthonormal ambient eigenvectors
with positive eigenvalues. -/
def solutionEnergyVector (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (b : ι → H) (μ : ι → ℝ) (i : ι) : E :=
  ((Real.sqrt (μ i))⁻¹ : ℂ) • formSolution B hB J (b i)

lemma solutionEnergyVector_pairing (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (b : ι → H) (μ : ι → ℝ) (i : ι) (u : E) :
    B (solutionEnergyVector B hB J b μ i) u =
      ((Real.sqrt (μ i))⁻¹ : ℂ) * inner ℂ (b i) (J u) := by
  rw [solutionEnergyVector, map_smulₛₗ B]
  simp only [smul_apply, smul_eq_mul, map_inv₀, Complex.conj_ofReal, formSolution_weak]

lemma solutionEnergyVector_image (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (b : ι → H) (μ : ι → ℝ)
    (hev : ∀ i, compactFormSolution B hB J (b i) = (μ i : ℂ) • b i) (i : ι) :
    J (solutionEnergyVector B hB J b μ i) =
      ((Real.sqrt (μ i))⁻¹ : ℂ) • ((μ i : ℂ) • b i) := by
  rw [solutionEnergyVector, map_smul]
  change _ • compactFormSolution B hB J (b i) = _
  rw [hev]

lemma solutionEnergyVector_orthonormal [DecidableEq ι]
    (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (b : ι → H) (hb : Orthonormal ℂ b) (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (hev : ∀ i, compactFormSolution B hB J (b i) = (μ i : ℂ) • b i) (i j : ι) :
    B (solutionEnergyVector B hB J b μ i) (solutionEnergyVector B hB J b μ j) =
      if i = j then 1 else 0 := by
  rw [solutionEnergyVector_pairing, solutionEnergyVector_image B hB J b μ hev,
    inner_smul_right, inner_smul_right]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, inner_self_eq_norm_sq_to_K, hb.norm_eq_one]
    have hs : (Real.sqrt (μ i) : ℂ) ^ 2 = (μ i : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt (hμ i))]
    have hn : (Real.sqrt (μ i) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (hμ i)))
    rw [← hs]
    field_simp
    norm_num
  · rw [ite_eq_right hij, hb.inner_eq_zero hij]
    simp

lemma solutionEnergyVector_coefficient_sq (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (b : ι → H) (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i) (i : ι) (u : E) :
    ‖B (solutionEnergyVector B hB J b μ i) u‖ ^ 2 =
      (μ i)⁻¹ * ‖inner ℂ (b i) (J u)‖ ^ 2 := by
  rw [solutionEnergyVector_pairing, norm_mul, mul_pow, norm_inv, inv_pow]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (le_of_lt (hμ i))]

/-- Finite spectral energy inequality for the variational solution map. -/
lemma solution_spectral_bessel [DecidableEq ι] (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (hherm : ∀ u w, star (B w u) = B u w)
    (b : ι → H) (hb : Orthonormal ℂ b) (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (hev : ∀ i, compactFormSolution B hB J (b i) = (μ i : ℂ) • b i)
    (s : Finset ι) (u : E) :
    ∑ i ∈ s, (μ i)⁻¹ * ‖inner ℂ (b i) (J u)‖ ^ 2 ≤ (B u u).re := by
  have h := form_bessel B (fun u => (sq_nonneg ‖u‖).trans (hB u)) hherm
    (solutionEnergyVector B hB J b μ) s
    (fun i _ j _ => solutionEnergyVector_orthonormal B hB J b hb μ hμ hev i j) u
  simpa only [solutionEnergyVector_coefficient_sq B hB J b μ hμ] using h

end KsIndex.Spectral
