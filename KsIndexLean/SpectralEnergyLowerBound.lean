module

public import KsIndexLean.SolutionEnergyVectors

@[expose] public section


noncomputable section
namespace KsIndex.Spectral

variable {E H ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma hilbertBasis_hasSum_sq_coeff (b : HilbertBasis ι ℂ H) (x : H) :
    HasSum (fun i => ‖inner ℂ (b i) x‖ ^ 2) (‖x‖ ^ 2) := by
  have h := Complex.hasSum_re (b.hasSum_inner_mul_inner x x)
  have he (i : ι) : (inner ℂ x (b i) * inner ℂ (b i) x).re = ‖inner ℂ (b i) x‖ ^ 2 := by
    rw [← inner_conj_symm x (b i), Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  simp only [he, inner_self_eq_norm_sq_to_K] at h
  change HasSum (fun i => ‖inner ℂ (b i) x‖ ^ 2) (((‖x‖ : ℂ) ^ 2).re) at h
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using h

/-- A lower energy estimate obtained by excluding all spectral coefficients
whose reciprocal eigenvalue is below the proposed bound. -/
lemma spectral_energy_lower_bound (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (hherm : ∀ u w, star (B w u) = B u w)
    (b : HilbertBasis ι ℂ H) (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (hev : ∀ i, compactFormSolution B hB J (b i) = (μ i : ℂ) • b i)
    (u : E) (κ : ℝ) (hκ : 0 ≤ κ)
    (hcoeff : ∀ i, κ ≤ (μ i)⁻¹ ∨ inner ℂ (b i) (J u) = 0) :
    κ * ‖J u‖ ^ 2 ≤ (B u u).re := by
  classical
  have hsum := (hilbertBasis_hasSum_sq_coeff b (J u)).mul_left κ
  rw [← hsum.tsum_eq]
  apply Real.tsum_le_of_sum_le
  · intro i
    exact mul_nonneg hκ (sq_nonneg _)
  · intro s
    apply le_trans _ (solution_spectral_bessel B hB J hherm b b.orthonormal μ hμ hev s u)
    apply Finset.sum_le_sum
    intro i hi
    rcases hcoeff i with hi | hi
    · exact mul_le_mul_of_nonneg_right hi (sq_nonneg _)
    · simp [hi]

/-- The lower min-max estimate outside earlier complex eigenvectors, for both
finite and infinite ordered basis indices. -/
lemma spectral_tail_energy_lower_bound [LinearOrder ι] (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (hherm : ∀ u w, star (B w u) = B u w)
    (b : HilbertBasis ι ℂ H) (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i) (hanti : Antitone μ)
    (hev : ∀ i, compactFormSolution B hB J (b i) = (μ i : ℂ) • b i)
    (n : ι) (u : E) (hu : ∀ i < n, inner ℂ (b i) (J u) = 0) :
    (μ n)⁻¹ * ‖J u‖ ^ 2 ≤ (B u u).re := by
  apply spectral_energy_lower_bound B hB J hherm b μ hμ hev u _ (le_of_lt (inv_pos.mpr (hμ n)))
  intro i
  by_cases hi : i < n
  · exact Or.inr (hu i hi)
  · exact Or.inl ((inv_le_inv₀ (hμ n) (hμ i)).mpr (hanti (le_of_not_gt hi)))

/-- Removing the mass shift yields the lower bound for the unshifted form. -/
lemma spectral_tail_shifted_lower_bound [LinearOrder ι] (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (hherm : ∀ u w, star (B w u) = B u w)
    (b : HilbertBasis ι ℂ H) (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i) (hanti : Antitone μ)
    (hev : ∀ i, compactFormSolution B hB J (b i) = (μ i : ℂ) • b i)
    (Q : E → E → ℂ) (c : ℝ)
    (hshift : ∀ u v, B u v = Q u v + (c : ℂ) * inner ℂ (J u) (J v))
    (n : ι) (u : E) (hu : ∀ i < n, inner ℂ (b i) (J u) = 0) :
    ((μ n)⁻¹ - c) * ‖J u‖ ^ 2 ≤ (Q u u).re := by
  have h := spectral_tail_energy_lower_bound B hB J hherm b μ hμ hanti hev n u hu
  have he : (B u u).re = (Q u u).re + c * ‖J u‖ ^ 2 := by
    rw [hshift, inner_self_eq_norm_sq_to_K]
    change (Q u u + (c : ℂ) * (‖J u‖ : ℂ) ^ 2).re = _
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.add_re, Complex.ofReal_re]
  rw [he] at h
  nlinarith

end KsIndex.Spectral
