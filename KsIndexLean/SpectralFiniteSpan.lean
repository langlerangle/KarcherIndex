module

public import KsIndexLean.SolutionEnergyVectors

@[expose] public section


noncomputable section
namespace KsIndex.Spectral

variable {E H ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private lemma real_conj_mul (a : ℂ) (r : ℝ) :
    ((starRingEnd ℂ) a * ((r : ℂ) * a)).re = r * ‖a‖ ^ 2 := by
  rw [mul_left_comm, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-- Exact energy of a finite linear combination of mass-orthonormal weak eigenvectors. -/
lemma finite_eigenvector_energy (B : E →L⋆[ℂ] E →L[ℂ] ℂ) (J : E →L[ℂ] H)
    (v : ι → E) (hv : Orthonormal ℂ (fun i => J (v i))) (κ : ι → ℝ)
    (he : ∀ i u, B (v i) u = (κ i : ℂ) * inner ℂ (J (v i)) (J u))
    (s : Finset ι) (a : ι → ℂ) :
    (B (∑ i ∈ s, a i • v i) (∑ i ∈ s, a i • v i)).re = ∑ i ∈ s, κ i * ‖a i‖ ^ 2 := by
  simp only [map_sum B, sum_apply, map_smulₛₗ B, smul_apply, smul_eq_mul, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [he, show J (∑ j ∈ s, a j • v j) = ∑ j ∈ s, a j • J (v j) from by simp]
  rw [hv.inner_right_sum a hi]
  exact real_conj_mul _ _

lemma finite_eigenvector_mass (J : E →L[ℂ] H)
    (v : ι → E) (hv : Orthonormal ℂ (fun i => J (v i)))
    (s : Finset ι) (a : ι → ℂ) :
    ‖J (∑ i ∈ s, a i • v i)‖ ^ 2 = ∑ i ∈ s, ‖a i‖ ^ 2 := by
  rw [show J (∑ j ∈ s, a j • v j) = ∑ j ∈ s, a j • J (v j) from by simp]
  rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ]
  change (inner ℂ (∑ j ∈ s, a j • J (v j)) (∑ j ∈ s, a j • J (v j))).re = _
  simp only [sum_inner, inner_smul_left, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hv.inner_right_sum a hi]
  simpa using real_conj_mul (a i) 1

/-- Spectral upper bound on a finite eigenvector span. -/
lemma finite_eigenvector_energy_upper (B : E →L⋆[ℂ] E →L[ℂ] ℂ) (J : E →L[ℂ] H)
    (v : ι → E) (hv : Orthonormal ℂ (fun i => J (v i))) (κ : ι → ℝ)
    (he : ∀ i u, B (v i) u = (κ i : ℂ) * inner ℂ (J (v i)) (J u))
    (s : Finset ι) (a : ι → ℂ) (L : ℝ) (hL : ∀ i ∈ s, κ i ≤ L) :
    (B (∑ i ∈ s, a i • v i) (∑ i ∈ s, a i • v i)).re ≤
      L * ‖J (∑ i ∈ s, a i • v i)‖ ^ 2 := by
  rw [finite_eigenvector_energy B J v hv κ he, finite_eigenvector_mass J v hv, Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hL i hi) (sq_nonneg _)

end KsIndex.Spectral
