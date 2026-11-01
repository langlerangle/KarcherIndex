module

public import KsIndexLean.SpectralDimensionIntersection
public import KsIndexLean.WeakEigenvectorLift

@[expose] public section


noncomputable section
namespace KsIndex.Spectral

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The first `n+1` lifted eigenvectors attain the shifted spectral upper bound. -/
lemma exists_spectral_trial_space (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (b : HilbertBasis ℕ ℂ H) (μ : ℕ → ℝ) (hμ : ∀ i, 0 < μ i) (hanti : Antitone μ)
    (hev : ∀ i, compactFormSolution B hB J (b i) = (μ i : ℂ) • b i) (n : ℕ) :
    ∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧ Module.finrank ℂ W = n + 1 ∧
      ∀ u : W, (B u u).re ≤ (μ n)⁻¹ * ‖J u‖ ^ 2 := by
  let v : Fin (n + 1) → E := fun i => weakEigenvectorLift B hB J b μ i.val
  have hi : LinearIndependent ℂ v :=
    (weakEigenvectorLift_linearIndependent B hB J b b.orthonormal μ hμ hev).comp
      Fin.val Fin.val_injective
  let W := Submodule.span ℂ (Set.range v)
  have hW : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  have hd : Module.finrank ℂ W = n + 1 := by simpa [W] using finrank_span_eq_card hi
  refine ⟨W, hW, hd, ?_⟩
  intro u
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp u.property
  have horth : Orthonormal ℂ (fun i : Fin (n + 1) => b i.val) :=
    b.orthonormal.comp Fin.val Fin.val_injective
  have h := weakEigenvectorLift_energy_upper B hB J (fun i : Fin (n + 1) => b i.val)
    horth (fun i => μ i.val) (fun i => hμ i.val) (fun i => hev i.val)
    Finset.univ a ((μ n)⁻¹) (fun i _ =>
      (inv_le_inv₀ (hμ i.val) (hμ n)).mpr (hanti (by omega)))
  change (B (∑ i, a i • v i) (∑ i, a i • v i)).re ≤
    (μ n)⁻¹ * ‖J (∑ i, a i • v i)‖ ^ 2 at h
  rwa [ha] at h

/-- Attained min-max characterization in terms of uniform energy bounds on
complex trial spaces. This is equivalent to the infimum of their Rayleigh suprema. -/
lemma infinite_form_minmax_iff (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (hJ : Function.Injective J) (hherm : ∀ u w, star (B w u) = B u w)
    (b : HilbertBasis ℕ ℂ H) (μ : ℕ → ℝ) (hμ : ∀ i, 0 < μ i) (hanti : Antitone μ)
    (hev : ∀ i, compactFormSolution B hB J (b i) = (μ i : ℂ) • b i)
    (n : ℕ) (L : ℝ) :
    (μ n)⁻¹ ≤ L ↔ ∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = n + 1 ∧ ∀ u : W, (B u u).re ≤ L * ‖J u‖ ^ 2 := by
  constructor
  · intro hL
    obtain ⟨W, hW, hd, hu⟩ := exists_spectral_trial_space B hB J b μ hμ hanti hev n
    exact ⟨W, hW, hd, fun u => (hu u).trans (mul_le_mul_of_nonneg_right hL (sq_nonneg _))⟩
  · rintro ⟨W, hW, hd, hu⟩
    let := hW
    exact trial_bound_ge_reciprocal B hB J hJ hherm b μ hμ hanti hev W n (by omega) L hu

omit [CompleteSpace E] [CompleteSpace H] in
lemma shifted_form_bound_iff (B : E →L⋆[ℂ] E →L[ℂ] ℂ) (J : E →L[ℂ] H)
    (Q : E → E → ℂ) (c : ℝ)
    (hshift : ∀ u v, B u v = Q u v + (c : ℂ) * inner ℂ (J u) (J v))
    (u : E) (L : ℝ) :
    (B u u).re ≤ (L + c) * ‖J u‖ ^ 2 ↔ (Q u u).re ≤ L * ‖J u‖ ^ 2 := by
  have he : (B u u).re = (Q u u).re + c * ‖J u‖ ^ 2 := by
    rw [hshift, inner_self_eq_norm_sq_to_K]
    change (Q u u + (c : ℂ) * (‖J u‖ : ℂ) ^ 2).re = _
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.add_re, Complex.ofReal_re]
  rw [he]
  constructor <;> intro h <;> nlinarith

/-- Attained trial-space min-max characterization after removing the mass shift. -/
lemma infinite_unshifted_form_minmax_iff (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (hJ : Function.Injective J) (hherm : ∀ u w, star (B w u) = B u w)
    (b : HilbertBasis ℕ ℂ H) (μ : ℕ → ℝ) (hμ : ∀ i, 0 < μ i) (hanti : Antitone μ)
    (hev : ∀ i, compactFormSolution B hB J (b i) = (μ i : ℂ) • b i)
    (Q : E → E → ℂ) (c : ℝ)
    (hshift : ∀ u v, B u v = Q u v + (c : ℂ) * inner ℂ (J u) (J v))
    (n : ℕ) (L : ℝ) :
    (μ n)⁻¹ - c ≤ L ↔ ∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = n + 1 ∧ ∀ u : W, (Q u u).re ≤ L * ‖J u‖ ^ 2 := by
  rw [sub_le_iff_le_add, infinite_form_minmax_iff B hB J hJ hherm b μ hμ hanti hev]
  simp only [shifted_form_bound_iff B J Q c hshift]

end KsIndex.Spectral
