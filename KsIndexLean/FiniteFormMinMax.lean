module

public import KsIndexLean.InfiniteFormMinMax

@[expose] public section


noncomputable section
namespace KsIndex.Spectral

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {m : ℕ}

/-- Finite sectors attain the upper bound with exactly `n.val+1` trial dimensions. -/
lemma exists_finite_spectral_trial_space (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (b : HilbertBasis (Fin m) ℂ H) (μ : Fin m → ℝ) (hμ : ∀ i, 0 < μ i) (hanti : Antitone μ)
    (hev : ∀ i, compactFormSolution B hB J (b i) = (μ i : ℂ) • b i) (n : Fin m) :
    ∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧ Module.finrank ℂ W = n.val + 1 ∧
      ∀ u : W, (B u u).re ≤ (μ n)⁻¹ * ‖J u‖ ^ 2 := by
  let f : Fin (n.val + 1) → Fin m := fun i => ⟨i.val, by omega⟩
  have hf : Function.Injective f := by
    intro i j he
    exact Fin.ext (congrArg (fun z : Fin m => z.val) he)
  let v : Fin (n.val + 1) → E := fun i => weakEigenvectorLift B hB J b μ (f i)
  have hi : LinearIndependent ℂ v :=
    (weakEigenvectorLift_linearIndependent B hB J b b.orthonormal μ hμ hev).comp f hf
  let W := Submodule.span ℂ (Set.range v)
  have hW : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  have hd : Module.finrank ℂ W = n.val + 1 := by simpa [W] using finrank_span_eq_card hi
  refine ⟨W, hW, hd, ?_⟩
  intro u
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp u.property
  have h := weakEigenvectorLift_energy_upper B hB J (fun i => b (f i))
    (b.orthonormal.comp f hf) (fun i => μ (f i)) (fun i => hμ (f i)) (fun i => hev (f i))
    Finset.univ a ((μ n)⁻¹) (fun i _ =>
      (inv_le_inv₀ (hμ (f i)) (hμ n)).mpr (hanti (by change i.val ≤ n.val; omega)))
  change (B (∑ i, a i • v i) (∑ i, a i • v i)).re ≤
    (μ n)⁻¹ * ‖J (∑ i, a i • v i)‖ ^ 2 at h
  rwa [ha] at h

lemma finite_trial_bound_ge_reciprocal (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (hJ : Function.Injective J) (hherm : ∀ u w, star (B w u) = B u w)
    (b : HilbertBasis (Fin m) ℂ H) (μ : Fin m → ℝ) (hμ : ∀ i, 0 < μ i) (hanti : Antitone μ)
    (hev : ∀ i, compactFormSolution B hB J (b i) = (μ i : ℂ) • b i)
    (W : Submodule ℂ E) [FiniteDimensional ℂ W] (n : Fin m) (hdim : n.val < Module.finrank ℂ W)
    (L : ℝ) (hL : ∀ u : W, (B u u).re ≤ L * ‖J u‖ ^ 2) : (μ n)⁻¹ ≤ L := by
  let f : Fin n.val → Fin m := fun i => ⟨i.val, by omega⟩
  obtain ⟨u, hu, horth⟩ := exists_nonzero_orthogonal_in_trial J (fun i => b (f i)) W
    (by simpa using hdim)
  have hu' : ∀ i < n, inner ℂ (b i) (J u) = 0 := by
    intro i hi
    exact horth ⟨i.val, hi⟩
  have hlo := spectral_tail_energy_lower_bound B hB J hherm b μ hμ hanti hev n u hu'
  have hbulk : J u ≠ 0 := by
    intro he
    have hz : (u : E) = 0 := hJ (he.trans J.map_zero.symm)
    exact hu (Subtype.ext hz)
  have hp : 0 < ‖J u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hbulk)
  nlinarith [hL u]

/-- Finite attained min-max. `Fin m` prevents padding beyond the sector dimension. -/
lemma finite_form_minmax_iff (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (hJ : Function.Injective J) (hherm : ∀ u w, star (B w u) = B u w)
    (b : HilbertBasis (Fin m) ℂ H) (μ : Fin m → ℝ) (hμ : ∀ i, 0 < μ i) (hanti : Antitone μ)
    (hev : ∀ i, compactFormSolution B hB J (b i) = (μ i : ℂ) • b i)
    (n : Fin m) (L : ℝ) :
    (μ n)⁻¹ ≤ L ↔ ∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = n.val + 1 ∧ ∀ u : W, (B u u).re ≤ L * ‖J u‖ ^ 2 := by
  constructor
  · intro hL
    obtain ⟨W, hW, hd, hu⟩ := exists_finite_spectral_trial_space B hB J b μ hμ hanti hev n
    exact ⟨W, hW, hd, fun u => (hu u).trans (mul_le_mul_of_nonneg_right hL (sq_nonneg _))⟩
  · rintro ⟨W, hW, hd, hu⟩
    let := hW
    exact finite_trial_bound_ge_reciprocal B hB J hJ hherm b μ hμ hanti hev W n (by omega) L hu

lemma finite_unshifted_form_minmax_iff (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (hJ : Function.Injective J) (hherm : ∀ u w, star (B w u) = B u w)
    (b : HilbertBasis (Fin m) ℂ H) (μ : Fin m → ℝ) (hμ : ∀ i, 0 < μ i) (hanti : Antitone μ)
    (hev : ∀ i, compactFormSolution B hB J (b i) = (μ i : ℂ) • b i)
    (Q : E → E → ℂ) (c : ℝ)
    (hshift : ∀ u v, B u v = Q u v + (c : ℂ) * inner ℂ (J u) (J v))
    (n : Fin m) (L : ℝ) :
    (μ n)⁻¹ - c ≤ L ↔ ∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = n.val + 1 ∧ ∀ u : W, (Q u u).re ≤ L * ‖J u‖ ^ 2 := by
  rw [sub_le_iff_le_add, finite_form_minmax_iff B hB J hJ hherm b μ hμ hanti hev]
  simp only [shifted_form_bound_iff B J Q c hshift]

end KsIndex.Spectral
