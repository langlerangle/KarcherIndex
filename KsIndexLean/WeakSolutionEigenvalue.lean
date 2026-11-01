module

public import KsIndexLean.CompactFormSolution

@[expose] public section


noncomputable section
namespace KsIndex.Spectral

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace E] in
/-- Coercivity gives uniqueness for the complex weak problem. -/
lemma coerciveForm_unique (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) {u w : E}
    (h : ∀ v, B u v = B w v) : u = w := by
  have hz : B (u - w) (u - w) = 0 := by
    rw [map_sub B u w, sub_apply, h, sub_self]
  have hn := hB (u - w)
  rw [hz] at hn
  have he : ‖u - w‖ = 0 := by simpa using (sq_eq_zero_iff.mp (le_antisymm hn (sq_nonneg _)))
  exact sub_eq_zero.mp (norm_eq_zero.mp he)

lemma formSolution_eq_iff (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H) (f : H) (u : E) :
    formSolution B hB J f = u ↔ ∀ v, B u v = inner ℂ f (J v) := by
  constructor
  · intro h v
    rw [← h]
    exact formSolution_weak B hB J f v
  · intro h
    apply coerciveForm_unique B hB
    intro v
    rw [formSolution_weak, h]

/-- Exact correspondence in the form domain; no regularity of eigenfunctions
is assumed. Nonzero vectors and nonzero eigenvalues are handled separately. -/
lemma compactFormSolution_eigen_equation_iff (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (hJ : Function.Injective J) (u : E) (t : ℂ) :
    compactFormSolution B hB J (J u) = t • J u ↔
      ∀ v, B (t • u) v = inner ℂ (J u) (J v) := by
  change J (formSolution B hB J (J u)) = t • J u ↔ _
  rw [← map_smul, hJ.eq_iff]
  exact formSolution_eq_iff B hB J (J u) (t • u)

/-- Every nonzero solution-operator eigenvalue has its eigenvectors in the
embedded form domain. This is the regularity needed for the weak equation. -/
lemma compactFormSolution_eigen_mem_range (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    {f : H} {t : ℂ} (ht : t ≠ 0)
    (hf : compactFormSolution B hB J f = t • f) : f ∈ J.toLinearMap.range := by
  refine ⟨t⁻¹ • formSolution B hB J f, ?_⟩
  change J (t⁻¹ • formSolution B hB J f) = f
  rw [map_smul]
  change t⁻¹ • compactFormSolution B hB J f = f
  rw [hf, smul_smul, inv_mul_cancel₀ ht, one_smul]

/-- For a real nonzero solution eigenvalue, the weak eigenvalue is its reciprocal. -/
lemma compactFormSolution_real_eigen_iff (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (hJ : Function.Injective J) (u : E) (t : ℝ) (ht : t ≠ 0) :
    compactFormSolution B hB J (J u) = (t : ℂ) • J u ↔
      ∀ v, B u v = (t⁻¹ : ℝ) * inner ℂ (J u) (J v) := by
  rw [compactFormSolution_eigen_equation_iff B hB J hJ]
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have hs (v : E) : B ((t : ℂ) • u) v = (t : ℂ) * B u v := by
    rw [map_smulₛₗ B]
    simp
  simp only [hs, Complex.ofReal_inv]
  constructor
  · intro h v
    rw [← h v, ← mul_assoc, inv_mul_cancel₀ htC, one_mul]
  · intro h v
    rw [h v, ← mul_assoc, mul_inv_cancel₀ htC, one_mul]

/-- Removing a real mass shift gives the weak Jacobi eigenvalue `t⁻¹ - c`.
The form equality is an explicit hypothesis to be discharged by the actual
geometric form, rather than an identification hidden in a definition. -/
lemma compactFormSolution_shifted_eigen_iff (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (hJ : Function.Injective J) (Q : E → E → ℂ) (c : ℝ)
    (hshift : ∀ u v, B u v = Q u v + (c : ℂ) * inner ℂ (J u) (J v))
    (u : E) (t : ℝ) (ht : t ≠ 0) :
    compactFormSolution B hB J (J u) = (t : ℂ) • J u ↔
      ∀ v, Q u v = ((t⁻¹ - c : ℝ) : ℂ) * inner ℂ (J u) (J v) := by
  rw [compactFormSolution_real_eigen_iff B hB J hJ u t ht]
  simp only [hshift, Complex.ofReal_sub, sub_mul]
  exact forall_congr' (fun v => eq_sub_iff_add_eq.symm)

end KsIndex.Spectral
