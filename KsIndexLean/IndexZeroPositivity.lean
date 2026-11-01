module

public import KsIndexLean.FormEqualityCase
public import KsIndexLean.NegativeDensity

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma form_nonnegative_of_index_zero (Q : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hi : KsIndex.NegativeDensity.negativeIndex (fun u => (Q u u).re) = 0) :
    ∀ u, 0 ≤ (Q u u).re := by
  intro u
  by_contra h
  have hu : (Q u u).re < 0 := lt_of_not_ge h
  have hu0 : u ≠ 0 := by intro he; simp [he] at hu
  have hn : ∀ v ∈ Submodule.span ℂ {u}, v ≠ 0 → (Q v v).re < 0 := by
    intro v hv hv0
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    have hc : c ≠ 0 := by intro he; simp [he] at hv0
    have he : (Q (c • u) (c • u)).re = ‖c‖ ^ 2 * (Q u u).re := by
      simp only [map_smulₛₗ, smul_apply, smul_eq_mul,
        RingHom.id_apply, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [he]
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos (norm_pos_iff.mpr hc)) hu
  have hd : Module.finrank ℂ (Submodule.span ℂ {u}) = 1 := finrank_span_singleton hu0
  have hb : ((Module.finrank ℂ (Submodule.span ℂ {u}) : ℕ) : ℕ∞) ≤
      KsIndex.NegativeDensity.negativeIndex (fun u => (Q u u).re) :=
    le_iSup_of_le _ (le_iSup_of_le hn (le_iSup_of_le inferInstance le_rfl))
  rw [hi, hd] at hb
  norm_num at hb

lemma form_positive_of_index_zero_kernel_zero (Q : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hQ : ∀ u v, star (Q v u) = Q u v)
    (hi : KsIndex.NegativeDensity.negativeIndex (fun u => (Q u u).re) = 0)
    (hk : ∀ u, (∀ v, Q u v = 0) → u = 0) :
    ∀ u, u ≠ 0 → 0 < (Q u u).re := by
  intro u hu
  have hn := form_nonnegative_of_index_zero Q hi
  apply lt_of_le_of_ne (hn u)
  intro hz
  apply hu
  apply hk u
  exact fun v => form_zero_energy_on_subspace Q hQ ⊤ (fun v _ => hn v)
    (Submodule.mem_top) hz.symm v (Submodule.mem_top)

end KsIndex.Spectral
