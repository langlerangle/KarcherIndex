module

public import KsIndexLean.SpectralComplement
public import KsIndexLean.FormEqualityCase

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
variable {E H ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Saturation on the complement of finitely many weak spectral modes gives
the weak equation against every form-domain test vector. The finite set need
not consist of simple eigenvalues, and multiplicities are not discarded. -/
lemma spectral_complement_equality (Q M : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hQ : ∀ u v, star (Q v u) = Q u v)
    (hM : ∀ u v, star (M v u) = M u v)
    (J : E →L[ℂ] H) (hmass : ∀ u v, M u v = inner ℂ (J u) (J v))
    (b : ι → H) (v : ι → E) (hb : Orthonormal ℂ b) (hv : ∀ i, J (v i) = b i)
    (ν : ι → ℂ) (hev : ∀ i w, Q (v i) w = ν i * M (v i) w)
    (s : Finset ι) (L : ℝ)
    (hlower : ∀ x ∈ bulkSpectralComplement J b s, L * (M x x).re ≤ (Q x x).re)
    {u : E} (hu : u ∈ bulkSpectralComplement J b s)
    (heq : (Q u u).re = L * (M u u).re) :
    ∀ w, Q u w = (L : ℂ) * M u w := by
  apply form_lower_bound_equality_of_sup Q M hQ hM
    (Submodule.span ℂ (v '' (s : Set ι))) (bulkSpectralComplement J b s)
    (bulkSpectralComplement_span_sup J b v hb hv s) L hlower hu heq
  let K : E →L[ℂ] ℂ := Q u - (L : ℂ) • M u
  have hk : Submodule.span ℂ (v '' (s : Set ι)) ≤ K.toLinearMap.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    have hm : M u (v i) = 0 := by
      rw [hmass, hv, ← inner_conj_symm]
      rw [hu i hi]
      simp
    have hq := form_pairing_zero_of_weak_eigenvector Q M hQ hM (v i) u (ν i) (hev i) hm
    change Q u (v i) - (L : ℂ) * M u (v i) = 0
    rw [hq, hm, mul_zero, sub_zero]
  intro w hw
  have h := hk hw
  change Q u w - (L : ℂ) * M u w = 0 at h
  exact sub_eq_zero.mp h

end KsIndex.Spectral
