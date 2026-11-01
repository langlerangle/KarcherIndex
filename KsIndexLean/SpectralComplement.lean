module

public import KsIndexLean.WeakEigenvectorLift

@[expose] public section


noncomputable section
namespace KsIndex.Spectral

variable {E H ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Orthogonality imposed on bulk values, with vectors retained in the actual
form domain. -/
def bulkSpectralComplement (J : E →L[ℂ] H) (b : ι → H) (s : Finset ι) : Submodule ℂ E where
  carrier := {u | ∀ i ∈ s, inner ℂ (b i) (J u) = 0}
  zero_mem' := by simp
  add_mem' := by intro u v hu hv i hi; simp [hu i hi, hv i hi]
  smul_mem' := by intro c u hu i hi; simp [hu i hi]

/-- The finite low-mode projection uses lifts into the form domain, so its
remainder remains an admissible weak function. -/
def bulkSpectralProjection (J : E →L[ℂ] H) (b : ι → H) (v : ι → E)
    (s : Finset ι) (u : E) : E := ∑ i ∈ s, inner ℂ (b i) (J u) • v i

lemma bulkSpectralProjection_coefficient (J : E →L[ℂ] H) (b : ι → H) (v : ι → E)
    (hb : Orthonormal ℂ b) (hv : ∀ i, J (v i) = b i) (s : Finset ι) (u : E)
    {i : ι} (hi : i ∈ s) :
    inner ℂ (b i) (J (bulkSpectralProjection J b v s u)) = inner ℂ (b i) (J u) := by
  classical
  simp only [bulkSpectralProjection, map_sum, map_smul, hv, inner_sum, inner_smul_right,
    orthonormal_iff_ite.mp hb]
  simp [hi]

lemma bulkSpectralProjection_remainder (J : E →L[ℂ] H) (b : ι → H) (v : ι → E)
    (hb : Orthonormal ℂ b) (hv : ∀ i, J (v i) = b i) (s : Finset ι) (u : E) :
    u - bulkSpectralProjection J b v s u ∈ bulkSpectralComplement J b s := by
  intro i hi
  rw [map_sub, inner_sub_right, bulkSpectralProjection_coefficient J b v hb hv s u hi, sub_self]

/-- Every form-domain vector is a finite spectral part plus an admissible
orthogonal remainder. This is algebraic and does not assume ambient completeness. -/
lemma bulkSpectralComplement_span_sup (J : E →L[ℂ] H) (b : ι → H) (v : ι → E)
    (hb : Orthonormal ℂ b) (hv : ∀ i, J (v i) = b i) (s : Finset ι) :
    Submodule.span ℂ (v '' (s : Set ι)) ⊔ bulkSpectralComplement J b s = ⊤ := by
  apply top_unique
  intro u _
  let p := bulkSpectralProjection J b v s u
  have hp : p ∈ Submodule.span ℂ (v '' (s : Set ι)) := by
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  exact Submodule.mem_sup.mpr ⟨p, hp, u - p,
    bulkSpectralProjection_remainder J b v hb hv s u, by abel⟩

end KsIndex.Spectral
