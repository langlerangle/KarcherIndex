module

public import KsIndexLean.CompactFormSolution

@[expose] public section


noncomputable section
namespace KsIndex.Spectral

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Finite coefficient sum associated with a sesquilinear form and a family.
For an energy-orthonormal family, the coefficient lemma below gives the projection identity. -/
def formProjection (B : E →L⋆[ℂ] E →L[ℂ] ℂ) (v : ι → E) (s : Finset ι) (u : E) : E :=
  ∑ i ∈ s, (B (v i) u) • v i

lemma formProjection_pairing (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (v : ι → E) (s : Finset ι) (u w : E) :
    B (formProjection B v s u) w = ∑ i ∈ s, star (B (v i) u) * B (v i) w := by
  simp only [formProjection, map_sum, sum_apply, map_smulₛₗ, smul_apply, smul_eq_mul,
    Complex.star_def]

lemma formProjection_pairing_self (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (v : ι → E) (s : Finset ι) (u : E) :
    (B (formProjection B v s u) u).re = ∑ i ∈ s, ‖B (v i) u‖ ^ 2 := by
  rw [formProjection_pairing, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.star_def, Complex.conj_mul']
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

lemma formProjection_coefficient [DecidableEq ι] (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (v : ι → E) (s : Finset ι)
    (hv : ∀ i ∈ s, ∀ j ∈ s, B (v i) (v j) = if i = j then 1 else 0)
    (u : E) {i : ι} (hi : i ∈ s) :
    B (v i) (formProjection B v s u) = B (v i) u := by
  simp only [formProjection, map_sum, map_smul, smul_eq_mul]
  calc
    _ = ∑ j ∈ s, (B (v j) u) * (if i = j then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hv i hi j hj]
    _ = _ := by simp [hi]

/-- Bessel's inequality for a nonnegative complex Hermitian form.
This is finite-sum energy control, without any completeness assumption. -/
lemma form_bessel [DecidableEq ι] (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hpos : ∀ u, 0 ≤ (B u u).re) (hherm : ∀ u w, star (B w u) = B u w)
    (v : ι → E) (s : Finset ι)
    (hv : ∀ i ∈ s, ∀ j ∈ s, B (v i) (v j) = if i = j then 1 else 0)
    (u : E) : ∑ i ∈ s, ‖B (v i) u‖ ^ 2 ≤ (B u u).re := by
  let p := formProjection B v s u
  have hpu : (B p u).re = ∑ i ∈ s, ‖B (v i) u‖ ^ 2 := formProjection_pairing_self B v s u
  have hpp : B p p = B p u := by
    rw [show p = formProjection B v s u from rfl, formProjection_pairing,
      formProjection_pairing]
    apply Finset.sum_congr rfl
    intro i hi
    rw [formProjection_coefficient B v s hv u hi]
  have hup : (B u p).re = (B p u).re := by
    rw [← hherm u p]
    simp
  have h := hpos (u - p)
  have he : B (u - p) (u - p) = B u u - B u p - (B p u - B p p) := by
    rw [map_sub B u p, sub_apply, map_sub, map_sub]
  rw [he, Complex.sub_re, Complex.sub_re, Complex.sub_re, hpp, hup, hpu] at h
  linarith

end KsIndex.Spectral
