module

public import KsIndexLean.SpectralComplementEquality
public import KsIndexLean.SpectralEnergyLowerBound
public import KsIndexLean.DiskJacobiSesquilinear

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
variable {E H ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [LinearOrder ι]

/-- Equality in the ordered spectral tail bound gives the full unshifted weak
Jacobi equation. A finite initial segment is explicit, allowing both finite
spectra and natural-number spectra without assuming infinite dimension. -/
lemma ordered_spectral_tail_equality
    (B Q : E →L⋆[ℂ] E →L[ℂ] ℂ) (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re)
    (J : E →L[ℂ] H) (hherm : ∀ u v, star (B v u) = B u v)
    (hQ : ∀ u v, star (Q v u) = Q u v)
    (b : HilbertBasis ι ℂ H) (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i) (hanti : Antitone μ)
    (hev : ∀ i, compactFormSolution B hB J (b i) = (μ i : ℂ) • b i)
    (c : ℝ) (hshift : ∀ u v, B u v = Q u v + (c : ℂ) * inner ℂ (J u) (J v))
    (n : ι) (s : Finset ι) (hs : ∀ i, i ∈ s ↔ i < n)
    (u : E) (hu : ∀ i < n, inner ℂ (b i) (J u) = 0)
    (heq : (Q u u).re = ((μ n)⁻¹ - c) * ‖J u‖ ^ 2) :
    ∀ w, Q u w = (((μ n)⁻¹ - c : ℝ) : ℂ) * inner ℂ (J u) (J w) := by
  let M := mapPairing J J
  have hm (x y : E) : M x y = inner ℂ (J x) (J y) := rfl
  have hmself (x : E) : (M x x).re = ‖J x‖ ^ 2 := by
    rw [hm, inner_self_eq_norm_sq_to_K]
    change ((‖J x‖ : ℂ) ^ 2).re = _
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  let v := weakEigenvectorLift B hB J b μ
  have hv (i : ι) : J (v i) = b i := weakEigenvectorLift_image B hB J b μ hμ hev i
  have he (i : ι) (w : E) : Q (v i) w = (((μ i)⁻¹ - c : ℝ) : ℂ) * M (v i) w := by
    have hp := weakEigenvectorLift_pairing B hB J b μ i w
    rw [hshift] at hp
    change Q (v i) w + (c : ℂ) * inner ℂ (J (v i)) (J w) = _ at hp
    rw [hv] at hp
    rw [hm, hv, Complex.ofReal_sub, Complex.ofReal_inv, sub_mul]
    linear_combination hp
  apply spectral_complement_equality Q M hQ (fun x y => inner_conj_symm _ _)
    J hm b v b.orthonormal hv (fun i => (((μ i)⁻¹ - c : ℝ) : ℂ)) he
    s ((μ n)⁻¹ - c)
  · intro x hx
    rw [hmself]
    exact spectral_tail_shifted_lower_bound B hB J hherm b μ hμ hanti hev
      (fun x y => Q x y) c hshift n x (fun i hi => hx i ((hs i).mpr hi))
  · intro i hi
    exact hu i ((hs i).mp hi)
  · rwa [hmself]

end KsIndex.Spectral
