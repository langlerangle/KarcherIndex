module

public import KsIndexLean.WirtingerPolynomialProduct
public import KsIndexLean.ExplicitModeFlux

@[expose] public section


noncomputable section
namespace KsIndex.Trace
open KsIndex.JacobiFields KsIndex.JacobiMode KsIndex.Radial KsIndex.Surface

lemma modeU_eq_shifted_Ffun {k : ℕ} (hk : 2 ≤ k) (ℓ : ℕ) :
    modeU k ℓ = fun z => (Ffun (k-1) 0 0 1 z * (-((k-1 : ℕ) : ℂ)) + (ℓ : ℂ)) * z ^ ℓ := by
  funext z
  unfold modeU gRad kap Ffun Nfun Dfun
  rw [show 2 * k - 2 = 2 * (k - 1) by omega]
  push_cast
  rw [norm_pow_eq]
  have hkcast : ((k-1 : ℕ) : ℂ) = (k : ℂ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  rw [hkcast]
  have hd := Dfun_ne_zero (k-1) z
  unfold Dfun at hd
  field_simp
  ring

lemma modeU_jacobi {k : ℕ} (hk : 2 ≤ k) (ℓ : ℕ) (w : ℂ) :
    laplacian (modeU k ℓ) w + (potV k w : ℂ) * modeU k ℓ w = 0 := by
  rw [modeU_eq_shifted_Ffun hk ℓ, potV_eq k hk]
  exact jacobi_shifted_Ffun (k-1) ℓ (by omega) w

lemma laplacian_conjugate (f : ℂ → ℂ) (w : ℂ) :
    laplacian (fun z => (starRingEnd ℂ) (f z)) w = (starRingEnd ℂ) (laplacian f w) := by
  change laplacian (fun z => star (f z)) w = star (laplacian f w)
  simp only [laplacian, fderiv_star, ContinuousLinearMap.comp_apply, star_add]
  change fderiv ℝ (fun z => star (fderiv ℝ f z 1)) w 1 +
    fderiv ℝ (fun z => star (fderiv ℝ f z Complex.I)) w Complex.I = _
  rw [fderiv_star, fderiv_star]
  rfl

lemma signedModeU_jacobi {k : ℕ} (hk : 2 ≤ k) (n : ℤ) (w : ℂ) :
    laplacian (signedModeU k n) w + (potV k w : ℂ) * signedModeU k n w = 0 := by
  cases n with
  | ofNat m => exact modeU_jacobi hk m w
  | negSucc m =>
    change laplacian (fun z => (starRingEnd ℂ) (modeU k (m+1) z)) w +
      (potV k w : ℂ) * (starRingEnd ℂ) (modeU k (m+1) w) = 0
    rw [laplacian_conjugate]
    have h := congrArg (starRingEnd ℂ) (modeU_jacobi hk (m+1) w)
    simpa only [map_add, map_mul, Complex.conj_ofReal, map_zero] using h

open KsIndex.WeakH1 in
lemma weak_neumann_nonresonant_boundary_zero {k : ℕ} (hk : 2 ≤ k)
    (v : ComplexH1) (hv : ∀ w : ComplexH1, weakJacobi (surfacePotential k) v w = 0)
    (n : ℤ) (hn : n.natAbs ≠ k-1) :
    circleFourierCoeff (diskTraceCLM v) n = 0 :=
  weak_neumann_fourier_trace_zero (surfacePotential k) v hv (signedModeU k n)
    (signedModeU_smooth hk n) (fun w _ => signedModeU_jacobi hk n w)
    n _ (signedModeU_flux_nonzero hk n hn) (signedModeU_normal hk n)

end KsIndex.Trace
