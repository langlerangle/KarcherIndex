module

public import KsIndexLean.SigmaDeriv
public import KsIndexLean.SignedWeakReflection
public import KsIndexLean.WeakH1Localization

@[expose] public section


open Set MeasureTheory
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket

/-- Differentiate actual inversion invariance of a smooth real cutoff. -/
lemma invariant_cutoff_derivative {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hi : ∀ z, χ (σ z) = χ z) {z : ℂ} (hz : z ≠ 0) :
    (fderiv ℝ χ (σ z)).comp (fderiv ℝ σ z) = fderiv ℝ χ z := by
  have hσ : DifferentiableAt ℝ σ z :=
    (KsIndex.SigmaDeriv.hasFDerivAt_sigmaR hz).differentiableAt
  have hh := (hχ.differentiable (by norm_num) (σ z)).hasFDerivAt.comp z hσ.hasFDerivAt
  have he : χ ∘ σ = χ := funext hi
  rw [he] at hh
  exact hh.fderiv.symm

lemma localized_value_parity {χ : ℂ → ℝ} (hi : ∀ z, χ (σ z) = χ z)
    (s : ℂ) {u : ℂ → ℂ} (hu : ∀ᵐ z ∂volume, s • u (σ z) = u z) :
    ∀ᵐ z ∂volume, s • (χ (σ z) • u (σ z)) = χ z • u z := by
  filter_upwards [hu] with z hz
  rw [hi, smul_comm s (χ z), hz]

/-- The full localized weak jet retains reflection parity, including the cutoff derivative. -/
lemma localized_jet_parity {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hi : ∀ z, χ (σ z) = χ z) (s : ℂ) {u : ℂ → ℂ} {J : ℂ → ℂ →L[ℝ] ℂ}
    (hu : ∀ᵐ z ∂volume, s • u (σ z) = u z)
    (hJ : ∀ᵐ z ∂volume, s • (J (σ z)).comp (fderiv ℝ σ z) = J z) :
    ∀ᵐ z ∂volume,
      s • (χ (σ z) • J (σ z) + (fderiv ℝ χ (σ z)).smulRight (u (σ z))).comp
        (fderiv ℝ σ z) = χ z • J z + (fderiv ℝ χ z).smulRight (u z) := by
  filter_upwards [hu, hJ, volume.ae_ne (0 : ℂ)] with z hu hJ hz
  ext d
  have hd := congrArg (fun L : ℂ →L[ℝ] ℝ => L d) (invariant_cutoff_derivative hχ hi hz)
  have hj := congrArg (fun L : ℂ →L[ℝ] ℂ => L d) hJ
  change fderiv ℝ χ (σ z) (fderiv ℝ σ z d) = fderiv ℝ χ z d at hd
  change s • J (σ z) (fderiv ℝ σ z d) = J z d at hj
  change s • (χ (σ z) • J (σ z) (fderiv ℝ σ z d) +
      fderiv ℝ χ (σ z) (fderiv ℝ σ z d) • u (σ z)) =
    χ z • J z d + fderiv ℝ χ z d • u z
  rw [smul_add, hi, hd, smul_comm s (χ z), smul_comm s (fderiv ℝ χ z d), hj, hu]

end KsIndex.Trace
