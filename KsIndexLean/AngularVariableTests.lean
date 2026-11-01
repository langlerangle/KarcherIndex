module

public import KsIndexLean.AngularGraphGluing

@[expose] public section


open Set MeasureTheory
open scoped ContDiff InnerProductSpace

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

def scaledAngularTest (ψ : ℂ → ℝ) (r : ℝ) (w : ℂ) : ℝ := ψ (r • w)

lemma contDiff_scaledAngularTest {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (r : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (scaledAngularTest ψ r) :=
  hψ.comp (r • ContinuousLinearMap.id ℝ ℂ).contDiff

/-- The varying angular test has exactly the derivative of the planar test along r w I. -/
lemma angularTestDeriv_scaled {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (r : ℝ) (w : ℂ) :
    angularTestDeriv (scaledAngularTest ψ r) w =
      fderiv ℝ ψ (r • w) (r • (w * Complex.I)) := by
  have hs := (hasFDerivAt_id (𝕜 := ℝ) w).const_smul r
  have hh := (hψ.differentiable (by simp) (r • w)).hasFDerivAt.comp w hs
  change fderiv ℝ (ψ ∘ fun z : ℂ => r • z) w (w * Complex.I) = _
  rw [hh.fderiv]
  rfl

/-- Common exceptional-set control allows tests to depend on the radius.
This is the form needed for a planar test restricted to each circle. -/
theorem joined_disk_varying_angular_test_ae (u v : ComplexH1) (c : ℂ)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ∀ᵐ r ∂volume.restrict (Ioo (1 / 2 : ℝ) 2),
      inner ℂ (angularTestLp (angularTestDeriv (scaledAngularTest ψ r))
        (contDiff_angularTestDeriv (contDiff_scaledAngularTest hψ r)).continuous)
        (joinAt 1 (diskProfile u) (fun t => c • diskProfile v t⁻¹) r) =
      -inner ℂ (angularTestLp (scaledAngularTest ψ r)
        (contDiff_scaledAngularTest hψ r).continuous)
        (joinAt 1 (diskAngularProfile u) (fun t => c • diskAngularProfile v t⁻¹) r) := by
  filter_upwards [joined_disk_circleAngularGraph_ae u v c] with r hr
  exact (mem_circleAngularGraph_iff _ _).mp hr _ (contDiff_scaledAngularTest hψ r)

end KsIndex.Trace
