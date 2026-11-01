module

public import KsIndexLean.EndChartLaplacian
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

@[expose] public section


/-! The pointwise Laplacian change of variables under the exponential map. -/
noncomputable section
open Set Complex Topology Filter
open scoped ContDiff
namespace KsIndex.Cylindrical
open Surface EndChart

/-- The real differential of the complex exponential. -/
def expDifferential (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (((1 : ℂ →L[ℂ] ℂ).smulRight (Complex.exp z)).restrictScalars ℝ)

lemma expDifferential_apply (z v : ℂ) : expDifferential z v = Complex.exp z * v := by
  simp [expDifferential, ContinuousLinearMap.coe_restrictScalars', mul_comm]

lemma hasFDerivAt_exp_real (z : ℂ) : HasFDerivAt Complex.exp (expDifferential z) z :=
  (Complex.hasDerivAt_exp z).hasFDerivAt.restrictScalars ℝ

/-- The logarithmic coordinate Laplacian has the exponential Jacobian weight. -/
theorem laplacian_comp_exp {u : ℂ → ℂ} {ζ : ℂ}
    (hu : ContDiffAt ℝ 2 u (Complex.exp ζ)) :
    laplacian (u ∘ Complex.exp) ζ =
      ((‖Complex.exp ζ‖ ^ 2 : ℝ) : ℂ) * laplacian u (Complex.exp ζ) := by
  set q : ℂ := Complex.exp ζ with hqdef
  set c : ℂ := Complex.exp ζ with hcdef
  have hu1 : ContDiffAt ℝ 1 (fderiv ℝ u) q := hu.fderiv_right le_rfl
  set B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := fderiv ℝ (fderiv ℝ u) q with hBdef
  have hev : ∀ᶠ z in nhds ζ, fderiv ℝ (u ∘ Complex.exp) z =
      (fderiv ℝ u (Complex.exp z)).comp (expDifferential z) := by
    have hu' : ∀ᶠ y in nhds q, DifferentiableAt ℝ u y := by
      filter_upwards [hu.eventually (by simp)] with y hy
      exact hy.differentiableAt (by norm_num)
    have hφc : ContinuousAt (Complex.exp) ζ :=
      (hasFDerivAt_exp_real ζ).differentiableAt.continuousAt
    filter_upwards [hφc.eventually hu'] with z hz
    rw [fderiv_comp z hz (hasFDerivAt_exp_real z).differentiableAt,
      (hasFDerivAt_exp_real z).fderiv]
  have hA : DifferentiableAt ℝ (fun z => fderiv ℝ u (Complex.exp z)) ζ :=
    (hu1.differentiableAt (by norm_num)).comp ζ
      (hasFDerivAt_exp_real ζ).differentiableAt
  have hAderiv : fderiv ℝ (fun z => fderiv ℝ u (Complex.exp z)) ζ =
      B.comp (expDifferential ζ) := by
    change fderiv ℝ (fderiv ℝ u ∘ Complex.exp) ζ = _
    rw [fderiv_comp ζ (hu1.differentiableAt (by norm_num))
      (hasFDerivAt_exp_real ζ).differentiableAt,
      (hasFDerivAt_exp_real ζ).fderiv]
  obtain ⟨D, hD⟩ : ∃ D, HasDerivAt (fun z : ℂ => Complex.exp z) D ζ :=
    ⟨_, Complex.hasDerivAt_exp ζ⟩
  have hsecond : ∀ e : ℂ,
      fderiv ℝ (fun z => (fderiv ℝ u (Complex.exp z)) (expDifferential z e)) ζ e =
        (fderiv ℝ u q) (e * (D * e)) + B (c * e) (c * e) := by
    intro e
    have hve : HasDerivAt (fun z : ℂ => Complex.exp z * e) (D * e) ζ :=
      hD.mul_const e
    have hveR : DifferentiableAt ℝ (fun z : ℂ => Complex.exp z * e) ζ :=
      (hve.hasFDerivAt.restrictScalars ℝ).differentiableAt
    have hveq : (fun z => (fderiv ℝ u (Complex.exp z)) (expDifferential z e)) =
        fun z => (fderiv ℝ u (Complex.exp z)) (Complex.exp z * e) := by
      funext z
      rw [expDifferential_apply]
    rw [hveq, fderiv_clm_apply hA hveR]
    simp only [add_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.comp_apply]
    congr 1
    · congr 1
      have hfd := (hve.hasFDerivAt.restrictScalars ℝ).fderiv
      rw [hfd]
      simp [ContinuousLinearMap.coe_restrictScalars']
    · rw [hAderiv]
      simp only [ContinuousLinearMap.comp_apply, expDifferential_apply]
      rfl
  have hlap : laplacian (u ∘ Complex.exp) ζ =
      (fderiv ℝ u q) (1 * (D * 1)) + B (c * 1) (c * 1) +
        ((fderiv ℝ u q) (Complex.I * (D * Complex.I)) +
          B (c * Complex.I) (c * Complex.I)) := by
    unfold laplacian
    have he1 : (fun z => fderiv ℝ (u ∘ Complex.exp) z 1) =ᶠ[nhds ζ]
        fun z => (fderiv ℝ u (Complex.exp z)) (expDifferential z 1) := by
      filter_upwards [hev] with z hz
      rw [hz]
      rfl
    have heI : (fun z => fderiv ℝ (u ∘ Complex.exp) z Complex.I) =ᶠ[nhds ζ]
        fun z => (fderiv ℝ u (Complex.exp z)) (expDifferential z Complex.I) := by
      filter_upwards [hev] with z hz
      rw [hz]
      rfl
    have h1 := he1.fderiv_eq (𝕜 := ℝ)
    have hI := heI.fderiv_eq (𝕜 := ℝ)
    rw [h1, hI, hsecond 1, hsecond Complex.I]
  rw [hlap]
  have hIarg : Complex.I * (D * Complex.I) = -(1 * (D * 1)) := by
    rw [show Complex.I * (D * Complex.I) = D * (Complex.I * Complex.I) from by ring,
      Complex.I_mul_I]
    ring
  rw [hIarg, map_neg]
  have hw : B (c * 1) (c * 1) + B (c * Complex.I) (c * Complex.I) =
      ((‖c‖ ^ 2 : ℝ) : ℂ) * (B 1 1 + B Complex.I Complex.I) := by
    rw [mul_one]
    exact bilinear_frame_weight B c
  have hlapu : B 1 1 + B Complex.I Complex.I = laplacian u q := by
    unfold laplacian
    have he : ∀ e : ℂ, fderiv ℝ (fun z => fderiv ℝ u z e) q e = B e e := by
      intro e
      have h := fderiv_clm_apply (c := fderiv ℝ u) (u := fun _ => e)
        (hu1.differentiableAt (by norm_num)) (differentiableAt_const e)
      rw [h, (hasFDerivAt_const e q).fderiv]
      simp [ContinuousLinearMap.flip_apply, hBdef]
    rw [he 1, he Complex.I]
  calc (fderiv ℝ u q) (1 * (D * 1)) + B (c * 1) (c * 1) +
        (-((fderiv ℝ u q) (1 * (D * 1))) + B (c * Complex.I) (c * Complex.I))
      = B (c * 1) (c * 1) + B (c * Complex.I) (c * Complex.I) := by ring
    _ = ((‖c‖ ^ 2 : ℝ) : ℂ) * (B 1 1 + B Complex.I Complex.I) := hw
    _ = ((‖Complex.exp ζ‖ ^ 2 : ℝ) : ℂ) * laplacian u q := by
        rw [hcdef, hlapu]

end KsIndex.Cylindrical
