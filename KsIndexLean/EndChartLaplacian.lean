module

public import KsIndexLean.EndChartTransport

@[expose] public section


/-!
# The flat Laplacian under the end chart

`Δ(u ∘ endChart p m) ζ = m²·‖ζ‖^{2(m−1)} · (Δu)(endChart p m ζ)` for `u`
of class C² at the image point.

The chain-rule calculation uses two cancellations:
* the `φ″` term contributes `Du(D·1·1) + Du(D·I·I) = Du(D) − Du(D) = 0` —
  the trace of the second chart derivative dies on `1² + I² = 0`, with the
  chart's second derivative `D` left unspecified (no `m`-case analysis);
* the `φ′` term is `B(c)(c) + B(cI)(cI) = ‖c‖²·(B(1)(1) + B(I)(I))` for the
  second derivative `B` of `u` — the frame cross terms cancel pairwise
  between the two directions, so no Hessian symmetry is needed
  (`bilinear_frame_weight`, the second-order sibling of
  `sesq_antilinear_weight`).

Combined with `endPotential p m = Jacobian × potV 3 ∘ endChart`
(EndChartPotential, definitional), this transports the pointwise Jacobi
equation to `ΔF + endPotential·F = 0` on the punctured chart disk — the
pointwise end-chart equation.
-/

noncomputable section
open Set Complex
open scoped ContDiff
namespace KsIndex.EndChart
open KsIndex.Surface

/-! ### The frame algebra (no symmetry needed) -/

/-- Second-order frame weight: for ANY real-bilinear `B` on `ℂ`, evaluating
on the rotated frame `{c, cI}` gives the `‖c‖²`-weighted trace — the mixed
terms cancel pairwise between the two directions. -/
lemma bilinear_frame_weight (B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ) (c : ℂ) :
    B c c + B (c * Complex.I) (c * Complex.I) =
      ((‖c‖ ^ 2 : ℝ) : ℂ) * (B 1 1 + B Complex.I Complex.I) := by
  obtain ⟨r, s, rfl⟩ : ∃ r s : ℝ, c = (r : ℂ) + (s : ℂ) * Complex.I :=
    ⟨c.re, c.im, (Complex.re_add_im c).symm⟩
  have hn : (‖(r : ℂ) + (s : ℂ) * Complex.I‖ ^ 2 : ℝ) = r ^ 2 + s ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  have h2 : (((r : ℂ) + (s : ℂ) * Complex.I) * Complex.I) =
      (-s : ℝ) • (1 : ℂ) + (r : ℝ) • Complex.I := by
    apply Complex.ext <;> simp [Complex.real_smul, Complex.mul_re, Complex.mul_im]
  have h1 : ((r : ℂ) + (s : ℂ) * Complex.I) = (r : ℝ) • (1 : ℂ) + (s : ℝ) • Complex.I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  have key : ∀ a b : ℝ, B ((a : ℝ) • (1 : ℂ) + (b : ℝ) • Complex.I)
      ((a : ℝ) • (1 : ℂ) + (b : ℝ) • Complex.I)
      = ((a : ℂ) * a) * B 1 1 + ((a : ℂ) * b) * B 1 Complex.I
        + ((b : ℂ) * a) * B Complex.I 1 + ((b : ℂ) * b) * B Complex.I Complex.I := by
    intro a b
    simp only [map_add, map_smul]
    simp only [add_apply, smul_apply,
      smul_add, smul_smul]
    simp only [Complex.real_smul]
    push_cast
    ring
  rw [hn, h2, h1, key, key]
  push_cast
  ring

/-! ### Laplacian transformation -/

/-- The flat Laplacian transforms under the end chart
with the Jacobian weight. -/
theorem laplacian_comp_endChart {u : ℂ → ℂ} (p : ℂ) (m : ℕ) {ζ : ℂ}
    (hu : ContDiffAt ℝ 2 u (endChart p m ζ)) :
    laplacian (u ∘ endChart p m) ζ =
      (((m : ℝ) ^ 2 * ‖ζ‖ ^ (2 * (m - 1)) : ℝ) : ℂ) *
        laplacian u (endChart p m ζ) := by
  -- notation
  set q : ℂ := endChart p m ζ with hqdef
  set c : ℂ := (m : ℂ) * ζ ^ (m - 1) with hcdef
  -- the second derivative of u at q
  have hu1 : ContDiffAt ℝ 1 (fderiv ℝ u) q := hu.fderiv_right le_rfl
  set B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := fderiv ℝ (fderiv ℝ u) q with hBdef
  -- the eventual first-derivative identity for the composite
  have hev : ∀ᶠ z in nhds ζ, fderiv ℝ (u ∘ endChart p m) z =
      (fderiv ℝ u (endChart p m z)).comp (endDeriv m z) := by
    have hu' : ∀ᶠ y in nhds q, DifferentiableAt ℝ u y := by
      filter_upwards [hu.eventually (by simp)] with y hy
      exact hy.differentiableAt (by norm_num)
    have hφc : ContinuousAt (endChart p m) ζ :=
      (hasFDerivAt_endChart p m ζ).differentiableAt.continuousAt
    filter_upwards [hφc.eventually hu'] with z hz
    rw [fderiv_comp z hz (hasFDerivAt_endChart p m z).differentiableAt,
      (hasFDerivAt_endChart p m z).fderiv]
  -- per-direction expansion of the second derivative of the composite
  have hA : DifferentiableAt ℝ (fun z => fderiv ℝ u (endChart p m z)) ζ :=
    (hu1.differentiableAt (by norm_num)).comp ζ
      (hasFDerivAt_endChart p m ζ).differentiableAt
  have hAderiv : fderiv ℝ (fun z => fderiv ℝ u (endChart p m z)) ζ =
      B.comp (endDeriv m ζ) := by
    change fderiv ℝ (fderiv ℝ u ∘ endChart p m) ζ = _
    rw [fderiv_comp ζ (hu1.differentiableAt (by norm_num))
      (hasFDerivAt_endChart p m ζ).differentiableAt,
      (hasFDerivAt_endChart p m ζ).fderiv]
  -- the chart-coefficient function and its (existential) derivative
  obtain ⟨D, hD⟩ : ∃ D, HasDerivAt (fun z : ℂ => (m : ℂ) * z ^ (m - 1)) D ζ :=
    ⟨_, (hasDerivAt_pow (m - 1) ζ).const_mul (m : ℂ)⟩
  have hsecond : ∀ e : ℂ,
      fderiv ℝ (fun z => (fderiv ℝ u (endChart p m z)) (endDeriv m z e)) ζ e =
        (fderiv ℝ u q) (e * (D * e)) + B (c * e) (c * e) := by
    intro e
    have hve : HasDerivAt (fun z : ℂ => (m : ℂ) * z ^ (m - 1) * e) (D * e) ζ :=
      hD.mul_const e
    have hveR : DifferentiableAt ℝ (fun z : ℂ => (m : ℂ) * z ^ (m - 1) * e) ζ :=
      (hve.hasFDerivAt.restrictScalars ℝ).differentiableAt
    have hveq : (fun z => (fderiv ℝ u (endChart p m z)) (endDeriv m z e)) =
        fun z => (fderiv ℝ u (endChart p m z)) ((m : ℂ) * z ^ (m - 1) * e) := by
      funext z
      rw [endDeriv_apply]
    rw [hveq, fderiv_clm_apply hA hveR]
    simp only [add_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.comp_apply]
    congr 1
    · congr 1
      have hfd := (hve.hasFDerivAt.restrictScalars ℝ).fderiv
      rw [hfd]
      simp [ContinuousLinearMap.coe_restrictScalars']
    · rw [hAderiv]
      simp only [ContinuousLinearMap.comp_apply, endDeriv_apply]
      rfl
  -- the Laplacian of the composite
  have hlap : laplacian (u ∘ endChart p m) ζ =
      (fderiv ℝ u q) (1 * (D * 1)) + B (c * 1) (c * 1) +
        ((fderiv ℝ u q) (Complex.I * (D * Complex.I)) +
          B (c * Complex.I) (c * Complex.I)) := by
    unfold laplacian
    have he1 : (fun z => fderiv ℝ (u ∘ endChart p m) z 1) =ᶠ[nhds ζ]
        fun z => (fderiv ℝ u (endChart p m z)) (endDeriv m z 1) := by
      filter_upwards [hev] with z hz
      rw [hz]
      rfl
    have heI : (fun z => fderiv ℝ (u ∘ endChart p m) z Complex.I) =ᶠ[nhds ζ]
        fun z => (fderiv ℝ u (endChart p m z)) (endDeriv m z Complex.I) := by
      filter_upwards [hev] with z hz
      rw [hz]
      rfl
    have h1 := he1.fderiv_eq (𝕜 := ℝ)
    have hI := heI.fderiv_eq (𝕜 := ℝ)
    rw [h1, hI, hsecond 1, hsecond Complex.I]
  rw [hlap]
  -- the φ″ trace terms cancel on 1² + I² = 0
  have hIarg : Complex.I * (D * Complex.I) = -(1 * (D * 1)) := by
    rw [show Complex.I * (D * Complex.I) = D * (Complex.I * Complex.I) from by ring,
      Complex.I_mul_I]
    ring
  rw [hIarg, map_neg]
  -- the frame weight on the second-derivative terms
  have hw : B (c * 1) (c * 1) + B (c * Complex.I) (c * Complex.I) =
      ((‖c‖ ^ 2 : ℝ) : ℂ) * (B 1 1 + B Complex.I Complex.I) := by
    rw [mul_one]
    exact bilinear_frame_weight B c
  have hcnorm : (‖c‖ ^ 2 : ℝ) = (m : ℝ) ^ 2 * ‖ζ‖ ^ (2 * (m - 1)) := by
    rw [hcdef, norm_mul, Complex.norm_natCast, norm_pow, mul_pow, ← pow_mul,
      mul_comm (m - 1) 2]
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
    _ = (((m : ℝ) ^ 2 * ‖ζ‖ ^ (2 * (m - 1)) : ℝ) : ℂ) * laplacian u q := by
        rw [hcnorm, hlapu]

end KsIndex.EndChart
