module

public import KsIndexLean.EndChartLaplacian
public import KsIndexLean.SphericalInversionJacobian

@[expose] public section


noncomputable section
open Set Complex
open scoped ContDiff
namespace KsIndex.EndChart
open KsIndex.Surface

/-- The flat Laplacian transforms under the seam reflection `σ(z) = 1/z̄`
with weight `‖z‖⁻⁴`, at nonzero `z` where `u` is twice continuously
differentiable at `σ z`. This is the anti-holomorphic counterpart of
`laplacian_comp_endChart`.

The Hessian frame terms reduce by `bilinear_frame_weight`: the two
negations in the imaginary direction cancel in the bilinear slots.
The second-derivative trace of `σ` contributes `Du(D) + Du(-D) = 0`,
so only the weighted Laplacian of `u` remains. -/
theorem laplacian_comp_sigma {u : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0)
    (hu : ContDiffAt ℝ 2 u (Bracket.σ z)) :
    laplacian (u ∘ Bracket.σ) z =
      ((‖z‖⁻¹ ^ 4 : ℝ) : ℂ) * laplacian u (Bracket.σ z) := by
  have hσd : DifferentiableAt ℝ Bracket.σ z :=
    (KsIndex.SigmaDeriv.hasFDerivAt_sigmaR hz).differentiableAt
  have hu1 : ContDiffAt ℝ 1 (fderiv ℝ u) (Bracket.σ z) := hu.fderiv_right le_rfl
  set B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := fderiv ℝ (fderiv ℝ u) (Bracket.σ z) with hBdef
  set a : ℂ := -(((starRingEnd ℂ) z) ^ 2)⁻¹ with hadef
  -- the anti-holomorphic coefficient c and its derivative data
  set c : ℂ → ℂ := fun w => -(((starRingEnd ℂ) w) ^ 2)⁻¹ with hcdef
  have hgc : (starRingEnd ℂ) z ≠ 0 := by simpa using hz
  have hconjFD : HasFDerivAt (fun w : ℂ => (starRingEnd ℂ) w)
      (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ) z := by
    have hfun : (fun w : ℂ => (starRingEnd ℂ) w) = ⇑Complex.conjCLE := by
      funext w
      rw [Complex.conjCLE_apply]
    rw [hfun]
    exact Complex.conjCLE.hasFDerivAt
  obtain ⟨D, hD⟩ : ∃ D : ℂ, HasFDerivAt c
      ((((1 : ℂ →L[ℂ] ℂ).smulRight D).restrictScalars ℝ).comp
        (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ)) z := by
    have hg : HasDerivAt (fun y : ℂ => -((y ^ 2)⁻¹))
        (-(-(((2 : ℕ) : ℂ) * ((starRingEnd ℂ) z) ^ (2 - 1)) /
          ((((starRingEnd ℂ) z) ^ 2) ^ 2))) ((starRingEnd ℂ) z) :=
      ((hasDerivAt_pow 2 ((starRingEnd ℂ) z)).inv (pow_ne_zero 2 hgc)).neg
    exact ⟨_, (hg.hasFDerivAt.restrictScalars ℝ).comp z hconjFD⟩
  have hDapp : ∀ e : ℂ, fderiv ℝ c z e = D * (starRingEnd ℂ) e := by
    intro e
    rw [hD.fderiv]
    simp [ContinuousLinearMap.coe_restrictScalars', mul_comm]
  -- eventual identities near z (where w ≠ 0)
  have hevσ : ∀ᶠ w in nhds z, ∀ e : ℂ,
      fderiv ℝ Bracket.σ w e = (starRingEnd ℂ) e * c w := by
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw0
    intro e
    have h : fderiv ℝ (fun x : ℂ => 1 / (starRingEnd ℂ) x) w e =
        -(((starRingEnd ℂ) w) ^ 2)⁻¹ * (starRingEnd ℂ) e :=
      KsIndex.SigmaDeriv.fderiv_sigmaR_apply hw0 e
    change fderiv ℝ (fun x : ℂ => 1 / (starRingEnd ℂ) x) w e = _
    rw [h, hcdef]
    ring
  -- the composed-derivative eventual identity
  have hev : ∀ᶠ w in nhds z, fderiv ℝ (u ∘ Bracket.σ) w =
      (fderiv ℝ u (Bracket.σ w)).comp (fderiv ℝ Bracket.σ w) := by
    have hu' : ∀ᶠ y in nhds (Bracket.σ z), DifferentiableAt ℝ u y := by
      filter_upwards [hu.eventually (by simp)] with y hy
      exact hy.differentiableAt (by norm_num)
    filter_upwards [hσd.continuousAt.eventually hu', isOpen_ne.mem_nhds hz]
      with w hw hw0
    rw [fderiv_comp w hw
      (KsIndex.SigmaDeriv.hasFDerivAt_sigmaR hw0).differentiableAt]
  have hA : DifferentiableAt ℝ (fun w => fderiv ℝ u (Bracket.σ w)) z :=
    (hu1.differentiableAt (by norm_num)).comp z hσd
  have hAderiv : fderiv ℝ (fun w => fderiv ℝ u (Bracket.σ w)) z =
      B.comp (fderiv ℝ Bracket.σ z) := by
    change fderiv ℝ (fderiv ℝ u ∘ Bracket.σ) z = _
    rw [fderiv_comp z (hu1.differentiableAt (by norm_num)) hσd]
  have hL1 : fderiv ℝ Bracket.σ z 1 = a := by
    change fderiv ℝ (fun x : ℂ => 1 / (starRingEnd ℂ) x) z 1 = _
    rw [KsIndex.SigmaDeriv.fderiv_sigmaR_apply hz 1]
    simp [hadef]
  have hLI : fderiv ℝ Bracket.σ z Complex.I = -(a * Complex.I) := by
    change fderiv ℝ (fun x : ℂ => 1 / (starRingEnd ℂ) x) z Complex.I = _
    rw [KsIndex.SigmaDeriv.fderiv_sigmaR_apply hz Complex.I, Complex.conj_I]
    rw [hadef]
    ring
  -- per-direction second derivative
  have hsecond : ∀ e : ℂ,
      fderiv ℝ (fun w => (fderiv ℝ u (Bracket.σ w)) (fderiv ℝ Bracket.σ w e)) z e =
        (fderiv ℝ u (Bracket.σ z))
            (((starRingEnd ℂ) e) ^ 2 * D)
          + B (fderiv ℝ Bracket.σ z e) (fderiv ℝ Bracket.σ z e) := by
    intro e
    have hvev : (fun w => fderiv ℝ Bracket.σ w e) =ᶠ[nhds z]
        fun w => (starRingEnd ℂ) e * c w := by
      filter_upwards [hevσ] with w hw
      exact hw e
    have hvd : DifferentiableAt ℝ (fun w => (starRingEnd ℂ) e * c w) z :=
      (hD.differentiableAt.const_mul _)
    have hvd' : DifferentiableAt ℝ (fun w => fderiv ℝ Bracket.σ w e) z :=
      hvd.congr_of_eventuallyEq hvev
    have hfe : (fun w => (fderiv ℝ u (Bracket.σ w)) (fderiv ℝ Bracket.σ w e))
        =ᶠ[nhds z]
        fun w => (fderiv ℝ u (Bracket.σ w)) ((starRingEnd ℂ) e * c w) := by
      filter_upwards [hvev] with w hw
      rw [hw]
    rw [Filter.EventuallyEq.fderiv_eq hfe, fderiv_clm_apply hA
      ((hD.differentiableAt).const_mul _)]
    simp only [add_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.comp_apply]
    congr 1
    · -- the trace term: Du applied to conj(e)·(fderiv c z e) = conj(e)²·D
      congr 1
      rw [fderiv_const_mul (hD.differentiableAt)]
      simp only [smul_apply, hDapp e, smul_eq_mul]
      ring
    · -- the frame term: B at the σ-directions, via the eventual identity
      rw [hAderiv]
      simp only [ContinuousLinearMap.comp_apply]
      rw [show (starRingEnd ℂ) e * c z = fderiv ℝ Bracket.σ z e from
        (hevσ.self_of_nhds e).symm]
  -- assemble the Laplacian
  have hlap : laplacian (u ∘ Bracket.σ) z =
      ((fderiv ℝ u (Bracket.σ z)) (((starRingEnd ℂ) 1) ^ 2 * D)
          + B (fderiv ℝ Bracket.σ z 1) (fderiv ℝ Bracket.σ z 1))
        + ((fderiv ℝ u (Bracket.σ z)) (((starRingEnd ℂ) Complex.I) ^ 2 * D)
          + B (fderiv ℝ Bracket.σ z Complex.I) (fderiv ℝ Bracket.σ z Complex.I)) := by
    unfold laplacian
    have he1 : (fun w => fderiv ℝ (u ∘ Bracket.σ) w 1) =ᶠ[nhds z]
        fun w => (fderiv ℝ u (Bracket.σ w)) (fderiv ℝ Bracket.σ w 1) := by
      filter_upwards [hev] with w hw
      rw [hw]
      rfl
    have heI : (fun w => fderiv ℝ (u ∘ Bracket.σ) w Complex.I) =ᶠ[nhds z]
        fun w => (fderiv ℝ u (Bracket.σ w)) (fderiv ℝ Bracket.σ w Complex.I) := by
      filter_upwards [hev] with w hw
      rw [hw]
      rfl
    rw [he1.fderiv_eq (𝕜 := ℝ), heI.fderiv_eq (𝕜 := ℝ), hsecond 1, hsecond Complex.I]
  rw [hlap, hL1, hLI]
  -- the trace terms cancel: conj(1)² = 1, conj(I)² = −1
  have htr1 : ((starRingEnd ℂ) 1) ^ 2 * D = D := by simp
  have htrI : ((starRingEnd ℂ) Complex.I) ^ 2 * D = -D := by
    rw [Complex.conj_I]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [htr1, htrI]
  have hDneg : (fderiv ℝ u (Bracket.σ z)) (-D) =
      -((fderiv ℝ u (Bracket.σ z)) D) := map_neg _ _
  -- the frame terms: B(−aI)(−aI) = B(aI)(aI) (two negations cancel bilinearly)
  have hframe : B (-(a * Complex.I)) (-(a * Complex.I)) =
      B (a * Complex.I) (a * Complex.I) := by
    rw [map_neg]
    simp
  rw [hDneg, hframe]
  have hna : ‖a‖ ^ 2 = ‖z‖⁻¹ ^ 4 := by
    rw [hadef, norm_neg, norm_inv, norm_pow, Complex.norm_conj, ← inv_pow, ← pow_mul]
  have hw := bilinear_frame_weight B a
  have hlapu : B 1 1 + B Complex.I Complex.I = laplacian u (Bracket.σ z) := by
    unfold laplacian
    have he : ∀ e : ℂ, fderiv ℝ (fun y => fderiv ℝ u y e) (Bracket.σ z) e = B e e := by
      intro e
      have h := fderiv_clm_apply (c := fderiv ℝ u) (u := fun _ => e)
        (hu1.differentiableAt (by norm_num)) (differentiableAt_const e)
      rw [h, (hasFDerivAt_const e (Bracket.σ z)).fderiv]
      simp [ContinuousLinearMap.flip_apply, hBdef]
    rw [he 1, he Complex.I]
  calc (fderiv ℝ u (Bracket.σ z)) D + B a a +
        (-((fderiv ℝ u (Bracket.σ z)) D) + B (a * Complex.I) (a * Complex.I))
      = B a a + B (a * Complex.I) (a * Complex.I) := by ring
    _ = ((‖a‖ ^ 2 : ℝ) : ℂ) * (B 1 1 + B Complex.I Complex.I) := hw
    _ = ((‖z‖⁻¹ ^ 4 : ℝ) : ℂ) * laplacian u (Bracket.σ z) := by
        rw [hna, hlapu]

end KsIndex.EndChart
