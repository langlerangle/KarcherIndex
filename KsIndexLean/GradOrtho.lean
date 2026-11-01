module

/-
# Gradient orthogonality of distinct angular modes

The Dirichlet cross integral of distinct modes vanishes by rotational
symmetry. Together with `ThetaOrtho.disk_offdiag_potV`, this removes the
cross terms from the Jacobi energy of a finite mode sum.

The gradient cross density is conjugate-linear in its first argument.
Differentiating the mode character identity and rotating the real
orthonormal basis `{1, I}` show that
`gradInner (modeU k ℓ') (modeU k ℓ)` transforms by
`a^ℓ * conj(a^ℓ')` under a unit rotation. A rotation for which this scalar
is `-1` forces the cross integral to vanish. The derivative calculation
here is made away from the origin; almost-everywhere equivariance suffices.
-/
public import KsIndexLean.ThetaOrtho

@[expose] public section


noncomputable section

namespace KsIndex.GradOrtho

open Complex Real MeasureTheory
  KsIndex.Radial KsIndex.JacobiExtension KsIndex.JacobiMode KsIndex.ThetaOrtho

variable {k ℓ ℓ' : ℕ}

/-! ### The sesquilinear gradient-cross integrand -/

/-- The Dirichlet cross density of two `ℂ`-valued functions on `ℂ ≅ ℝ²`:
`⟨∇f, ∇g⟩ = conj(∂_x f)·∂_x g + conj(∂_y f)·∂_y g`, with `∂_x = fderiv ℝ · 1`, `∂_y = fderiv ℝ · I`.
Its diagonal `gradInner f f = ↑(gradSq f)` is the flat gradient density; the conjugate sits on the
first slot to match the potential cross term `potV·conj(modeU_{ℓ'})·modeU_ℓ`. -/
def gradInner (f g : ℂ → ℂ) (w : ℂ) : ℂ :=
  starRingEnd ℂ (fderiv ℝ f w 1) * fderiv ℝ g w 1
    + starRingEnd ℂ (fderiv ℝ f w I) * fderiv ℝ g w I

/-- Consistency: the diagonal of the cross density is the flat gradient density `gradSq`. -/
lemma gradInner_self (f : ℂ → ℂ) (w : ℂ) : gradInner f f w = (Surface.gradSq f w : ℂ) := by
  have h : ∀ z : ℂ, starRingEnd ℂ z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [gradInner, Surface.gradSq, h, h]
  push_cast; ring

/-! ### Differentiability of `modeU` off the origin -/

/-- `modeU k ℓ` is `ℝ`-differentiable away from `0` (the profile `gRad ∘ ‖·‖` is differentiable off
`0`, the angular part `w^ℓ` is holomorphic). -/
lemma modeU_differentiableAt (hk : 2 ≤ k) (ℓ : ℕ) {w : ℂ} (hw : w ≠ 0) :
    DifferentiableAt ℝ (modeU k ℓ) w := by
  have hB : DifferentiableAt ℝ (fun z : ℂ => z ^ ℓ) w :=
    ((hasDerivAt_pow ℓ w).hasFDerivAt.restrictScalars ℝ).differentiableAt
  have hR : DifferentiableAt ℝ (fun z : ℂ => gRad k ℓ ‖z‖) w :=
    ((gRad_hasDerivAt hk ℓ ‖w‖).comp_hasFDerivAt w (hasFDerivAt_norm_ne hw)).differentiableAt
  have hA : DifferentiableAt ℝ (fun z : ℂ => (gRad k ℓ ‖z‖ : ℂ)) w :=
    (Complex.ofRealCLM.differentiableAt).comp w hR
  exact hA.mul hB

/-! ### Differentiating the character identity -/

/-- **The Fréchet derivative of a mode is rotation-equivariant.**  Differentiating the character
identity `modeU k ℓ (a·z) = aˡ·modeU k ℓ z` (chain rule through `z ↦ a·z`) gives, for `w ≠ 0`,
`∂(modeU k ℓ)(a·w)(a·v) = aˡ · ∂(modeU k ℓ)(w)(v)`. -/
lemma modeU_fderiv_rotation (hk : 2 ≤ k) (ℓ : ℕ) {a : ℂ} (ha : ‖a‖ = 1) {w : ℂ} (hw : w ≠ 0)
    (v : ℂ) :
    fderiv ℝ (modeU k ℓ) (a * w) (a * v) = a ^ ℓ * fderiv ℝ (modeU k ℓ) w v := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have haw : a * w ≠ 0 := mul_ne_zero ha0 hw
  have hfw : HasFDerivAt (modeU k ℓ) (fderiv ℝ (modeU k ℓ) w) w :=
    (modeU_differentiableAt hk ℓ hw).hasFDerivAt
  have hfaw : HasFDerivAt (modeU k ℓ) (fderiv ℝ (modeU k ℓ) (a * w)) (a * w) :=
    (modeU_differentiableAt hk ℓ haw).hasFDerivAt
  have hLa : HasFDerivAt (fun z : ℂ => a * z) (a • ContinuousLinearMap.id ℝ ℂ) w := by
    have hfun : (fun z : ℂ => a * z) = ⇑(a • ContinuousLinearMap.id ℝ ℂ) := by
      funext z; simp [smul_eq_mul]
    rw [hfun]; exact (a • ContinuousLinearMap.id ℝ ℂ).hasFDerivAt
  have hcomp : HasFDerivAt (fun z => modeU k ℓ (a * z))
      ((fderiv ℝ (modeU k ℓ) (a * w)).comp (a • ContinuousLinearMap.id ℝ ℂ)) w := hfaw.comp w hLa
  have heq : (fun z => modeU k ℓ (a * z)) = fun z => a ^ ℓ • modeU k ℓ z := by
    funext z; rw [modeU_rotation k ℓ ha z, smul_eq_mul]
  rw [heq] at hcomp
  have hother : HasFDerivAt (fun z => a ^ ℓ • modeU k ℓ z) (a ^ ℓ • fderiv ℝ (modeU k ℓ) w) w :=
    hfw.const_smul (a ^ ℓ)
  have huniq := hcomp.unique hother
  have happ := ContinuousLinearMap.ext_iff.mp huniq v
  simpa only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul] using happ

/-! ### Rotating the orthonormal basis of `ℂ` -/

/-- **Basis-rotation invariance of the Dirichlet sum.**  For `ℝ`-linear `L, M : ℂ → ℂ` and a unit
`a`, the sum `conj(L·)·(M·)` over the orthonormal basis `{1, I}` equals the same sum over the
rotated orthonormal basis `{a·1, a·I}`.  This is where `‖a‖² = a.re² + a.im² = 1` enters. -/
lemma basis_rot (L M : ℂ →L[ℝ] ℂ) {a : ℂ} (ha : ‖a‖ = 1) :
    starRingEnd ℂ (L 1) * M 1 + starRingEnd ℂ (L I) * M I
      = starRingEnd ℂ (L (a * 1)) * M (a * 1) + starRingEnd ℂ (L (a * I)) * M (a * I) := by
  have habC : (a.re : ℂ) ^ 2 + (a.im : ℂ) ^ 2 = 1 := by
    have hab : a.re ^ 2 + a.im ^ 2 = 1 := by rw [← nsq a, ha]; norm_num
    exact_mod_cast hab
  have ha1 : a * 1 = (a.re : ℝ) • (1 : ℂ) + (a.im : ℝ) • I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  have haI : a * I = (-a.im : ℝ) • (1 : ℂ) + (a.re : ℝ) • I := by
    apply Complex.ext <;>
      simp [Complex.real_smul, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im]
  -- distribute `L`, `M` over the (real-smul) basis decomposition FIRST, then convert smuls to mults
  have eLa1 : L (a * 1) = (a.re : ℝ) • L 1 + (a.im : ℝ) • L I := by
    rw [ha1, map_add, map_smul, map_smul]
  have eLaI : L (a * I) = (-a.im : ℝ) • L 1 + (a.re : ℝ) • L I := by
    rw [haI, map_add, map_smul, map_smul]
  have eMa1 : M (a * 1) = (a.re : ℝ) • M 1 + (a.im : ℝ) • M I := by
    rw [ha1, map_add, map_smul, map_smul]
  have eMaI : M (a * I) = (-a.im : ℝ) • M 1 + (a.re : ℝ) • M I := by
    rw [haI, map_add, map_smul, map_smul]
  rw [eLa1, eLaI, eMa1, eMaI]
  simp only [Complex.real_smul, map_add, map_mul, Complex.conj_ofReal]
  push_cast
  linear_combination (-(starRingEnd ℂ (L 1) * M 1 + starRingEnd ℂ (L I) * M I)) * habC

/-! ### The gradient cross density is rotation-equivariant -/

/-- **The gradient cross density transforms by the character `aˡ·conj(aˡ')`.**  Combining
`basis_rot` (rotate the basis to `{a, a·I}`) with `modeU_fderiv_rotation` (pull out the character on
each rotated basis vector), for `w ≠ 0`,
`gradInner (modeU ℓ') (modeU ℓ) (a·w) = (aˡ · conj(aˡ')) · gradInner (modeU ℓ') (modeU ℓ) w`. -/
lemma gradInner_modeU_rotation (hk : 2 ≤ k) (ℓ ℓ' : ℕ) {a : ℂ} (ha : ‖a‖ = 1) {w : ℂ} (hw : w ≠ 0) :
    gradInner (modeU k ℓ') (modeU k ℓ) (a * w)
      = (a ^ ℓ * starRingEnd ℂ (a ^ ℓ')) * gradInner (modeU k ℓ') (modeU k ℓ) w := by
  simp only [gradInner]
  rw [basis_rot (fderiv ℝ (modeU k ℓ') (a * w)) (fderiv ℝ (modeU k ℓ) (a * w)) ha,
    modeU_fderiv_rotation hk ℓ' ha hw 1, modeU_fderiv_rotation hk ℓ ha hw 1,
    modeU_fderiv_rotation hk ℓ' ha hw I, modeU_fderiv_rotation hk ℓ ha hw I]
  simp only [map_mul]
  ring

/-! ### The rotation-vanishing engine (a.e. form) and the off-diagonal orthogonality -/

/-- A nontrivial rotation character forces the disk integral to vanish.
Almost-everywhere equivariance suffices, so an exceptional point such as the
origin does not affect the argument. No integrability hypothesis is needed:
this identity uses the total Bochner integral, which is zero when the
integrand is not integrable. -/
lemma setIntegral_disk_eq_zero_of_rotation_ae
    {F : ℂ → ℂ} {a : Circle} {c : ℂ} (hc : c ≠ 1)
    (hequiv : ∀ᵐ w ∂(volume.restrict Surface.disk), F ((a : ℂ) * w) = c * F w) :
    ∫ w in Surface.disk, F w = 0 := by
  have hmp : MeasurePreserving (rotation a) volume volume :=
    (rotation a).measurePreserving
  have hemb : MeasurableEmbedding (rotation a) :=
    (rotation a).toHomeomorph.measurableEmbedding
  have hpre : (rotation a) ⁻¹' Surface.disk = Surface.disk := by
    ext w
    simp only [Set.mem_preimage, rotation_apply, Surface.disk, Metric.mem_ball, dist_zero_right,
      norm_mul, Circle.norm_coe, one_mul]
  have hcov : ∫ w in Surface.disk, F ((a : ℂ) * w) = ∫ w in Surface.disk, F w := by
    have h := hmp.setIntegral_preimage_emb hemb F Surface.disk
    rw [hpre] at h
    simpa only [rotation_apply] using h
  have hkey : c * ∫ w in Surface.disk, F w = ∫ w in Surface.disk, F w := by
    have h1 : c * ∫ w in Surface.disk, F w = ∫ w in Surface.disk, F ((a : ℂ) * w) := by
      rw [← MeasureTheory.integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hequiv] with w hw using hw.symm
    rw [h1, hcov]
  have hsub : (c - 1) * ∫ w in Surface.disk, F w = 0 := by
    rw [sub_mul, one_mul, hkey, sub_self]
  rcases mul_eq_zero.mp hsub with h | h
  · exact absurd (sub_eq_zero.mp h) hc
  · exact h

/-- **The disk off-diagonal orthogonality (gradient term).**  For `ℓ ≠ ℓ'`,
`∫_disk ⟨∇(modeU ℓ'), ∇(modeU ℓ)⟩ = 0`: the Dirichlet cross terms of a mode sum vanish — the twin of
`ThetaOrtho.disk_offdiag_potV`.  Proved by rotational symmetry, `a = exp(iπ/(ℓ−ℓ'))` scaling the
cross density by `−1`. -/
lemma disk_offdiag_gradInner (hk : 2 ≤ k) (ℓ ℓ' : ℕ) (hne : ℓ ≠ ℓ') :
    ∫ w in Surface.disk, gradInner (modeU k ℓ') (modeU k ℓ) w = 0 := by
  have hden : (ℓ : ℝ) - (ℓ' : ℝ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  set θ₀ : ℝ := π / ((ℓ : ℝ) - (ℓ' : ℝ)) with hθ₀
  set a : Circle := Circle.exp θ₀ with ha
  have hanorm : ‖(a : ℂ)‖ = 1 := Circle.norm_coe a
  have hreal : ((ℓ : ℝ) - (ℓ' : ℝ)) * θ₀ = π := by rw [hθ₀]; exact mul_div_cancel₀ π hden
  have hexp : (↑ℓ : ℂ) * ((θ₀ : ℂ) * I) + starRingEnd ℂ ((↑ℓ' : ℂ) * ((θ₀ : ℂ) * I))
      = (π : ℂ) * I := by
    have h2 : (↑ℓ : ℂ) * ((θ₀ : ℂ) * I) + starRingEnd ℂ ((↑ℓ' : ℂ) * ((θ₀ : ℂ) * I))
        = (((ℓ : ℝ) - (ℓ' : ℝ)) * θ₀ : ℝ) * I := by
      simp only [map_mul, map_natCast, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    rw [h2, hreal]
  have hscalar : (a : ℂ) ^ ℓ * starRingEnd ℂ ((a : ℂ) ^ ℓ') = -1 := by
    have hcoe : (a : ℂ) = Complex.exp ((θ₀ : ℂ) * I) := by rw [ha, Circle.coe_exp]
    rw [hcoe, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_conj, ← Complex.exp_add,
      hexp, Complex.exp_pi_mul_I]
  have hc_ne : (a : ℂ) ^ ℓ * starRingEnd ℂ ((a : ℂ) ^ ℓ') ≠ 1 := by rw [hscalar]; norm_num
  refine setIntegral_disk_eq_zero_of_rotation_ae (a := a) hc_ne ?_
  have hne0 : ∀ᵐ w ∂(volume.restrict Surface.disk), w ≠ (0 : ℂ) :=
    ae_restrict_of_ae (by rw [ae_iff]; simpa using measure_singleton (0 : ℂ))
  filter_upwards [hne0] with w hw
  exact gradInner_modeU_rotation hk ℓ ℓ' hanorm hw

end KsIndex.GradOrtho
