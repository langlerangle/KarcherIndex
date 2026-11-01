module

/-
KsIndexLean — ThetaOrtho: angular orthogonality for disk-energy assembly.

Integer angular characters satisfy
`∫₀^{2π} exp(i n θ) dθ = 2π` for `n = 0` and vanish otherwise.
The same identity holds on the polar angle interval `(-π, π)`.

This file also gives polar-coordinate formulas for the radial potential and
modes, and proves that the potential pairing between distinct angular modes
vanishes. The disk-integral proof uses rotation invariance: a suitable rotation
multiplies the off-diagonal integrand by `-1` while preserving its integral.
These results supply the angular orthogonality used in disk-energy assembly.
-/
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import KsIndexLean.JacobiMode

@[expose] public section


noncomputable section

namespace KsIndex.ThetaOrtho

open Complex Real MeasureTheory intervalIntegral KsIndex.Radial KsIndex.JacobiExtension
  KsIndex.JacobiMode

/-- **Character orthogonality on the circle**: for `n : ℤ`,
`∫₀^{2π} e^{i n θ} dθ = 2π` if `n = 0`, and `0` otherwise.  The elementary engine that
diagonalizes the disk energy over angular frequencies (the cross terms carry `n = ℓ − ℓ' ≠ 0`). -/
lemma charInt (n : ℤ) :
    (∫ θ in (0:ℝ)..(2 * π), Complex.exp ((n : ℂ) * I * θ))
      = if n = 0 then (2 * π : ℂ) else 0 := by
  rcases eq_or_ne n 0 with hn | hn
  · -- `n = 0`: the integrand is the constant `1`.
    subst hn
    rw [if_pos rfl]
    simp only [Int.cast_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const,
      sub_zero, Complex.real_smul, mul_one]
    push_cast; ring
  · -- `n ≠ 0`: antiderivative `e^{inθ}/(in)`, and `e^{i n 2π} = 1` by the integer period.
    rw [if_neg hn]
    have hc : (n : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hn) Complex.I_ne_zero
    rw [integral_exp_mul_complex hc]
    have e1 : Complex.exp ((n : ℂ) * I * ((2 * π : ℝ) : ℂ)) = 1 := by
      have harg : (n : ℂ) * I * ((2 * π : ℝ) : ℂ) = (n : ℂ) * (2 * (π : ℂ) * I) := by
        push_cast; ring
      rw [harg]; simp
    have e0 : Complex.exp ((n : ℂ) * I * ((0 : ℝ) : ℂ)) = 1 := by
      rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [e1, e0, sub_self, zero_div]

/-- The angular character `θ ↦ e^{i n θ}` is `2π`-periodic (`n : ℤ`). -/
lemma exp_char_periodic (n : ℤ) :
    Function.Periodic (fun θ : ℝ => Complex.exp ((n : ℂ) * I * θ)) (2 * π) := by
  intro θ
  have h1 : Complex.exp ((n : ℂ) * I * ((2 * π : ℝ) : ℂ)) = 1 := by
    have harg : (n : ℂ) * I * ((2 * π : ℝ) : ℂ) = (n : ℂ) * (2 * (π : ℂ) * I) := by push_cast; ring
    rw [harg]; simp
  simp only [Complex.ofReal_add, mul_add, Complex.exp_add, h1, mul_one]

/-- **Character orthogonality on the polar angle range `(−π, π)`** — the form the polar change of
variables (`Complex.integral_comp_polarCoord_symm`, whose `target` has `θ ∈ Ioo (−π) π`) consumes.
Same value as `charInt` by `2π`-periodicity. -/
lemma charInt_neg_pi_pi (n : ℤ) :
    (∫ θ in (-π : ℝ)..π, Complex.exp ((n : ℂ) * I * θ))
      = if n = 0 then (2 * π : ℂ) else 0 := by
  have hper := exp_char_periodic n
  have e1 : -π + 2 * π = π := by ring
  have e2 : (0 : ℝ) + 2 * π = 2 * π := by ring
  calc (∫ θ in (-π : ℝ)..π, Complex.exp ((n : ℂ) * I * θ))
      = ∫ θ in (-π : ℝ)..(-π + 2 * π), Complex.exp ((n : ℂ) * I * θ) := by rw [e1]
    _ = ∫ θ in (0 : ℝ)..(0 + 2 * π), Complex.exp ((n : ℂ) * I * θ) :=
          hper.intervalIntegral_add_eq (-π) 0
    _ = ∫ θ in (0 : ℝ)..(2 * π), Complex.exp ((n : ℂ) * I * θ) := by rw [e2]
    _ = if n = 0 then (2 * π : ℂ) else 0 := charInt n

/-! ### Polar-coordinate facts for the disk change of variables -/

/-- `Complex.polarCoord.symm (r, θ) = r · e^{iθ}`. -/
lemma polarCoord_symm_eq (r θ : ℝ) :
    Complex.polarCoord.symm (r, θ) = (r : ℂ) * Complex.exp ((θ : ℂ) * I) := by
  rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-- `‖r · e^{iθ}‖ = r` for `r ≥ 0`. -/
lemma norm_polarCoord_symm {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    ‖Complex.polarCoord.symm (r, θ)‖ = r := by
  rw [polarCoord_symm_eq, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one,
    Real.norm_of_nonneg hr]

/-- On the polar `target` (`r ≥ 0`), `r e^{iθ}` lies in the open unit disk iff `r < 1` — the
predicate the disk indicator turns into under the change of variables. -/
lemma polarCoord_symm_mem_disk_iff {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    Complex.polarCoord.symm (r, θ) ∈ Surface.disk ↔ r < 1 := by
  rw [Surface.disk, Metric.mem_ball, dist_zero_right, norm_polarCoord_symm hr]

/-- `potV` in polar coordinates depends only on `r = ‖·‖`: `potV k (r e^{iθ}) = Vrad k r`. -/
lemma potV_polarCoord_symm (k : ℕ) {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    Surface.potV k (Complex.polarCoord.symm (r, θ)) = Vrad k r := by
  rw [potV_eq_Vrad, norm_polarCoord_symm hr]

/-! ### The mode in polar coordinates -/

/-- **`modeU` in polar coordinates**: `modeU k ℓ (r e^{iθ}) = uRad k ℓ r · e^{iℓθ}` for `r ≥ 0`.
The radial profile `uRad = r^ℓ · gRad` is real; the angular part is the pure character `e^{iℓθ}`.
This is the ingredient that, under the polar change of variables, exposes the `e^{i(ℓ−ℓ')θ}` cross
factor for `charInt_neg_pi_pi` to annihilate. -/
lemma modeU_polarCoord_symm (k ℓ : ℕ) {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    modeU k ℓ (Complex.polarCoord.symm (r, θ))
      = (uRad k ℓ r : ℂ) * Complex.exp ((ℓ : ℂ) * ((θ : ℂ) * I)) := by
  rw [modeU, norm_polarCoord_symm hr, polarCoord_symm_eq, mul_pow, ← Complex.exp_nat_mul, uRad]
  push_cast; ring

/-! ### The disk integrand is separable in polar coordinates -/

/-- **The off-diagonal integrand factorizes** under the polar change of variables: at
`w = r e^{iθ}` (`r ≥ 0`), `V·conj(modeU_{ℓ'})·modeU_ℓ` splits into a real radial factor
`Vrad·uRad_{ℓ'}·uRad_ℓ` times the pure angular character `e^{i(ℓ−ℓ')θ}`.  The character is what
`charInt_neg_pi_pi` will integrate to `0` once Fubini separates the `r` and `θ` integrals. -/
lemma integrand_polar (k ℓ ℓ' : ℕ) {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    Surface.potV k (Complex.polarCoord.symm (r, θ)) *
        (starRingEnd ℂ) (modeU k ℓ' (Complex.polarCoord.symm (r, θ))) *
        modeU k ℓ (Complex.polarCoord.symm (r, θ))
      = ((Vrad k r * uRad k ℓ' r * uRad k ℓ r : ℝ) : ℂ) *
          Complex.exp (((ℓ : ℂ) - (ℓ' : ℂ)) * ((θ : ℂ) * I)) := by
  have hconj : (starRingEnd ℂ) ((ℓ' : ℂ) * ((θ : ℂ) * I)) = -((ℓ' : ℂ) * ((θ : ℂ) * I)) := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_natCast]; ring
  have hcombine : Complex.exp (((ℓ : ℂ) - (ℓ' : ℂ)) * ((θ : ℂ) * I))
      = Complex.exp (-((ℓ' : ℂ) * ((θ : ℂ) * I))) * Complex.exp ((ℓ : ℂ) * ((θ : ℂ) * I)) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [potV_polarCoord_symm k hr, modeU_polarCoord_symm k ℓ hr, modeU_polarCoord_symm k ℓ' hr,
    map_mul, Complex.conj_ofReal, ← Complex.exp_conj, hconj, hcombine]
  push_cast; ring

/-- The off-diagonal integrand `V·conj(modeU_{ℓ'})·modeU_ℓ` is integrable on the disk (continuous
on the compact closed disk).  The integrability hypothesis the polar change of variables / Fubini
step consumes. -/
lemma integrableOn_offdiag (hk : 2 ≤ k) (ℓ ℓ' : ℕ) :
    IntegrableOn
      (fun w => Surface.potV k w * (starRingEnd ℂ) (modeU k ℓ' w) * modeU k ℓ w) Surface.disk := by
  have hmodeU : ∀ j : ℕ, Continuous (modeU k j) := by
    intro j
    have h1 : Continuous (fun w : ℂ => (gRad k j ‖w‖ : ℂ)) :=
      Complex.continuous_ofReal.comp ((gRad_continuous hk j).comp continuous_norm)
    unfold modeU
    exact h1.mul (continuous_pow j)
  have hpotVr : Continuous (fun w : ℂ => Surface.potV k w) := by
    have heq : (fun w : ℂ => Surface.potV k w) = fun w : ℂ => Vrad k ‖w‖ := by
      funext w; exact potV_eq_Vrad k w
    rw [heq]; exact (continuous_Vrad k).comp continuous_norm
  have hpotV : Continuous (fun w : ℂ => (Surface.potV k w : ℂ)) :=
    Complex.continuous_ofReal.comp hpotVr
  have hcont : Continuous
      (fun w => Surface.potV k w * (starRingEnd ℂ) (modeU k ℓ' w) * modeU k ℓ w) :=
    (hpotV.mul (Complex.continuous_conj.comp (hmodeU ℓ'))).mul (hmodeU ℓ)
  exact (hcont.continuousOn.integrableOn_compact
    (ProperSpace.isCompact_closedBall (0 : ℂ) 1)).mono_set
    (by rw [Surface.disk]; exact Metric.ball_subset_closedBall)

/-! ### Rotation-equivariance and the disk off-diagonal orthogonality

The mode integrals decouple because the disk energy is *rotationally symmetric*.  Rotation by a
unit complex number `a` (`w ↦ a·w`) is a linear isometry of `ℂ`, hence volume-preserving and
disk-preserving; and each ingredient transforms by a pure character: `potV` is radial (invariant),
`modeU k ℓ (a·w) = aˡ · modeU k ℓ w`.  So the off-diagonal integrand picks up the scalar
`aˡ · conj(aˡ')`, and for `ℓ ≠ ℓ'` a suitable `a` makes that scalar `≠ 1`, forcing the integral to
vanish. The proof applies this rotation identity directly to the potential pairing. -/

/-- `potV` is rotation-invariant: `‖a‖ = 1 ⟹ potV k (a·w) = potV k w` (it depends only on `‖w‖`). -/
lemma potV_rotation (k : ℕ) {a : ℂ} (ha : ‖a‖ = 1) (w : ℂ) :
    Surface.potV k (a * w) = Surface.potV k w := by
  rw [potV_eq_Vrad, potV_eq_Vrad, norm_mul, ha, one_mul]

/-- Each mode transforms by a pure character under rotation:
`‖a‖ = 1 ⟹ modeU k ℓ (a·w) = aˡ · modeU k ℓ w`. -/
lemma modeU_rotation (k ℓ : ℕ) {a : ℂ} (ha : ‖a‖ = 1) (w : ℂ) :
    modeU k ℓ (a * w) = a ^ ℓ * modeU k ℓ w := by
  unfold modeU
  rw [norm_mul, ha, one_mul, mul_pow]; ring

/-- **Rotation vanishing on the disk.**  If an integrand `F` is rotation-equivariant with a
nontrivial scalar — `F (a·w) = c · F w` for a circle element `a`, with `c ≠ 1` — then its integral
over the (rotation-invariant) disk vanishes.  Proof: the rotation `w ↦ a·w` is a measure-preserving
self-map of `ℂ` fixing the disk, so `∫_disk F(a·w) = ∫_disk F`; equivariance turns the left side
into `c·∫_disk F`; hence `(c−1)∫_disk F = 0`. -/
lemma setIntegral_disk_eq_zero_of_rotation
    {F : ℂ → ℂ} {a : Circle} {c : ℂ} (hc : c ≠ 1)
    (hequiv : ∀ w, F ((a : ℂ) * w) = c * F w) :
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
      exact integral_congr_ae (ae_of_all _ fun w => (hequiv w).symm)
    rw [h1, hcov]
  have hsub : (c - 1) * ∫ w in Surface.disk, F w = 0 := by
    rw [sub_mul, one_mul, hkey, sub_self]
  rcases mul_eq_zero.mp hsub with h | h
  · exact absurd (sub_eq_zero.mp h) hc
  · exact h

/-- **The disk off-diagonal orthogonality (potential term).**  For `ℓ ≠ ℓ'`,
`∫_disk potV · conj(modeU ℓ') · modeU ℓ = 0`: the cross terms of the Jacobi energy of a mode sum
carry no potential contribution — the diagonalization over angular frequency.  Proved by rotational
symmetry, with `a = exp(iπ/(ℓ−ℓ'))` multiplying the integrand by `−1`. -/
lemma disk_offdiag_potV (k ℓ ℓ' : ℕ) (hne : ℓ ≠ ℓ') :
    ∫ w in Surface.disk,
      Surface.potV k w * (starRingEnd ℂ) (modeU k ℓ' w) * modeU k ℓ w = 0 := by
  set F : ℂ → ℂ :=
    fun w => Surface.potV k w * (starRingEnd ℂ) (modeU k ℓ' w) * modeU k ℓ w with hF
  have hden : (ℓ : ℝ) - (ℓ' : ℝ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  set θ₀ : ℝ := π / ((ℓ : ℝ) - (ℓ' : ℝ)) with hθ₀
  set a : Circle := Circle.exp θ₀ with ha
  have hanorm : ‖(a : ℂ)‖ = 1 := Circle.norm_coe a
  have hequiv : ∀ w, F ((a : ℂ) * w)
      = ((a : ℂ) ^ ℓ * (starRingEnd ℂ) ((a : ℂ) ^ ℓ')) * F w := by
    intro w
    simp only [hF]
    rw [potV_rotation k hanorm, modeU_rotation k ℓ hanorm, modeU_rotation k ℓ' hanorm, map_mul]
    ring
  have hreal : ((ℓ : ℝ) - (ℓ' : ℝ)) * θ₀ = π := by
    rw [hθ₀]; exact mul_div_cancel₀ π hden
  have hexp : (↑ℓ : ℂ) * ((θ₀ : ℂ) * I) + (starRingEnd ℂ) ((↑ℓ' : ℂ) * ((θ₀ : ℂ) * I))
      = (π : ℂ) * I := by
    have h2 : (↑ℓ : ℂ) * ((θ₀ : ℂ) * I) + (starRingEnd ℂ) ((↑ℓ' : ℂ) * ((θ₀ : ℂ) * I))
        = (((ℓ : ℝ) - (ℓ' : ℝ)) * θ₀ : ℝ) * I := by
      simp only [map_mul, map_natCast, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    rw [h2, hreal]
  have hscalar : (a : ℂ) ^ ℓ * (starRingEnd ℂ) ((a : ℂ) ^ ℓ') = -1 := by
    have hcoe : (a : ℂ) = Complex.exp ((θ₀ : ℂ) * I) := by rw [ha, Circle.coe_exp]
    rw [hcoe, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_conj, ← Complex.exp_add,
      hexp, Complex.exp_pi_mul_I]
  have hc_ne : (a : ℂ) ^ ℓ * (starRingEnd ℂ) ((a : ℂ) ^ ℓ') ≠ 1 := by
    rw [hscalar]; norm_num
  exact setIntegral_disk_eq_zero_of_rotation hc_ne hequiv

end KsIndex.ThetaOrtho
