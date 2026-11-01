module

public import KsIndexLean.KarcherGaussNormal

@[expose] public section


/-! Differentiating normal-tangent orthogonality gives the Hessian definition
of the second fundamental form. -/
noncomputable section
open scoped ContDiff Topology
namespace KsIndex.KarcherData

/-- Coordinatewise expression for an actual directional derivative. -/
def coordinateTangent (X : ℂ → AmbientTriple) (w v : ℂ) : AmbientTriple :=
  (fderiv ℝ (fun z => (X z).1) w v,
   fderiv ℝ (fun z => (X z).2.1) w v,
   fderiv ℝ (fun z => (X z).2.2) w v)

lemma coordinateTangent_eq {X : ℂ → AmbientTriple} {w : ℂ}
    (h : DifferentiableAt ℝ X w) (v : ℂ) : coordinateTangent X w v = fderiv ℝ X w v := by
  simp [coordinateTangent, fderiv.fst h, fderiv.fst h.snd, fderiv.snd h.snd, fderiv.snd h]

lemma fderiv_normal_coordinate_pair {f n : ℂ → ℝ} {w : ℂ}
    (hf : ContDiffAt ℝ 2 f w) (hn : DifferentiableAt ℝ n w) (u v : ℂ) :
    fderiv ℝ (fun z => n z * fderiv ℝ f z v) w u =
      fderiv ℝ n w u * fderiv ℝ f w v + n w * bilinearIteratedFDerivTwo ℝ f w u v := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) w :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by simp)
  rw [fderiv_fun_mul hn (hdf.clm_apply (differentiableAt_const v)),
    fderiv_clm_apply hdf (differentiableAt_const v)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    add_apply, smul_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul]
  change n w * (fderiv ℝ (fderiv ℝ f) w u v) + fderiv ℝ f w v * fderiv ℝ n w u = _
  unfold bilinearIteratedFDerivTwo
  change _ = fderiv ℝ n w u * fderiv ℝ f w v + n w * (fderiv ℝ (fderiv ℝ f) w u v)
  ring

/-- Weingarten's identity with explicit hypotheses: the normal field is
 differentiable, agrees with the chosen normal, and is orthogonal locally.
 The conclusion uses the actual Hessian-defined second fundamental form. -/
theorem secondFundamentalForm_eq_neg_normal_derivative
    {X N : ℂ → AmbientTriple} {w : ℂ}
    (hX : ContDiffAt ℝ 2 X w) (hN : DifferentiableAt ℝ N w)
    (hNw : N w = chartUnitNormal X w) (u v : ℂ)
    (horth : ∀ᶠ z in 𝓝 w, euclideanDot (N z) (coordinateTangent X z v) = 0) :
    secondFundamentalForm X w u v = -euclideanDot (fderiv ℝ N w u) (fderiv ℝ X w v) := by
  have hx1 := hX.fst
  have hx2 := hX.snd.fst
  have hx3 := hX.snd.snd
  have ht (f : ℂ → ℝ) (hf : ContDiffAt ℝ 2 f w) :
      DifferentiableAt ℝ (fun z => fderiv ℝ f z v) w :=
    ((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
      (by simp)).clm_apply (differentiableAt_const v)
  have h1 := hN.fst.mul (ht _ hx1)
  have h2 := hN.snd.fst.mul (ht _ hx2)
  have h3 := hN.snd.snd.mul (ht _ hx3)
  have ho : (fun z => euclideanDot (N z) (coordinateTangent X z v)) =ᶠ[𝓝 w] (fun _ => (0 : ℝ)) := horth
  have he := congrArg (fun L : ℂ →L[ℝ] ℝ => L u) ho.fderiv_eq
  change fderiv ℝ (fun z =>
      (N z).1 * fderiv ℝ (fun z => (X z).1) z v +
      (N z).2.1 * fderiv ℝ (fun z => (X z).2.1) z v +
      (N z).2.2 * fderiv ℝ (fun z => (X z).2.2) z v) w u = _ at he
  have hsum : fderiv ℝ (fun z =>
      (N z).1 * fderiv ℝ (fun z => (X z).1) z v +
      (N z).2.1 * fderiv ℝ (fun z => (X z).2.1) z v +
      (N z).2.2 * fderiv ℝ (fun z => (X z).2.2) z v) w =
      fderiv ℝ (fun z => (N z).1 * fderiv ℝ (fun z => (X z).1) z v) w +
      fderiv ℝ (fun z => (N z).2.1 * fderiv ℝ (fun z => (X z).2.1) z v) w +
      fderiv ℝ (fun z => (N z).2.2 * fderiv ℝ (fun z => (X z).2.2) z v) w := by
    convert ((h1.hasFDerivAt.add h2.hasFDerivAt).add h3.hasFDerivAt).fderiv using 1 <;> rfl
  rw [hsum] at he
  simp only [add_apply, fderiv_const_apply, zero_apply] at he
  rw [fderiv_normal_coordinate_pair hx1 hN.fst,
    fderiv_normal_coordinate_pair hx2 hN.snd.fst,
    fderiv_normal_coordinate_pair hx3 hN.snd.snd] at he
  rw [← coordinateTangent_eq hN u, ← coordinateTangent_eq (hX.differentiableAt (by simp)) v]
  simp only [secondFundamentalForm, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    euclideanDot, coordinateTangent]
  rw [hNw] at he
  linarith

/-- Differentiating a unit normal keeps its derivative in the tangent plane. -/
lemma unit_normal_derivative_tangent {N : ℂ → AmbientTriple} {w : ℂ}
    (hN : DifferentiableAt ℝ N w)
    (hunit : ∀ᶠ z in 𝓝 w, euclideanSq (N z) = 1) (u : ℂ) :
    euclideanDot (N w) (fderiv ℝ N w u) = 0 := by
  have h1 := hN.fst.hasFDerivAt.mul hN.fst.hasFDerivAt
  have h2 := hN.snd.fst.hasFDerivAt.mul hN.snd.fst.hasFDerivAt
  have h3 := hN.snd.snd.hasFDerivAt.mul hN.snd.snd.hasFDerivAt
  have hsum := (h1.add h2 |>.add h3).fderiv
  have ho : (fun z => euclideanSq (N z)) =ᶠ[𝓝 w] (fun _ => (1 : ℝ)) := hunit
  have he := congrArg (fun L : ℂ →L[ℝ] ℝ => L u) ho.fderiv_eq
  have heq : (fun z => euclideanSq (N z)) = (fun z =>
      (N z).1 * (N z).1 + (N z).2.1 * (N z).2.1 + (N z).2.2 * (N z).2.2) := by
    funext z
    simp [euclideanSq, pow_two]
  rw [heq] at he
  have hs : fderiv ℝ (fun z =>
      (N z).1 * (N z).1 + (N z).2.1 * (N z).2.1 + (N z).2.2 * (N z).2.2) w =
      (N w).1 • fderiv ℝ (fun z => (N z).1) w + (N w).1 • fderiv ℝ (fun z => (N z).1) w +
      ((N w).2.1 • fderiv ℝ (fun z => (N z).2.1) w + (N w).2.1 • fderiv ℝ (fun z => (N z).2.1) w) +
      ((N w).2.2 • fderiv ℝ (fun z => (N z).2.2) w + (N w).2.2 • fderiv ℝ (fun z => (N z).2.2) w) := by
    convert hsum using 1
  rw [hs] at he
  simp only [add_apply, smul_apply, smul_eq_mul, fderiv_const_apply, zero_apply] at he
  rw [← coordinateTangent_eq hN u]
  unfold euclideanDot coordinateTangent
  linarith

lemma euclidean_gram_identity (a b t : AmbientTriple) :
    euclideanSq a * euclideanSq b * euclideanSq t -
      euclideanSq a * euclideanDot b t ^ 2 - euclideanSq b * euclideanDot a t ^ 2 -
      euclideanSq t * euclideanDot a b ^ 2 +
      2 * euclideanDot a b * euclideanDot a t * euclideanDot b t =
    euclideanDot (euclideanCross a b) t ^ 2 := by
  simp only [euclideanSq, euclideanDot, euclideanCross]
  ring

/-- Parseval's identity in a conformal tangent frame, without any product-norm
 substitution for Euclidean length. -/
lemma conformal_frame_parseval {a b t : AmbientTriple} {q : ℝ}
    (hq : 0 < q) (ha : euclideanSq a = q) (hb : euclideanSq b = q)
    (hab : euclideanDot a b = 0) (ht : euclideanDot (euclideanCross a b) t = 0) :
    euclideanDot t a ^ 2 + euclideanDot t b ^ 2 = q * euclideanSq t := by
  have he := euclidean_gram_identity a b t
  rw [ha, hb, hab, ht] at he
  have hz : q * (q * euclideanSq t - (euclideanDot a t ^ 2 + euclideanDot b t ^ 2)) = 0 := by
    nlinarith [he]
  have hc := (mul_eq_zero.mp hz).resolve_left hq.ne'
  have hs (x y : AmbientTriple) : euclideanDot x y = euclideanDot y x := by
    unfold euclideanDot
    ring
  rw [hs t a, hs t b]
  linarith

/-- Squared tensor norm in conformal coordinates with metric q times the
identity. Each of the two covariant indices contributes a factor q⁻¹. -/
def conformalSecondFundamentalNormSq (X : ℂ → AmbientTriple) (w : ℂ) (q : ℝ) : ℝ :=
  (secondFundamentalForm X w 1 1 ^ 2 + secondFundamentalForm X w 1 Complex.I ^ 2 +
   secondFundamentalForm X w Complex.I 1 ^ 2 +
   secondFundamentalForm X w Complex.I Complex.I ^ 2) / q ^ 2

/-- The norm of the Hessian-normal tensor is the metric energy of the normal.
All geometric assumptions are explicit; no curvature formula is assumed. -/
theorem conformalSecondFundamentalNormSq_eq_normal_energy
    {X N : ℂ → AmbientTriple} {w : ℂ} {q : ℝ}
    (hX : ContDiffAt ℝ 2 X w) (hN : DifferentiableAt ℝ N w)
    (hNw : N w = chartUnitNormal X w) (hq : 0 < q)
    (hm : ∀ d : ℂ, euclideanSq (fderiv ℝ X w d) = q * ‖d‖ ^ 2)
    (hunit : ∀ᶠ z in 𝓝 w, euclideanSq (N z) = 1)
    (horth : ∀ v : ℂ, ∀ᶠ z in 𝓝 w,
      euclideanDot (N z) (coordinateTangent X z v) = 0) :
    conformalSecondFundamentalNormSq X w q =
      (euclideanSq (fderiv ℝ N w 1) + euclideanSq (fderiv ℝ N w Complex.I)) / q := by
  have ha : euclideanSq (fderiv ℝ X w 1) = q := by simpa using hm 1
  have hb : euclideanSq (fderiv ℝ X w Complex.I) = q := by simpa using hm Complex.I
  obtain ⟨_, hab, _⟩ := metric_coefficients_of_conformal hm
  have ht (u : ℂ) : euclideanDot
      (euclideanCross (fderiv ℝ X w 1) (fderiv ℝ X w Complex.I)) (fderiv ℝ N w u) = 0 := by
    have he := unit_normal_derivative_tangent hN hunit u
    rw [hNw, chartUnitNormal_eq_inv_conformal hq hm, euclideanDot_smul_left] at he
    exact (mul_eq_zero.mp he).resolve_left (inv_ne_zero hq.ne')
  have hp (u : ℂ) := conformal_frame_parseval hq ha hb hab (ht u)
  have hwg (u v : ℂ) :=
    secondFundamentalForm_eq_neg_normal_derivative hX hN hNw u v (horth v)
  unfold conformalSecondFundamentalNormSq
  rw [hwg 1 1, hwg 1 Complex.I, hwg Complex.I 1, hwg Complex.I Complex.I]
  simp only [neg_sq]
  rw [show ∀ a b c d : ℝ, a + b + c + d = (a + b) + (c + d) by intros; ring,
    hp 1, hp Complex.I]
  field_simp

end KsIndex.KarcherData
