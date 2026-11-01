module

public import KsIndexLean.KarcherGaussNormal
public import KsIndexLean.SphericalMetric

@[expose] public section


/-! Differential energy of the actual finite-chart EW unit normal.
Identification with the metric norm of the Hessian-defined II is separate. -/
noncomputable section
open scoped Topology
namespace KsIndex.KarcherData

/-- Normal in the existing Euclidean spherical carrier. -/
def gaussNormalEuclidean (k : ℕ) (w : ℂ) : Spherical.Ambient :=
  Spherical.stereoPoint (gauss k w)

lemma hasDerivAt_gauss {k : ℕ} (hk : 2 ≤ k) (w : ℂ) :
    HasDerivAt (gauss k) (((k : ℂ) - 1) * w ^ (k - 2)) w := by
  have he : k - 1 - 1 = k - 2 := by omega
  convert (hasDerivAt_id w).pow (k - 1) using 1 <;> first | rfl | simp [he, Nat.cast_sub (by omega : 1 ≤ k)]

lemma fderiv_gaussNormalEuclidean {k : ℕ} (hk : 2 ≤ k) (w d : ℂ) :
    fderiv ℝ (gaussNormalEuclidean k) w d =
      Spherical.stereoDifferential (gauss k w) (d * (((k : ℂ) - 1) * w ^ (k - 2))) := by
  have hg := (hasDerivAt_gauss hk w).hasFDerivAt.restrictScalars ℝ
  have hs := (Spherical.contDiff_stereoPoint.differentiable (by simp)).differentiableAt (x := gauss k w) |>.hasFDerivAt
  have he := (hs.comp w hg).fderiv
  change fderiv ℝ (Spherical.stereoPoint ∘ gauss k) w d = _
  rw [he, ContinuousLinearMap.comp_apply, Spherical.fderiv_stereoPoint_apply]
  rfl

lemma gaussNormalEuclidean_differentiableAt {k : ℕ} (hk : 2 ≤ k) (w : ℂ) :
    DifferentiableAt ℝ (gaussNormalEuclidean k) w :=
  (Spherical.contDiff_stereoPoint.differentiable (by simp)).differentiableAt.comp w
    ((hasDerivAt_gauss hk w).differentiableAt.restrictScalars ℝ)

/-- Euclidean energy of the Gauss map in the flat complex coordinate. -/
theorem gaussNormalEuclidean_energy {k : ℕ} (hk : 2 ≤ k) (w : ℂ) :
    ‖fderiv ℝ (gaussNormalEuclidean k) w 1‖ ^ 2 +
      ‖fderiv ℝ (gaussNormalEuclidean k) w Complex.I‖ ^ 2 = Surface.potV k w := by
  rw [fderiv_gaussNormalEuclidean hk, fderiv_gaussNormalEuclidean hk,
    Spherical.stereoDifferential_norm_sq, Spherical.stereoDifferential_norm_sq]
  have hc : ‖(k : ℂ) - 1‖ ^ 2 = ((k : ℝ) - 1) ^ 2 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have he : 2 * (k - 1) = 2 * k - 2 := by omega
  have he' : 2 * (k - 2) = 2 * k - 4 := by omega
  simp only [one_mul, norm_mul, Complex.norm_I, one_mul, mul_pow, hc,
    gauss, norm_pow, ← pow_mul]
  rw [Nat.mul_comm (k - 1) 2, he, Nat.mul_comm (k - 2) 2, he']
  unfold Surface.potV
  ring

/-- On an actual EW chart the derivative of the cross-product unit normal,
not merely that of a prescribed Gauss-map formula, has this energy. -/
theorem actual_normal_energy {k : ℕ} (hk : 2 ≤ k) {X : ℂ → AmbientTriple}
    {U : Set ℂ} (hU : IsOpen U)
    (havoid : ∀ z ∈ U, z ∉ Surface.punctures k)
    (hd : ∀ z ∈ U, HasFDerivAt X (ewRealDifferential k z) z)
    {w : ℂ} (hw : w ∈ U) :
    ‖fderiv ℝ (fun z => tripleToEuclidean (chartUnitNormal X z)) w 1‖ ^ 2 +
      ‖fderiv ℝ (fun z => tripleToEuclidean (chartUnitNormal X z)) w Complex.I‖ ^ 2 =
      Surface.potV k w := by
  have he : (fun z => tripleToEuclidean (chartUnitNormal X z)) =ᶠ[𝓝 w] gaussNormalEuclidean k := by
    filter_upwards [hU.mem_nhds hw] with z hz
    rw [ew_chartUnitNormal_eq_stereoNormal hk (havoid z hz) (hd z hz)]
    rfl
  rw [he.fderiv_eq, gaussNormalEuclidean_energy hk]

/-- Dividing the normal's flat-coordinate energy by the induced conformal
metric yields the square of the paper's prescribed curvature magnitude. -/
theorem actual_normal_metric_energy_eq_absA_sq {k : ℕ} (hk : 2 ≤ k)
    {X : ℂ → AmbientTriple} {U : Set ℂ} (hU : IsOpen U)
    (havoid : ∀ z ∈ U, z ∉ Surface.punctures k)
    (hd : ∀ z ∈ U, HasFDerivAt X (ewRealDifferential k z) z)
    {w : ℂ} (hw : w ∈ U) :
    (‖fderiv ℝ (fun z => tripleToEuclidean (chartUnitNormal X z)) w 1‖ ^ 2 +
      ‖fderiv ℝ (fun z => tripleToEuclidean (chartUnitNormal X z)) w Complex.I‖ ^ 2) /
      Surface.rho k w ^ 2 = Surface.absA k w ^ 2 := by
  rw [actual_normal_energy hk hU havoid hd hw]
  have he := Surface.potential_integrand hk (fun _ => (1 : ℂ)) (havoid w hw)
  simp only [norm_one, mul_one, one_pow] at he
  rw [← he]
  exact mul_div_cancel_right₀ _ (ne_of_gt (rho_sq_pos hk (havoid w hw)))

end KsIndex.KarcherData
