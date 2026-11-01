module

public import KsIndexLean.KarcherNormalEnergy
public import KsIndexLean.KarcherWeingarten

@[expose] public section


/-! Curvature magnitude of actual finite-chart EW representatives, derived
from their Hessian-defined second fundamental form. -/
noncomputable section
open scoped ContDiff Topology
namespace KsIndex.KarcherData

/-- Change of carrier only: the triple is still measured with Euclidean length. -/
def tripleEuclideanCLM : AmbientTriple →L[ℝ] Spherical.Ambient :=
  LinearMap.toContinuousLinearMap {
    toFun := tripleToEuclidean
    map_add' := by intros a b; ext i; fin_cases i <;> rfl
    map_smul' := by intros c a; ext i; fin_cases i <;> rfl }

lemma tripleToEuclidean_norm_sq (p : AmbientTriple) :
    ‖tripleToEuclidean p‖ ^ 2 = euclideanSq p := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [tripleToEuclidean, euclideanSq, Fin.sum_univ_three]

lemma normal_derivative_euclidean_sq {N : ℂ → AmbientTriple} {w : ℂ}
    (hN : DifferentiableAt ℝ N w) (u : ℂ) :
    ‖fderiv ℝ (fun z => tripleToEuclidean (N z)) w u‖ ^ 2 =
      euclideanSq (fderiv ℝ N w u) := by
  have he := (tripleEuclideanCLM.hasFDerivAt.comp w hN.hasFDerivAt).fderiv
  change ‖fderiv ℝ (tripleEuclideanCLM ∘ N) w u‖ ^ 2 = _
  rw [he, ContinuousLinearMap.comp_apply]
  exact tripleToEuclidean_norm_sq _

lemma differentiable_stereoNormal : Differentiable ℝ stereoNormal := by
  have hr : Differentiable ℝ (fun z : ℂ => z.re) := Complex.reCLM.differentiable
  have hi : Differentiable ℝ (fun z : ℂ => z.im) := Complex.imCLM.differentiable
  have hn := (hr.pow 2).add (hi.pow 2)
  have hd := (differentiable_const (𝕜 := ℝ) (1 : ℝ)).add hn
  have hne (z : ℂ) : 1 + (z.re ^ 2 + z.im ^ 2) ≠ 0 := by positivity
  have h1 := ((differentiable_const (𝕜 := ℝ) (2 : ℝ)).mul hr).mul (hd.inv hne)
  have h2 := ((differentiable_const (𝕜 := ℝ) (2 : ℝ)).mul hi).mul (hd.inv hne)
  have h3 := (hn.sub (differentiable_const (𝕜 := ℝ) (1 : ℝ))).mul (hd.inv hne)
  convert h1.prodMk (h2.prodMk h3) using 1 <;> first
  | rfl
  | funext z
    unfold stereoNormal
    simp only [Complex.sq_norm, Complex.normSq_apply]
    simp [pow_two, div_eq_mul_inv]

lemma ew_chartUnitNormal_differentiableAt {k : ℕ} (hk : 2 ≤ k)
    {X : ℂ → AmbientTriple} {U : Set ℂ} (hU : IsOpen U)
    (havoid : ∀ z ∈ U, z ∉ Surface.punctures k)
    (hd : ∀ z ∈ U, HasFDerivAt X (ewRealDifferential k z) z)
    {w : ℂ} (hw : w ∈ U) : DifferentiableAt ℝ (chartUnitNormal X) w := by
  have he : chartUnitNormal X =ᶠ[𝓝 w] (fun z => stereoNormal (gauss k z)) := by
    filter_upwards [hU.mem_nhds hw] with z hz
    exact ew_chartUnitNormal_eq_stereoNormal hk (havoid z hz) (hd z hz)
  exact (differentiable_stereoNormal.differentiableAt.comp w
    ((hasDerivAt_gauss hk w).differentiableAt.restrictScalars ℝ)).congr_of_eventuallyEq he

lemma normal_orthogonal_all {D : ℂ →L[ℝ] AmbientTriple} {n : AmbientTriple}
    (h1 : euclideanDot n (D 1) = 0) (hi : euclideanDot n (D Complex.I) = 0) (v : ℂ) :
    euclideanDot n (D v) = 0 := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [hv, map_add, map_smul, map_smul]
  have he (a b : AmbientTriple) (r s : ℝ) : euclideanDot n (r • a + s • b) =
      r * euclideanDot n a + s * euclideanDot n b := by
    simp [euclideanDot, smul_eq_mul]
    ring
  rw [he, h1, hi]
  ring

/-- The square of the prescribed scalar absA equals the squared metric
norm of the actual second fundamental form, on every C² EW chart. -/
theorem ew_secondFundamentalNormSq_eq_absA_sq {k : ℕ} (hk : 2 ≤ k)
    {X : ℂ → AmbientTriple} {U : Set ℂ} (hU : IsOpen U)
    (havoid : ∀ z ∈ U, z ∉ Surface.punctures k)
    (hd : ∀ z ∈ U, HasFDerivAt X (ewRealDifferential k z) z)
    {w : ℂ} (hw : w ∈ U) (hX : ContDiffAt ℝ 2 X w) :
    conformalSecondFundamentalNormSq X w (Surface.rho k w ^ 2) = Surface.absA k w ^ 2 := by
  have hN := ew_chartUnitNormal_differentiableAt hk hU havoid hd hw
  have hm (d : ℂ) : euclideanSq (fderiv ℝ X w d) = Surface.rho k w ^ 2 * ‖d‖ ^ 2 := by
    rw [(hd w hw).fderiv, ewRealDifferential_metric hk]
  have hu : ∀ᶠ z in 𝓝 w, euclideanSq (chartUnitNormal X z) = 1 := by
    filter_upwards [hU.mem_nhds hw] with z hz
    exact (ew_chartUnitNormal_spec hk (havoid z hz) (hd z hz)).1
  have ho (v : ℂ) : ∀ᶠ z in 𝓝 w,
      euclideanDot (chartUnitNormal X z) (coordinateTangent X z v) = 0 := by
    filter_upwards [hU.mem_nhds hw] with z hz
    rw [coordinateTangent_eq (hd z hz).differentiableAt]
    obtain ⟨_, h1, hi⟩ := ew_chartUnitNormal_spec hk (havoid z hz) (hd z hz)
    exact normal_orthogonal_all h1 hi v
  rw [conformalSecondFundamentalNormSq_eq_normal_energy hX hN rfl
    (rho_sq_pos hk (havoid w hw)) hm hu ho]
  rw [← normal_derivative_euclidean_sq hN 1, ← normal_derivative_euclidean_sq hN Complex.I]
  exact actual_normal_metric_energy_eq_absA_sq hk hU havoid hd hw

/-- Length of the second fundamental form in the positive conformal metric. -/
def conformalSecondFundamentalNorm (X : ℂ → AmbientTriple) (w : ℂ) (q : ℝ) : ℝ :=
  Real.sqrt (conformalSecondFundamentalNormSq X w q)

/-- The paper's explicit curvature magnitude equals the geometric norm of II. -/
theorem ew_secondFundamentalNorm_eq_absA {k : ℕ} (hk : 2 ≤ k)
    {X : ℂ → AmbientTriple} {U : Set ℂ} (hU : IsOpen U)
    (havoid : ∀ z ∈ U, z ∉ Surface.punctures k)
    (hd : ∀ z ∈ U, HasFDerivAt X (ewRealDifferential k z) z)
    {w : ℂ} (hw : w ∈ U) (hX : ContDiffAt ℝ 2 X w) :
    conformalSecondFundamentalNorm X w (Surface.rho k w ^ 2) = Surface.absA k w := by
  unfold conformalSecondFundamentalNorm
  rw [ew_secondFundamentalNormSq_eq_absA_sq hk hU havoid hd hw hX]
  apply Real.sqrt_sq
  have hr := Surface.rho_pos (by omega : 1 ≤ k) (havoid w hw)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  unfold Surface.absA
  positivity

end KsIndex.KarcherData
