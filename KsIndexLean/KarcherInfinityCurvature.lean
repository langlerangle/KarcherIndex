module

public import KsIndexLean.KarcherCurvature

@[expose] public section


/-! The curvature calculation extends over the regular infinity-chart center. -/
noncomputable section
open scoped ContDiff Topology
namespace KsIndex.KarcherData

def normalHalfTurnCLM : AmbientTriple →L[ℝ] AmbientTriple :=
  LinearMap.toContinuousLinearMap {
    toFun := normalHalfTurn
    map_add' := by intros a b; ext <;> simp [normalHalfTurn, add_comm]
    map_smul' := by intros c a; exact normalHalfTurn_smul c a }

lemma normalHalfTurn_euclideanSq (p : AmbientTriple) :
    euclideanSq (normalHalfTurn p) = euclideanSq p := by
  simp [euclideanSq, normalHalfTurn]

lemma stereoGauss_differentiableAt {k : ℕ} (hk : 2 ≤ k) (w : ℂ) :
    DifferentiableAt ℝ (fun z => stereoNormal (gauss k z)) w :=
  differentiable_stereoNormal.differentiableAt.comp w
    ((hasDerivAt_gauss hk w).differentiableAt.restrictScalars ℝ)

lemma infinity_chartUnitNormal_eventuallyEq {k : ℕ} (hk : 2 ≤ k)
    {X : ℂ → AmbientTriple} {U : Set ℂ} (hU : IsOpen U)
    (havoid : ∀ z ∈ U, z ∉ Surface.punctures k)
    (hd : ∀ z ∈ U, HasFDerivAt X (infinityRealDifferential k z) z)
    {w : ℂ} (hw : w ∈ U) :
    chartUnitNormal X =ᶠ[𝓝 w] normalHalfTurnCLM ∘ (fun z => stereoNormal (gauss k z)) := by
  filter_upwards [hU.mem_nhds hw] with z hz
  exact infinity_chartUnitNormal_eq hk (havoid z hz) (hd z hz)

lemma infinity_chartUnitNormal_differentiableAt {k : ℕ} (hk : 2 ≤ k)
    {X : ℂ → AmbientTriple} {U : Set ℂ} (hU : IsOpen U)
    (havoid : ∀ z ∈ U, z ∉ Surface.punctures k)
    (hd : ∀ z ∈ U, HasFDerivAt X (infinityRealDifferential k z) z)
    {w : ℂ} (hw : w ∈ U) : DifferentiableAt ℝ (chartUnitNormal X) w :=
  (normalHalfTurnCLM.differentiableAt.comp w (stereoGauss_differentiableAt hk w)).congr_of_eventuallyEq
    (infinity_chartUnitNormal_eventuallyEq hk hU havoid hd hw)

/-- Normal energy in the infinity chart, valid also at its center. -/
theorem infinity_normal_energy {k : ℕ} (hk : 2 ≤ k)
    {X : ℂ → AmbientTriple} {U : Set ℂ} (hU : IsOpen U)
    (havoid : ∀ z ∈ U, z ∉ Surface.punctures k)
    (hd : ∀ z ∈ U, HasFDerivAt X (infinityRealDifferential k z) z)
    {w : ℂ} (hw : w ∈ U) :
    euclideanSq (fderiv ℝ (chartUnitNormal X) w 1) +
      euclideanSq (fderiv ℝ (chartUnitNormal X) w Complex.I) = Surface.potV k w := by
  rw [(infinity_chartUnitNormal_eventuallyEq hk hU havoid hd hw).fderiv_eq]
  rw [(normalHalfTurnCLM.hasFDerivAt.comp w (stereoGauss_differentiableAt hk w).hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  change euclideanSq (normalHalfTurn _) + euclideanSq (normalHalfTurn _) = _
  rw [normalHalfTurn_euclideanSq, normalHalfTurn_euclideanSq,
    ← normal_derivative_euclidean_sq (stereoGauss_differentiableAt hk w) 1,
    ← normal_derivative_euclidean_sq (stereoGauss_differentiableAt hk w) Complex.I]
  exact gaussNormalEuclidean_energy hk w

/-- The Hessian-defined II has the stated metric norm at every infinity-chart
point, with no nonzero-coordinate hypothesis. -/
theorem infinity_secondFundamentalNormSq_eq_absA_sq {k : ℕ} (hk : 2 ≤ k)
    {X : ℂ → AmbientTriple} {U : Set ℂ} (hU : IsOpen U)
    (havoid : ∀ z ∈ U, z ∉ Surface.punctures k)
    (hd : ∀ z ∈ U, HasFDerivAt X (infinityRealDifferential k z) z)
    {w : ℂ} (hw : w ∈ U) (hX : ContDiffAt ℝ 2 X w) :
    conformalSecondFundamentalNormSq X w (Surface.rho k w ^ 2) = Surface.absA k w ^ 2 := by
  have hN := infinity_chartUnitNormal_differentiableAt hk hU havoid hd hw
  have hm (d : ℂ) : euclideanSq (fderiv ℝ X w d) = Surface.rho k w ^ 2 * ‖d‖ ^ 2 := by
    rw [(hd w hw).fderiv, infinityRealDifferential_metric hk]
  have hu : ∀ᶠ z in 𝓝 w, euclideanSq (chartUnitNormal X z) = 1 := by
    filter_upwards [hU.mem_nhds hw] with z hz
    exact (infinity_chartUnitNormal_spec hk (havoid z hz) (hd z hz)).1
  have ho (v : ℂ) : ∀ᶠ z in 𝓝 w,
      euclideanDot (chartUnitNormal X z) (coordinateTangent X z v) = 0 := by
    filter_upwards [hU.mem_nhds hw] with z hz
    rw [coordinateTangent_eq (hd z hz).differentiableAt]
    obtain ⟨_, h1, hi⟩ := infinity_chartUnitNormal_spec hk (havoid z hz) (hd z hz)
    exact normal_orthogonal_all h1 hi v
  rw [conformalSecondFundamentalNormSq_eq_normal_energy hX hN rfl
    (rho_sq_pos hk (havoid w hw)) hm hu ho, infinity_normal_energy hk hU havoid hd hw]
  have he := Surface.potential_integrand hk (fun _ => (1 : ℂ)) (havoid w hw)
  simp only [norm_one, mul_one, one_pow] at he
  rw [← he]
  exact mul_div_cancel_right₀ _ (ne_of_gt (rho_sq_pos hk (havoid w hw)))

theorem infinity_secondFundamentalNorm_eq_absA {k : ℕ} (hk : 2 ≤ k)
    {X : ℂ → AmbientTriple} {U : Set ℂ} (hU : IsOpen U)
    (havoid : ∀ z ∈ U, z ∉ Surface.punctures k)
    (hd : ∀ z ∈ U, HasFDerivAt X (infinityRealDifferential k z) z)
    {w : ℂ} (hw : w ∈ U) (hX : ContDiffAt ℝ 2 X w) :
    conformalSecondFundamentalNorm X w (Surface.rho k w ^ 2) = Surface.absA k w := by
  unfold conformalSecondFundamentalNorm
  rw [infinity_secondFundamentalNormSq_eq_absA_sq hk hU havoid hd hw hX]
  apply Real.sqrt_sq
  have hr := Surface.rho_pos (by omega : 1 ≤ k) (havoid w hw)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  unfold Surface.absA
  positivity

/-- Scalar curvature magnitude is invariant under the inversion transition. -/
lemma absA_inv {k : ℕ} (hk : 2 ≤ k) {v : ℂ} (hv : v ≠ 0)
    (hp : v ∉ Surface.punctures k) : Surface.absA k v⁻¹ = Surface.absA k v := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hden : ‖v ^ (2 * k) + 1‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    intro he
    apply hp
    change v ^ (2 * k) = -1
    exact eq_neg_of_add_eq_zero_left he
  have he : v⁻¹ ^ (2 * k) + 1 = (v ^ (2 * k) + 1) / v ^ (2 * k) := by
    rw [inv_pow]
    field_simp
    ring
  unfold Surface.absA Surface.rho
  rw [he, norm_div, norm_pow]
  simp only [norm_inv, inv_pow]
  rw [pow_sub₀ ‖v‖ hn (by omega : 2 ≤ 2 * k), pow_sub₀ ‖v‖ hn hk]
  rw [show 2 * k = k * 2 by omega, pow_mul]
  have hsum : ‖v‖ ^ k ^ 2 + ‖v‖ ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- Curvature magnitudes from the actual two representatives agree on overlap. -/
theorem secondFundamentalNorm_overlap {k : ℕ} (hk : 2 ≤ k)
    {X Y : ℂ → AmbientTriple} {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (ha : ∀ z ∈ U, z ∉ Surface.punctures k) (hb : ∀ z ∈ V, z ∉ Surface.punctures k)
    (hd : ∀ z ∈ U, HasFDerivAt X (ewRealDifferential k z) z)
    (he : ∀ z ∈ V, HasFDerivAt Y (infinityRealDifferential k z) z)
    {v : ℂ} (hv : v ≠ 0) (hvU : v⁻¹ ∈ U) (hvV : v ∈ V)
    (hX : ContDiffAt ℝ 2 X v⁻¹) (hY : ContDiffAt ℝ 2 Y v) :
    conformalSecondFundamentalNorm X v⁻¹ (Surface.rho k v⁻¹ ^ 2) =
      conformalSecondFundamentalNorm Y v (Surface.rho k v ^ 2) := by
  rw [ew_secondFundamentalNorm_eq_absA hk hU ha hd hvU hX,
    infinity_secondFundamentalNorm_eq_absA hk hV hb he hvV hY, absA_inv hk hv (hb v hvV)]

/-- An actual integrated infinity chart carries the full local curvature
identification all the way through its center; no chart existence is assumed. -/
theorem exists_curvature_infinity_chart {k : ℕ} (hk : 2 ≤ k)
    (b : PuncturedPlane k) :
    ∃ r : ℝ, ∃ _hr0 : 0 < r, ∃ hr1 : r < 1,
    ∃ X : ℂ → AmbientTriple, ∃ C : PeriodTarget,
      X 0 = 0 ∧ ContDiffOn ℝ ∞ X (Metric.ball (0 : ℂ) r) ∧
      HarmonicCoordinates X (Metric.ball (0 : ℂ) r) ∧
      (∀ v ∈ Metric.ball (0 : ℂ) r, HasFDerivAt X (infinityRealDifferential k v) v) ∧
      (∀ v ∈ Metric.ball (0 : ℂ) r, Function.Injective (infinityRealDifferential k v)) ∧
      (∀ v : infinityOverlap r,
        descendedIntegral hk b (infinityOverlapPoint hk hr1.le v) = C + projectPeriod (X v.val)) ∧
      (∀ v ∈ Metric.ball (0 : ℂ) r, euclideanSq (chartUnitNormal X v) = 1 ∧
        chartMeanCurvature X v = 0 ∧
        conformalSecondFundamentalNorm X v (Surface.rho k v ^ 2) = Surface.absA k v) := by
  obtain ⟨r, hr0, hr1, X, C, hz, hs, hh, hd, hi, he, hf⟩ :=
    exists_zero_mean_curvature_infinity_chart hk b
  refine ⟨r, hr0, hr1, X, C, hz, hs, hh, hd, hi, he, ?_⟩
  intro v hv
  refine ⟨(hf v hv).1, (hf v hv).2, ?_⟩
  have ha : ∀ z ∈ Metric.ball (0 : ℂ) r, z ∉ Surface.punctures k := by
    intro z hz
    exact not_puncture_of_norm_lt_one hk ((by simpa using hz : ‖z‖ < r).trans hr1)
  have hC : ContDiffAt ℝ 2 X v :=
    (hs.contDiffAt (Metric.isOpen_ball.mem_nhds hv)).of_le (by simp)
  exact infinity_secondFundamentalNorm_eq_absA hk Metric.isOpen_ball ha hd hv hC

end KsIndex.KarcherData
