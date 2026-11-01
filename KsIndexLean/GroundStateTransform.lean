module

public import KsIndexLean.FiniteOrderGreen
public import KsIndexLean.ExplicitModeJacobi

@[expose] public section


/-! Ground-state identities for the disk Jacobi energy. The product formula
uses a real `C²` Jacobi field vanishing on the circle and a `C¹` multiplier;
positivity is needed only when dividing by the explicit radial field on the
support of a test function. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.GroundState
open KsIndex.Trace KsIndex.Surface KsIndex.GradOrtho

lemma product_energy_identity (a b z w : ℂ)
    (ha : (starRingEnd ℂ) a = a) (hb : (starRingEnd ℂ) b = b) :
    (starRingEnd ℂ) (b * z + a * w) * (b * z + a * w) =
      a ^ 2 * ((starRingEnd ℂ) w * w) +
        b * (b * (starRingEnd ℂ) z * z +
          a * (starRingEnd ℂ) w * z + a * (starRingEnd ℂ) z * w) := by
  simp only [map_add, map_mul, ha, hb]
  ring

lemma derivative_real {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℝ g z) (hr : ∀ w, (starRingEnd ℂ) (g w) = g w)
    (e : ℂ) : (starRingEnd ℂ) (fderiv ℝ g z e) = fderiv ℝ g z e := by
  have hf : (fun w => (starRingEnd ℂ) (g w)) = g := funext hr
  have h := KsIndex.FirstGreen.hasFDerivAt_conj hg
  rw [hf] at h
  have he := congrArg (fun L : ℂ →L[ℝ] ℂ => L e) h.fderiv
  exact he.symm

/-- Pointwise product identity before using the Jacobi equation or integrating. -/
lemma gradient_product_identity {g v : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℝ g z) (hv : DifferentiableAt ℝ v z)
    (hr : ∀ w, (starRingEnd ℂ) (g w) = g w) :
    gradInner (fun w => g w * v w) (fun w => g w * v w) z =
      g z ^ 2 * gradInner v v z +
        gradInner g (fun w => g w * (starRingEnd ℂ) (v w) * v w) z := by
  have hp := (hg.hasFDerivAt.mul hv.hasFDerivAt).fderiv
  have ht := ((hg.hasFDerivAt.mul (KsIndex.FirstGreen.hasFDerivAt_conj hv)).mul
    hv.hasFDerivAt).fderiv
  change fderiv ℝ (fun w => g w * v w) z = _ at hp
  change fderiv ℝ (fun w => g w * (starRingEnd ℂ) (v w) * v w) z = _ at ht
  simp only [gradInner, hp, ht, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    smul_eq_mul, Pi.mul_apply,
    map_add, map_mul, hr, derivative_real hg hr]
  ring

lemma continuous_gradInner {f h : ℂ → ℂ}
    (hf : ContDiff ℝ 1 f) (hh : ContDiff ℝ 1 h) : Continuous (gradInner f h) := by
  have df := hf.continuous_fderiv (by norm_num)
  have dh := hh.continuous_fderiv (by norm_num)
  exact (((df.clm_apply continuous_const).star).mul
    (dh.clm_apply continuous_const)).add
    (((df.clm_apply continuous_const).star).mul (dh.clm_apply continuous_const))

/-- Energy representation for a `C¹` multiple of a real `C²` Jacobi field
vanishing on the circle. The field need not be positive for this identity. -/
theorem disk_ground_state_identity (g v : ℂ → ℂ) (V : ℂ → ℝ)
    (hg : ContDiff ℝ 2 g) (hv : ContDiff ℝ 1 v)
    (hr : ∀ z, (starRingEnd ℂ) (g z) = g z)
    (hb : ∀ z : Circle₁, g z = 0)
    (he : ∀ z ∈ (WeakH1.disk : Set ℂ), laplacian g z + V z * g z = 0) :
    (∫ z in (WeakH1.disk : Set ℂ),
      gradInner (fun w => g w * v w) (fun w => g w * v w) z -
        V z * (starRingEnd ℂ) (g z * v z) * (g z * v z)) =
      ∫ z in (WeakH1.disk : Set ℂ), g z ^ 2 * gradInner v v z := by
  let t : ℂ → ℂ := fun z => g z * (starRingEnd ℂ) (v z) * v z
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have ht : ContDiff ℝ 1 t := (hg1.mul (Complex.conjCLE.contDiff.comp hv)).mul hv
  have hg0 := first_green_C2 g t hg ht
  have hb0 : (∫ z : Circle₁, (starRingEnd ℂ) (fderiv ℝ g z z) * t z ∂circleMeasure) = 0 := by
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall (fun z => by simp [t, hb z])
  rw [hb0] at hg0
  have hp (z : ℂ) (hz : z ∈ (WeakH1.disk : Set ℂ)) :
      gradInner (fun w => g w * v w) (fun w => g w * v w) z -
          V z * (starRingEnd ℂ) (g z * v z) * (g z * v z) =
        g z ^ 2 * gradInner v v z +
          (gradInner g t z + (starRingEnd ℂ) (laplacian g z) * t z) := by
    rw [gradient_product_identity (hg1.differentiable (by norm_num) z)
      (hv.differentiable (by norm_num) z) hr]
    have hl : laplacian g z = -(V z * g z) := eq_neg_of_add_eq_zero_left (he z hz)
    simp only [hl, map_neg, map_mul, Complex.conj_ofReal, hr, t]
    ring
  have hi (f : ℂ → ℂ) (hf : Continuous f) :
      IntegrableOn f (WeakH1.disk : Set ℂ) :=
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).mono_set
      Metric.ball_subset_closedBall
  have hbase : IntegrableOn (fun z => g z ^ 2 * gradInner v v z)
      (WeakH1.disk : Set ℂ) := hi _
    ((hg.continuous.pow 2).mul (continuous_gradInner hv hv))
  have hpartial (a : ℂ) : ContDiff ℝ 1 (fun z => fderiv ℝ g z a) :=
    (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hlap : Continuous (laplacian g) :=
    (((hpartial 1).continuous_fderiv (by norm_num)).clm_apply continuous_const).add
      (((hpartial Complex.I).continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hgreen : IntegrableOn
      (fun z => gradInner g t z + (starRingEnd ℂ) (laplacian g z) * t z)
      (WeakH1.disk : Set ℂ) :=
    hi _ ((continuous_gradInner hg1 ht).add (hlap.star.mul ht.continuous))
  calc
    _ = ∫ z in (WeakH1.disk : Set ℂ), g z ^ 2 * gradInner v v z +
        (gradInner g t z + (starRingEnd ℂ) (laplacian g z) * t z) := by
      apply setIntegral_congr_fun WeakH1.disk.isOpen.measurableSet
      exact hp
    _ = _ := by rw [integral_add hbase hgreen, hg0, add_zero]

/-- Real-valued energy representation for a `C¹` multiple of the real Jacobi field. -/
theorem disk_ground_state_energy (g v : ℂ → ℂ) (V : ℂ → ℝ)
    (hg : ContDiff ℝ 2 g) (hv : ContDiff ℝ 1 v)
    (hr : ∀ z, (starRingEnd ℂ) (g z) = g z)
    (hb : ∀ z : Circle₁, g z = 0)
    (he : ∀ z ∈ (WeakH1.disk : Set ℂ), laplacian g z + V z * g z = 0) :
    (∫ z in (WeakH1.disk : Set ℂ),
      gradSq (fun w => g w * v w) z - V z * ‖g z * v z‖ ^ 2) =
      ∫ z in (WeakH1.disk : Set ℂ), ‖g z‖ ^ 2 * gradSq v z := by
  have h := disk_ground_state_identity g v V hg hv hr hb he
  have hn (a : ℂ) : (starRingEnd ℂ) a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hs (z : ℂ) : g z ^ 2 = ((‖g z‖ ^ 2 : ℝ) : ℂ) := by
    calc
      _ = (starRingEnd ℂ) (g z) * g z := by rw [hr, pow_two]
      _ = _ := hn _
  simp only [gradInner_self, hs] at h
  have hp (z : ℂ) :
      (V z : ℂ) * (starRingEnd ℂ) (g z * v z) * (g z * v z) =
        ((V z * ‖g z * v z‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_assoc, hn, Complex.ofReal_mul]
  simp only [hp, ← Complex.ofReal_mul, ← Complex.ofReal_sub] at h
  rw [integral_complex_ofReal, integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

/-- `C¹` multiples of a real `C²` Jacobi field vanishing on the circle have
nonnegative Dirichlet Jacobi energy. -/
theorem disk_ground_state_nonnegative (g v : ℂ → ℂ) (V : ℂ → ℝ)
    (hg : ContDiff ℝ 2 g) (hv : ContDiff ℝ 1 v)
    (hr : ∀ z, (starRingEnd ℂ) (g z) = g z)
    (hb : ∀ z : Circle₁, g z = 0)
    (he : ∀ z ∈ (WeakH1.disk : Set ℂ), laplacian g z + V z * g z = 0) :
    0 ≤ ∫ z in (WeakH1.disk : Set ℂ),
      gradSq (fun w => g w * v w) z - V z * ‖g z * v z‖ ^ 2 := by
  rw [disk_ground_state_energy g v V hg hv hr hb he]
  apply integral_nonneg
  intro z
  exact mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The vertical radial Jacobi field has positive real value in the open disk. -/
lemma radial_ground_positive {k : ℕ} (hk : 2 ≤ k) {z : ℂ}
    (hz : z ∈ (WeakH1.disk : Set ℂ)) : 0 < (KsIndex.JacobiMode.modeU k 0 z).re := by
  simp only [KsIndex.JacobiMode.modeU, pow_zero, mul_one, Complex.ofReal_re]
  exact KsIndex.Radial.gRad_zero_pos hk (norm_nonneg z)
    (by change dist z 0 < 1 at hz; simpa only [dist_zero_right] using hz)

/-- Nonnegative energy of `C¹` multiples of the vertical radial Jacobi field. -/
theorem radial_ground_multiple_nonnegative {k : ℕ} (hk : 2 ≤ k)
    (v : ℂ → ℂ) (hv : ContDiff ℝ 1 v) :
    0 ≤ ∫ z in (WeakH1.disk : Set ℂ),
      gradSq (fun w => KsIndex.JacobiMode.modeU k 0 w * v w) z -
        potV k z * ‖KsIndex.JacobiMode.modeU k 0 z * v z‖ ^ 2 := by
  apply disk_ground_state_nonnegative _ v (potV k)
    ((KsIndex.ModeDiag.modeU_contDiff (by omega : 1 ≤ k) 0).of_le (by simp)) hv
  · intro z
    simp only [KsIndex.JacobiMode.modeU, pow_zero, mul_one, Complex.conj_ofReal]
  · intro z
    rw [KsIndex.JacobiMode.modeU, show ‖(z : ℂ)‖ = 1 by simp,
      KsIndex.Radial.gRad_zero_one hk]
    simp
  · intro z _
    exact modeU_jacobi hk 0 z

/-- Division of `C¹` functions remains `C¹` when the denominator is nonzero on the topological support;
its zeros elsewhere cause no singularity because the numerator vanishes locally. -/
lemma contDiff_div_of_nonzero_on_tsupport {f g : ℂ → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hne : ∀ z ∈ tsupport f, g z ≠ 0) : ContDiff ℝ 1 (fun z => f z / g z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport f
  · simpa only [div_eq_mul_inv] using
      hf.contDiffAt.mul (hg.contDiffAt.fun_inv (hne z hz))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with w hw
    simp only [Pi.zero_apply] at hw
    simp only [hw, zero_div]

/-- Multiplication recovers the original numerator even at zeros off its support. -/
lemma mul_div_eq_of_nonzero_on_tsupport {f g : ℂ → ℂ}
    (hne : ∀ z ∈ tsupport f, g z ≠ 0) :
    (fun z => g z * (f z / g z)) = f := by
  funext z
  by_cases hz : g z = 0
  · have hfz : f z = 0 := by
      by_contra hfz
      exact hne z (subset_tsupport f (Function.mem_support.mpr hfz)) hz
    simp only [hz, hfz, zero_div, mul_zero]
  · exact mul_div_cancel₀ (f z) hz

/-- The positive vertical field proves nonnegativity for every `C¹` test
whose topological support lies in the open disk. -/
theorem radial_ground_test_nonnegative {k : ℕ} (hk : 2 ≤ k)
    (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f)
    (hs : tsupport f ⊆ (WeakH1.disk : Set ℂ)) :
    0 ≤ ∫ z in (WeakH1.disk : Set ℂ), gradSq f z - potV k z * ‖f z‖ ^ 2 := by
  let g := KsIndex.JacobiMode.modeU k 0
  have hne : ∀ z ∈ tsupport f, g z ≠ 0 := by
    intro z hz he
    have hp := radial_ground_positive hk (hs hz)
    change 0 < (g z).re at hp
    rw [he] at hp
    exact (lt_irrefl 0) hp
  have hg : ContDiff ℝ 1 g :=
    (KsIndex.ModeDiag.modeU_contDiff (by omega : 1 ≤ k) 0).of_le (by simp)
  have h := radial_ground_multiple_nonnegative hk (fun z => f z / g z)
    (contDiff_div_of_nonzero_on_tsupport hf hg hne)
  change 0 ≤ ∫ z in (WeakH1.disk : Set ℂ),
    gradSq (fun w => g w * (f w / g w)) z - potV k z * ‖g z * (f z / g z)‖ ^ 2 at h
  have he := mul_div_eq_of_nonzero_on_tsupport hne
  simpa only [he, congrFun he] using h

end KsIndex.GroundState
