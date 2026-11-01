module

public import KsIndexLean.DiskTraceAgreement
public import KsIndexLean.PunctureRemoval
public import KsIndexLean.WeakH1Integration
public import KsIndexLean.SurfacePotentialFacts
public import KsIndexLean.GeneralDiskClassical
public import KsIndexLean.WeakSmoothGluing

@[expose] public section


/-! # Real tests for the weak Jacobi equation

Smooth compactly supported real functions embed into `ComplexH1` by
complexification. When their closed support lies in the open disk, their disk
and arc traces vanish. A zero weak Jacobi pairing with such a real test gives
the corresponding real and imaginary integral equations.

These local test constructions supply the interior regularity arguments without
depending on the slit index or ground-state kernel conclusions. -/
noncomputable section
open MeasureTheory TopologicalSpace Topology
open scoped ContDiff
namespace KsIndex.PaperSlitTransport
open KsIndex.Trace KsIndex.WeakH1

/-! ### Embedding a real test -/

/-- The `SmoothH1Data` of a smooth compactly supported real function,
complexified and restricted to the disk. Interior support is required only for the trace lemmas. -/
def realTestData (ψ : ℂ → ℝ) (hψs : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) : SmoothH1Data where
  F := fun z => (ψ z : ℂ)
  smooth := (Complex.ofRealCLM.contDiff.comp hψs).contDiffOn
  value_mem := ((Complex.ofRealCLM.continuous.comp
    hψs.continuous).memLp_of_hasCompactSupport
      (hψc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp))).restrict _
  dx_mem := by
    have hcont : Continuous fun x => fderiv ℝ (fun z => (ψ z : ℂ)) x 1 :=
      ((Complex.ofRealCLM.contDiff.comp hψs).continuous_fderiv
        (by simp)).clm_apply continuous_const
    have hcs : HasCompactSupport fun x => fderiv ℝ (fun z => (ψ z : ℂ)) x 1 := by
      apply ((hψc.comp_left (g := fun t : ℝ => (t : ℂ))
        (by simp)).fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℂ => L 1)
      simp
    exact (hcont.memLp_of_hasCompactSupport hcs).restrict _
  dy_mem := by
    have hcont : Continuous fun x => fderiv ℝ (fun z => (ψ z : ℂ)) x Complex.I :=
      ((Complex.ofRealCLM.contDiff.comp hψs).continuous_fderiv
        (by simp)).clm_apply continuous_const
    have hcs : HasCompactSupport
        fun x => fderiv ℝ (fun z => (ψ z : ℂ)) x Complex.I := by
      apply ((hψc.comp_left (g := fun t : ℝ => (t : ℂ))
        (by simp)).fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℂ => L Complex.I)
      simp
    exact (hcont.memLp_of_hasCompactSupport hcs).restrict _

/-- The embedded smooth compactly supported real test. -/
def realTestH1 (ψ : ℂ → ℝ) (hψs : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) : ComplexH1 :=
  smoothToH1 (realTestData ψ hψs hψc)

/-- Interior support kills the boundary trace. -/
lemma diskTrace_realTestH1 (ψ : ℂ → ℝ) (hψs : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ (disk : Set ℂ)) :
    diskTraceCLM (realTestH1 ψ hψs hψc) = 0 := by
  have hzero : ∀ w : Circle₁, (realTestData ψ hψs hψc).F (w : ℂ) = 0 := by
    intro w
    have hw : (w : ℂ) ∉ tsupport ψ := by
      intro hmem
      have h2 : (w : ℂ) ∈ Metric.ball (0 : ℂ) 1 := hsupp hmem
      rw [Metric.mem_ball, dist_zero_right] at h2
      have hnorm : ‖(w : ℂ)‖ = 1 := by
        exact mem_sphere_zero_iff_norm.mp w.property
      rw [hnorm] at h2
      exact lt_irrefl _ h2
    simp [realTestData, image_eq_zero_of_notMem_tsupport hw]
  have hcont : ContinuousOn (realTestData ψ hψs hψc).F annulus :=
    (Complex.ofRealCLM.continuous.comp hψs.continuous).continuousOn
  have hae := diskTrace_smooth_agreement (realTestData ψ hψs hψc) hcont
  have h0 : (diskTraceCLM (smoothToH1 (realTestData ψ hψs hψc)) : Circle₁ → ℂ)
      =ᵐ[circleMeasure] (0 : Circle₁ → ℂ) := by
    filter_upwards [hae] with w hw
    rw [hw, hzero w]
    rfl
  exact MeasureTheory.Lp.ext (h0.trans (MeasureTheory.Lp.coeFn_zero _ _ _).symm)

/-- Zero `arcTrace` on every arc (the trace factors through the restriction). -/
lemma arcTrace_realTestH1 (A : Set Circle₁) (ψ : ℂ → ℝ)
    (hψs : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ (disk : Set ℂ)) :
    arcTrace A (realTestH1 ψ hψs hψc) = 0 := by
  unfold arcTrace
  rw [ContinuousLinearMap.comp_apply, diskTrace_realTestH1 ψ hψs hψc hsupp,
    map_zero]

/-- The complexified test's derivative is the cast of the real derivative. -/
lemma fderiv_ofReal_apply {φ : ℂ → ℝ} (hφs : ContDiff ℝ (⊤ : ℕ∞) φ)
    (x v : ℂ) :
    fderiv ℝ (fun z => (φ z : ℂ)) x v = ((fderiv ℝ φ x v : ℝ) : ℂ) := by
  have h := (Complex.ofRealCLM.hasFDerivAt.comp x
    ((hφs.differentiable (by simp)).differentiableAt.hasFDerivAt)).fderiv
  rw [show (fun z => (φ z : ℂ)) = Complex.ofRealCLM ∘ φ from rfl, h]
  rfl

/-- A vanishing pairing with a real interior test gives both real weak equations. -/
theorem realTest_pairing_zero_components (k : ℕ) (u : ComplexH1)
    (φ : ℂ → ℝ) (hφs : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hT : weakJacobi (surfacePotential k) u (realTestH1 φ hφs hφc) = 0) :
    (∫ x in (disk : Set ℂ),
        ((TauCeti.W1p.gradient (rePart u) x).re * fderiv ℝ φ x 1
          + (TauCeti.W1p.gradient (rePart u) x).im * fderiv ℝ φ x Complex.I
          - Surface.potV k x * TauCeti.W1p.value (rePart u) x * φ x)) = 0
    ∧ (∫ x in (disk : Set ℂ),
        ((TauCeti.W1p.gradient (imPart u) x).re * fderiv ℝ φ x 1
          + (TauCeti.W1p.gradient (imPart u) x).im * fderiv ℝ φ x Complex.I
          - Surface.potV k x * TauCeti.W1p.value (imPart u) x * φ x)) = 0 := by
  unfold realTestH1 at hT
  set w := u with hwdef
  -- the six representatives
  have hexp := weakJacobi_integral_representatives (surfacePotential k) w
    (smoothToH1 (realTestData φ hφs hφc))
    (f := value w) (g := fun x => (φ x : ℂ))
    (a := fun x => ((TauCeti.W1p.gradient (rePart w) x).re : ℂ)
      + Complex.I * ((TauCeti.W1p.gradient (imPart w) x).re : ℂ))
    (b := fun x => ((TauCeti.W1p.gradient (rePart w) x).im : ℂ)
      + Complex.I * ((TauCeti.W1p.gradient (imPart w) x).im : ℂ))
    (c := fun x => ((fderiv ℝ φ x 1 : ℝ) : ℂ))
    (d := fun x => ((fderiv ℝ φ x Complex.I : ℝ) : ℂ))
    (valueLp_ae w)
    (by
      filter_upwards [smoothToH1_value_ae (realTestData φ hφs hφc)] with x hx
      exact hx)
    (dxLp_ae w) (dyLp_ae w)
    (by
      filter_upwards [smoothToH1_dx_ae (realTestData φ hφs hφc)] with x hx
      rw [hx]
      exact fderiv_ofReal_apply hφs x 1)
    (by
      filter_upwards [smoothToH1_dy_ae (realTestData φ hφs hφc)] with x hx
      rw [hx]
      exact fderiv_ofReal_apply hφs x Complex.I)
  rw [hT] at hexp
  -- integrability of the two complex integrands (congr from the CLM versions)
  have hgradInt : MeasureTheory.Integrable (fun x =>
      (starRingEnd ℂ) (((TauCeti.W1p.gradient (rePart w) x).re : ℂ)
          + Complex.I * ((TauCeti.W1p.gradient (imPart w) x).re : ℂ))
        * ((fderiv ℝ φ x 1 : ℝ) : ℂ)
      + (starRingEnd ℂ) (((TauCeti.W1p.gradient (rePart w) x).im : ℂ)
          + Complex.I * ((TauCeti.W1p.gradient (imPart w) x).im : ℂ))
        * ((fderiv ℝ φ x Complex.I : ℝ) : ℂ))
      (volume.restrict (disk : Set ℂ)) := by
    apply (dirichlet_integrable w (smoothToH1 (realTestData φ hφs hφc))).congr
    filter_upwards [dxLp_ae w, dyLp_ae w,
      smoothToH1_dx_ae (realTestData φ hφs hφc),
      smoothToH1_dy_ae (realTestData φ hφs hφc)] with x h1 h2 h3 h4
    have e1 : (dxCLM w : ℂ → ℂ) x
        = ((TauCeti.W1p.gradient (rePart w) x).re : ℂ)
          + Complex.I * ((TauCeti.W1p.gradient (imPart w) x).re : ℂ) := h1
    have e2 : (dyCLM w : ℂ → ℂ) x
        = ((TauCeti.W1p.gradient (rePart w) x).im : ℂ)
          + Complex.I * ((TauCeti.W1p.gradient (imPart w) x).im : ℂ) := h2
    have e5 : fderiv ℝ (realTestData φ hφs hφc).F x 1
        = ((fderiv ℝ φ x 1 : ℝ) : ℂ) := fderiv_ofReal_apply hφs x 1
    have e6 : fderiv ℝ (realTestData φ hφs hφc).F x Complex.I
        = ((fderiv ℝ φ x Complex.I : ℝ) : ℂ) :=
      fderiv_ofReal_apply hφs x Complex.I
    rw [e1, e2, h3, h4, e5, e6]
  have hpotInt : MeasureTheory.Integrable (fun x =>
      ((surfacePotential k).V x : ℂ) * (starRingEnd ℂ) (value w x)
        * ((φ x : ℝ) : ℂ))
      (volume.restrict (disk : Set ℂ)) := by
    apply (potential_integrable (surfacePotential k) w
      (smoothToH1 (realTestData φ hφs hφc))).congr
    filter_upwards [valueLp_ae w,
      smoothToH1_value_ae (realTestData φ hφs hφc)] with x h1 h2
    have e0 : (valueCLM w : ℂ → ℂ) x = value w x := h1
    rw [e0, h2]
    rfl
  -- The four real integrands and their integrability on the disk.
  have hE1int : MeasureTheory.Integrable (fun x =>
      (TauCeti.W1p.gradient (rePart w) x).re * fderiv ℝ φ x 1
        + (TauCeti.W1p.gradient (rePart w) x).im * fderiv ℝ φ x Complex.I)
      (volume.restrict (disk : Set ℂ)) :=
    ((KsIndex.PunctureRemoval.memLp_gradient_re (rePart w)).integrable_mul
      (KsIndex.PunctureRemoval.memLp_fderiv_test hφs hφc 1)).add
    ((KsIndex.PunctureRemoval.memLp_gradient_im (rePart w)).integrable_mul
      (KsIndex.PunctureRemoval.memLp_fderiv_test hφs hφc Complex.I))
  have hE2int : MeasureTheory.Integrable (fun x =>
      (TauCeti.W1p.gradient (imPart w) x).re * fderiv ℝ φ x 1
        + (TauCeti.W1p.gradient (imPart w) x).im * fderiv ℝ φ x Complex.I)
      (volume.restrict (disk : Set ℂ)) :=
    ((KsIndex.PunctureRemoval.memLp_gradient_re (imPart w)).integrable_mul
      (KsIndex.PunctureRemoval.memLp_fderiv_test hφs hφc 1)).add
    ((KsIndex.PunctureRemoval.memLp_gradient_im (imPart w)).integrable_mul
      (KsIndex.PunctureRemoval.memLp_fderiv_test hφs hφc Complex.I))
  have hφ2 : MeasureTheory.MemLp φ 2
      ((volume : Measure ℂ).restrict (disk : Set ℂ)) :=
    (hφs.continuous.memLp_of_hasCompactSupport hφc).restrict _
  have hvφ : ∀ p : RealH1, MeasureTheory.Integrable
      (fun x => TauCeti.W1p.value p x * φ x)
      (volume.restrict (disk : Set ℂ)) := fun p =>
    (MeasureTheory.Lp.memLp (TauCeti.W1p.value p)).integrable_mul hφ2
  have hPint : ∀ p : RealH1, MeasureTheory.Integrable
      (fun x => Surface.potV k x * TauCeti.W1p.value p x * φ x)
      (volume.restrict (disk : Set ℂ)) := by
    intro p
    apply MeasureTheory.Integrable.mono' (((hvφ p).abs).const_mul (8 * ((k:ℝ) - 1) ^ 2))
      (((SurfaceForm.continuous_potV k).aestronglyMeasurable).mul
        (hvφ p).aestronglyMeasurable |>.congr ?_)
    · filter_upwards [(surfacePotential k).bound] with x hx
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |Surface.potV k x| * |TauCeti.W1p.value p x| * |φ x|
          ≤ 8 * ((k:ℝ) - 1) ^ 2 * |TauCeti.W1p.value p x| * |φ x| := by
            apply mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hx (abs_nonneg _)) (abs_nonneg _)
        _ = 8 * ((k:ℝ) - 1) ^ 2 * (|TauCeti.W1p.value p x * φ x|) := by
            rw [abs_mul]; ring
    · filter_upwards with x
      simp only [Pi.mul_apply]
      ring
  -- the complex integrands split as cast-combinations
  have hgptw : ∀ x : ℂ,
      (starRingEnd ℂ) (((TauCeti.W1p.gradient (rePart w) x).re : ℂ)
          + Complex.I * ((TauCeti.W1p.gradient (imPart w) x).re : ℂ))
        * ((fderiv ℝ φ x 1 : ℝ) : ℂ)
      + (starRingEnd ℂ) (((TauCeti.W1p.gradient (rePart w) x).im : ℂ)
          + Complex.I * ((TauCeti.W1p.gradient (imPart w) x).im : ℂ))
        * ((fderiv ℝ φ x Complex.I : ℝ) : ℂ)
      = ((((TauCeti.W1p.gradient (rePart w) x).re * fderiv ℝ φ x 1
          + (TauCeti.W1p.gradient (rePart w) x).im * fderiv ℝ φ x Complex.I : ℝ)) : ℂ)
        - Complex.I * ((((TauCeti.W1p.gradient (imPart w) x).re * fderiv ℝ φ x 1
          + (TauCeti.W1p.gradient (imPart w) x).im * fderiv ℝ φ x Complex.I : ℝ)) : ℂ) := by
    intro x
    simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  have hpptw : ∀ x : ℂ,
      ((surfacePotential k).V x : ℂ) * (starRingEnd ℂ) (value w x) * ((φ x : ℝ) : ℂ)
      = (((Surface.potV k x * TauCeti.W1p.value (rePart w) x * φ x : ℝ)) : ℂ)
        - Complex.I * (((Surface.potV k x * TauCeti.W1p.value (imPart w) x * φ x : ℝ)) : ℂ) := by
    intro x
    change ((Surface.potV k x : ℝ) : ℂ) * (starRingEnd ℂ) (value w x) * _ = _
    rw [value]
    simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hgptw),
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpptw)] at hexp
  -- re/im exchange on the two cast-combination integrals (forward, no rw-at)
  have hgcomboInt : MeasureTheory.Integrable (fun x =>
      ((((TauCeti.W1p.gradient (rePart w) x).re * fderiv ℝ φ x 1
        + (TauCeti.W1p.gradient (rePart w) x).im * fderiv ℝ φ x Complex.I : ℝ)) : ℂ)
      - Complex.I * ((((TauCeti.W1p.gradient (imPart w) x).re * fderiv ℝ φ x 1
        + (TauCeti.W1p.gradient (imPart w) x).im * fderiv ℝ φ x Complex.I : ℝ)) : ℂ))
      (volume.restrict (disk : Set ℂ)) :=
    (hE1int.ofReal).sub ((hE2int.ofReal).const_mul Complex.I)
  have hpcomboInt : MeasureTheory.Integrable (fun x =>
      (((Surface.potV k x * TauCeti.W1p.value (rePart w) x * φ x : ℝ)) : ℂ)
      - Complex.I * (((Surface.potV k x * TauCeti.W1p.value (imPart w) x * φ x : ℝ)) : ℂ))
      (volume.restrict (disk : Set ℂ)) :=
    ((hPint (rePart w)).ofReal).sub (((hPint (imPart w)).ofReal).const_mul Complex.I)
  have hre := congrArg Complex.re hexp
  have him := congrArg Complex.im hexp
  have hgr := integral_re hgcomboInt
  have hgi := integral_im hgcomboInt
  have hpr := integral_re hpcomboInt
  have hpi := integral_im hpcomboInt
  simp only [RCLike.re_to_complex, RCLike.im_to_complex] at hgr hgi hpr hpi
  rw [Complex.sub_re, Complex.zero_re, ← hgr, ← hpr] at hre
  rw [Complex.sub_im, Complex.zero_im, ← hgi, ← hpi] at him
  have hgre : (∫ x in (disk : Set ℂ),
      (((((TauCeti.W1p.gradient (rePart w) x).re * fderiv ℝ φ x 1
        + (TauCeti.W1p.gradient (rePart w) x).im * fderiv ℝ φ x Complex.I : ℝ)) : ℂ)
      - Complex.I * ((((TauCeti.W1p.gradient (imPart w) x).re * fderiv ℝ φ x 1
        + (TauCeti.W1p.gradient (imPart w) x).im * fderiv ℝ φ x Complex.I : ℝ)) : ℂ)).re)
      = ∫ x in (disk : Set ℂ),
        ((TauCeti.W1p.gradient (rePart w) x).re * fderiv ℝ φ x 1
          + (TauCeti.W1p.gradient (rePart w) x).im * fderiv ℝ φ x Complex.I) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by simp)
  have hgim : (∫ x in (disk : Set ℂ),
      (((((TauCeti.W1p.gradient (rePart w) x).re * fderiv ℝ φ x 1
        + (TauCeti.W1p.gradient (rePart w) x).im * fderiv ℝ φ x Complex.I : ℝ)) : ℂ)
      - Complex.I * ((((TauCeti.W1p.gradient (imPart w) x).re * fderiv ℝ φ x 1
        + (TauCeti.W1p.gradient (imPart w) x).im * fderiv ℝ φ x Complex.I : ℝ)) : ℂ)).im)
      = ∫ x in (disk : Set ℂ),
        -((TauCeti.W1p.gradient (imPart w) x).re * fderiv ℝ φ x 1
          + (TauCeti.W1p.gradient (imPart w) x).im * fderiv ℝ φ x Complex.I) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by simp)
  have hpre : (∫ x in (disk : Set ℂ),
      ((((Surface.potV k x * TauCeti.W1p.value (rePart w) x * φ x : ℝ)) : ℂ)
      - Complex.I * (((Surface.potV k x * TauCeti.W1p.value (imPart w) x * φ x : ℝ)) : ℂ)).re)
      = ∫ x in (disk : Set ℂ),
        (Surface.potV k x * TauCeti.W1p.value (rePart w) x * φ x) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by simp)
  have hpim : (∫ x in (disk : Set ℂ),
      ((((Surface.potV k x * TauCeti.W1p.value (rePart w) x * φ x : ℝ)) : ℂ)
      - Complex.I * (((Surface.potV k x * TauCeti.W1p.value (imPart w) x * φ x : ℝ)) : ℂ)).im)
      = ∫ x in (disk : Set ℂ),
        -(Surface.potV k x * TauCeti.W1p.value (imPart w) x * φ x) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by simp)
  rw [hgre, hpre] at hre
  rw [hgim, hpim] at him
  rw [MeasureTheory.integral_neg, MeasureTheory.integral_neg] at him
  constructor
  · rw [MeasureTheory.integral_sub hE1int (hPint (rePart w))]
    linarith
  · rw [MeasureTheory.integral_sub hE2int (hPint (imPart w))]
    linarith

end KsIndex.PaperSlitTransport
