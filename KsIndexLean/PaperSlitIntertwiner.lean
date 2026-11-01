module

/-
# Fourier coefficients of the circle sign multiplier

Multiplication by the square wave `sgn(cos 3θ)` defines a bounded operator on
circle `L²`. This module identifies its Fourier coefficients with convolution
by the square wave's coefficient sequence, for every `L²` input and every
integer output mode.

The proof computes the coefficients on individual Fourier modes, then extends
by continuity of two coefficient functionals and the `ℓ²` Fourier expansion.
The convolution functional is an inner product against a reflected, conjugated
square-summable coefficient sequence. No pointwise convergence of a Fourier
series is required.

`PaperSlitSectorConnection` specializes this identity to the frequency class
`1+3ℤ`, identifies the sector sign operator, and retains the scalar `exp(iπα)`
in the phased seam multiplier. Half-order graph-domain and index/nullity
transport are separate from the `L²` identity proved here.

The square-wave coefficient and dilation suppliers are in
`SquareWaveCoefficients` and `SquareWaveDilation`, with Aristotle-assisted
proofs. The physical-to-coefficient construction was developed by Kai in
collaboration with Astra.
-/
public import KsIndexLean.CircleMeasure
public import KsIndexLean.CircleParseval
public import KsIndexLean.SquareWaveCoefficients
public import KsIndexLean.SquareWaveDilation
public import KsIndexLean.CircleFourierRotation
public import KsIndexLean.FourierEigenTests
public import KsIndexLean.AngularFourierIdentity
public import Mathlib.Analysis.InnerProductSpace.l2Space

@[expose] public section


noncomputable section
open MeasureTheory
open scoped Real
namespace KsIndex.Trace
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-! ### The physical square-wave multiplier -/

/-- The square-wave multiplier: `+1` when `Re(w³) ≥ 0`, and `−1` otherwise.
In particular its chosen value at the six zeroes is `+1`; it agrees with
`sgn(cos 3θ)` away from those endpoints. -/
def sigmaField : Circle₁ → ℂ := fun w => if 0 ≤ ((w : ℂ) ^ 3).re then 1 else -1

lemma continuous_cube_re : Continuous (fun w : Circle₁ => ((w : ℂ) ^ 3).re) :=
  Complex.continuous_re.comp ((continuous_pow 3).comp continuous_subtype_val)

lemma measurable_sigmaField : Measurable sigmaField := by
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le measurable_const continuous_cube_re.measurable

lemma norm_sigmaField_le_one (w : Circle₁) : ‖sigmaField w‖ ≤ 1 := by
  unfold sigmaField
  split <;> simp

/-- `(circleParam θ)³` has real part `cos 3θ` (since `circleParam θ = e^{iθ}`). -/
lemma cube_circleParam_re (θ : ℝ) : ((circleParam θ : ℂ) ^ 3).re = Real.cos (3 * θ) := by
  rw [circleParam_coe, ← Complex.exp_nat_mul,
    show ((3 : ℕ) : ℂ) * (↑θ * Complex.I) = ↑(3 * θ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re]

/-- The angular pullback of `sigmaField` is the square wave `sgn(cos 3θ)` — the bridge from the
abstract circle multiplier to the `θ`-integral computations (via `circleFourierCoeff`). -/
@[simp] lemma sigmaField_circleParam (θ : ℝ) :
    sigmaField (circleParam θ) = if 0 ≤ Real.cos (3 * θ) then (1 : ℂ) else -1 := by
  unfold sigmaField
  rw [cube_circleParam_re]

/-! ### The bounded multiplication operator

The discontinuous multiplier is measurable and has norm at most one. These
properties suffice to construct `sigmaMulCLM` on circle `L²`; no continuity
of the multiplier or boundedness on a Sobolev space is asserted here. -/

lemma memLp_sigmaMul (F : Lp ℂ 2 circleMeasure) :
    MemLp (fun w => sigmaField w • F w) 2 circleMeasure := by
  apply (Lp.memLp F).of_le_mul (c := 1)
    (measurable_sigmaField.aestronglyMeasurable.smul (Lp.aestronglyMeasurable F))
  exact Filter.Eventually.of_forall fun w => by
    change ‖sigmaField w • (F : Circle₁ → ℂ) w‖ ≤ 1 * ‖(F : Circle₁ → ℂ) w‖
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (norm_sigmaField_le_one w) (norm_nonneg _)

/-- Multiplication by `sigmaField` on `L²(circle)`. -/
def sigmaMul (F : Lp ℂ 2 circleMeasure) : Lp ℂ 2 circleMeasure :=
  (memLp_sigmaMul F).toLp (fun w => sigmaField w • F w)

lemma sigmaMul_coe (F : Lp ℂ 2 circleMeasure) :
    sigmaMul F =ᵐ[circleMeasure] fun w => sigmaField w • F w :=
  (memLp_sigmaMul F).coeFn_toLp

lemma sigmaMul_add (F G : Lp ℂ 2 circleMeasure) :
    sigmaMul (F + G) = sigmaMul F + sigmaMul G := by
  apply Lp.ext
  filter_upwards [sigmaMul_coe (F + G), sigmaMul_coe F, sigmaMul_coe G,
    Lp.coeFn_add F G, Lp.coeFn_add (sigmaMul F) (sigmaMul G)] with w h hF hG ha hb
  simp only [Pi.add_apply] at ha hb
  rw [h, hb, hF, hG, ha, smul_add]

lemma sigmaMul_smul (c : ℂ) (F : Lp ℂ 2 circleMeasure) :
    sigmaMul (c • F) = c • sigmaMul F := by
  apply Lp.ext
  filter_upwards [sigmaMul_coe (c • F), sigmaMul_coe F,
    Lp.coeFn_smul c F, Lp.coeFn_smul c (sigmaMul F)] with w h hF ha hb
  simp only [Pi.smul_apply] at ha hb
  rw [h, hb, hF, ha, smul_comm]

lemma norm_sigmaMul_le (F : Lp ℂ 2 circleMeasure) : ‖sigmaMul F‖ ≤ 1 * ‖F‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [sigmaMul_coe F] with w hw
  rw [hw, norm_smul]
  exact mul_le_mul_of_nonneg_right (norm_sigmaField_le_one w) (norm_nonneg _)

/-- The bounded `L²` multiplier `f ↦ sigmaField·f` (operator norm `≤ 1`). -/
def sigmaMulCLM : Lp ℂ 2 circleMeasure →L[ℂ] Lp ℂ 2 circleMeasure :=
  LinearMap.mkContinuous
    { toFun := sigmaMul
      map_add' := sigmaMul_add
      map_smul' := sigmaMul_smul }
    1 norm_sigmaMul_le

/-! ### Angular pullback of the square wave

`circleFourierCoeff sigmaField` is the Mathlib `fourierCoeffOn` of `sgn(cos 3θ)` (via the pullback
`sigmaField_circleParam`); the `φ=3θ` dilation then reduces it to the base square-wave coefficients
`squareWave_fourierCoeffOn_odd/even` (Aristotle, `SquareWaveCoefficients`): nonzero only at
`d = 3·odd`, where it equals `(2/π)(-1)^k/(2k+1)`. -/

/-- `sigmaField`'s physical Fourier coefficient as the Mathlib `fourierCoeffOn` of `sgn(cos 3θ)`. -/
lemma circleFourierCoeff_sigmaField (d : ℤ) :
    circleFourierCoeff sigmaField d
      = fourierCoeffOn Real.two_pi_pos
          (fun θ : ℝ => if 0 ≤ Real.cos (3 * θ) then (1 : ℂ) else -1) d := by
  simp only [circleFourierCoeff, sigmaField_circleParam]

/-! ### Fourier modulation

Multiplication by Fourier mode `n` shifts the coefficient index from `m` to
`m-n`. The geometric-circle identity follows by angular pullback and gives
the coefficient formula for the product of the square wave with one mode. -/

/-- AddCircle modulation: multiplying by mode `n` shifts the Fourier index by `-n`. -/
theorem fourierCoeff_mul_fourier (f : AddCircle (2 * Real.pi) → ℂ) (n m : ℤ) :
    fourierCoeff (fun x => fourier n x * f x) m = fourierCoeff f (m - n) := by
  have he : ∀ x : AddCircle (2 * Real.pi),
      fourier (-m) x * (fourier n x * f x) = fourier (-(m - n)) x * f x := by
    intro x
    rw [← mul_assoc, ← fourier_add, show (-m + n : ℤ) = -(m - n) by ring]
  simp only [fourierCoeff, smul_eq_mul]
  simp_rw [he]

/-- Geometric modulation: multiplying by `fourierAmbient n` (`= z^n = e^{inθ}`) shifts the physical
Fourier coefficient index by `-n`. -/
theorem circleFourierCoeff_fourierAmbient_mul (f : Circle₁ → ℂ) (n m : ℤ) :
    circleFourierCoeff (fun w => fourierAmbient n w * f w) m = circleFourierCoeff f (m - n) := by
  rw [← fourierCoeff_geometric_pullback, ← fourierCoeff_geometric_pullback f]
  have he : ∀ x : AddCircle (2 * Real.pi),
      fourierAmbient n (fourierCircleHomeomorph x) = fourier n x := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H y => rw [fourierCircleHomeomorph_coe, fourierAmbient_circleParam]
  simp_rw [he]
  exact fourierCoeff_mul_fourier (fun x => f (fourierCircleHomeomorph x)) n m

/-! ### Explicit square-wave coefficients

Combining `circleFourierCoeff_sigmaField` (connection), the dilation (`SquareWaveDilation`), and the
base coefficients (`SquareWaveCoefficients`): `circleFourierCoeff sigmaField` is
`(2/π)(-1)^k/(2k+1)` at the cross-half differences `6k+3`, and `0` at within-half `6k` and off-class
`3∤d`. This is
exactly the sector half-swap `ς` kernel (`chat`) on the class lattice `{6n+1}`/`{6m+4}`. -/

open Real in
/-- Cross-half coefficient (`d = 6k+3 = 3·(2k+1)`): the `chat` value `(2/π)(-1)^k/(2k+1)`. -/
lemma circleFourierCoeff_sigmaField_six_add_three (k : ℤ) :
    circleFourierCoeff sigmaField (6 * k + 3)
      = ((2 / π * (-1) ^ k / (2 * (k : ℝ) + 1) : ℝ) : ℂ) := by
  rw [circleFourierCoeff_sigmaField, show (6 * k + 3 : ℤ) = 3 * (2 * k + 1) by ring,
    sgnCos3_fourierCoeffOn_mul_three, squareWave_fourierCoeffOn_odd]

/-- Within-half coefficient (`d = 6k = 3·(2k)`): vanishes. -/
lemma circleFourierCoeff_sigmaField_six_mul (k : ℤ) :
    circleFourierCoeff sigmaField (6 * k) = 0 := by
  rw [circleFourierCoeff_sigmaField, show (6 * k : ℤ) = 3 * (2 * k) by ring,
    sgnCos3_fourierCoeffOn_mul_three, squareWave_fourierCoeffOn_even]

/-- Off the class (`3 ∤ d`): vanishes. -/
lemma circleFourierCoeff_sigmaField_not_dvd (d : ℤ) (hd : ¬ (3 : ℤ) ∣ d) :
    circleFourierCoeff sigmaField d = 0 := by
  rw [circleFourierCoeff_sigmaField, sgnCos3_fourierCoeffOn_not_dvd d hd]

/-! ### Multiplication of one Fourier mode -/

/-- Multiplying the mode `fourierTestLp n` by `sigmaField` shifts the Fourier index by `-n`
by modulation and the almost-everywhere representatives. This is the
single-mode identity used in the density argument. -/
lemma circleFourierCoeff_sigmaMul_fourierTestLp (n m : ℤ) :
    circleFourierCoeff (sigmaMul (fourierTestLp n)) m = circleFourierCoeff sigmaField (m - n) := by
  rw [congrFun (circleFourierCoeff_congr_ae (sigmaMul_coe (fourierTestLp n))) m]
  have hae : (fun w => sigmaField w • ((fourierTestLp n : Circle₁ → ℂ) w))
      =ᵐ[circleMeasure] (fun w => fourierAmbient n w * sigmaField w) := by
    filter_upwards [fourierTestLp_coe n] with w hw
    rw [hw, smul_eq_mul, mul_comm]
  rw [congrFun (circleFourierCoeff_congr_ae hae) m, circleFourierCoeff_fourierAmbient_mul]

/-! ### Extension to arbitrary L² inputs

The physical coefficient functional and the convolution coefficient functional
are continuous linear maps. The latter is represented by `innerSL` against
`sigmaKernelSeq`. Agreement on the Fourier modes extends to all `L²` inputs
using `lp.hasSum_single` and uniqueness of sums. The sector connection uses
this identity together with the explicit square-wave coefficients.
-/

/-- Coefficient of the unit mode `fourierTestLp n` (self-contained, via the geometric pullback). -/
lemma circleFourierCoeff_fourierTestLp (n e : ℤ) :
    circleFourierCoeff (fourierTestLp n) e = (Pi.single n 1 : ℤ → ℂ) e := by
  rw [congrFun (circleFourierCoeff_congr_ae (fourierTestLp_coe n)) e,
    ← fourierCoeff_geometric_pullback]
  have he : (fun x : AddCircle (2 * Real.pi) => fourierAmbient n (fourierCircleHomeomorph x))
      = fourier n := by
    funext x
    induction x using QuotientAddGroup.induction_on with
    | H y => rw [fourierCircleHomeomorph_coe, fourierAmbient_circleParam]
  rw [he, fourierCoeff_fourier]

/-- `circleFourierCLE (fourierTestLp n)` is the single ℓ² sequence `lp.single 2 n 1`. -/
lemma circleFourierCLE_fourierTestLp (n : ℤ) :
    circleFourierCLE (fourierTestLp n) = lp.single 2 n (1 : ℂ) := by
  ext e
  rw [circleFourierCLE_apply, circleFourierCoeff_fourierTestLp, lp.coeFn_single]

/-- `sigmaField` is bounded (`‖·‖ ≤ 1`) measurable on a finite measure, hence in `L²`. -/
lemma memLp_sigmaField : MemLp sigmaField 2 circleMeasure :=
  MemLp.of_bound measurable_sigmaField.aestronglyMeasurable 1
    (Filter.Eventually.of_forall norm_sigmaField_le_one)

/-- `sigmaField`'s `L²` representative. -/
def sigmaFieldLp : Lp ℂ 2 circleMeasure := memLp_sigmaField.toLp sigmaField

lemma circleFourierCoeff_sigmaFieldLp (e : ℤ) :
    circleFourierCoeff sigmaFieldLp e = circleFourierCoeff sigmaField e :=
  congrFun (circleFourierCoeff_congr_ae memLp_sigmaField.coeFn_toLp) e

/-- The reflected-conjugated coefficient sequence of `sigmaField`, as an ℓ² element:
`d ↦ conj (ĉ (m − d))`.  Its `ℓ²`-membership is a reindexing of `sigmaField ∈ L²` through the
involution `d ↦ m − d`. -/
def sigmaKernelSeq (m : ℤ) : lp (fun _ : ℤ => ℂ) 2 :=
  ⟨fun d => (starRingEnd ℂ) (circleFourierCoeff sigmaField (m - d)), by
    apply memℓp_gen
    have hp : (0 : ℝ) < (2 : ENNReal).toReal := by rw [ENNReal.toReal_ofNat]; norm_num
    have hmem : Memℓp (fun e : ℤ => circleFourierCoeff sigmaField e) 2 := by
      have := (circleFourierCLE sigmaFieldLp).property
      have hcoe : (⇑(circleFourierCLE sigmaFieldLp) : ℤ → ℂ)
          = fun e => circleFourierCoeff sigmaField e := by
        funext e; rw [circleFourierCLE_apply, circleFourierCoeff_sigmaFieldLp]
      rwa [hcoe] at this
    have hbase := hmem.summable hp
    have hinj : Function.Injective (fun d : ℤ => m - d) := by
      intro a b h; dsimp only at h; omega
    refine (hbase.comp_injective hinj).congr (fun d => ?_)
    simp only [Function.comp_apply]
    rw [starRingEnd_apply, norm_star]⟩

@[simp] lemma sigmaKernelSeq_apply (m d : ℤ) :
    sigmaKernelSeq m d = (starRingEnd ℂ) (circleFourierCoeff sigmaField (m - d)) := rfl

/-- The physical coefficient functional `F ↦ ĉ_{σ·F}(m)`, as a CLM. -/
def physCoeffCLM (m : ℤ) : Lp ℂ 2 circleMeasure →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m).comp
    (circleFourierCLE.toContinuousLinearMap.comp sigmaMulCLM)

@[simp] lemma physCoeffCLM_apply (m : ℤ) (F : Lp ℂ 2 circleMeasure) :
    physCoeffCLM m F = circleFourierCoeff (sigmaMul F) m := by
  simp only [physCoeffCLM, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  change circleFourierCLE (sigmaMulCLM F) m = circleFourierCoeff (sigmaMul F) m
  rw [circleFourierCLE_apply]
  rfl

/-- The convolution coefficient functional, as a CLM (inner product against `sigmaKernelSeq`). -/
def convCoeffCLM (m : ℤ) : Lp ℂ 2 circleMeasure →L[ℂ] ℂ :=
  (innerSL ℂ (sigmaKernelSeq m)).comp circleFourierCLE.toContinuousLinearMap

lemma convCoeffCLM_apply (m : ℤ) (F : Lp ℂ 2 circleMeasure) :
    convCoeffCLM m F
      = ∑' d : ℤ, circleFourierCoeff sigmaField (m - d) * circleFourierCoeff F d := by
  simp only [convCoeffCLM, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    innerSL_apply_apply]
  rw [lp.inner_eq_tsum]
  refine tsum_congr (fun d => ?_)
  rw [RCLike.inner_apply, sigmaKernelSeq_apply, starRingEnd_self_apply, circleFourierCLE_apply]
  ring

/-- `circleFourierCLE.symm` of a single sequence is a scalar multiple of a unit mode. -/
lemma circleFourierCLE_symm_single (d : ℤ) (c : ℂ) :
    circleFourierCLE.symm (lp.single 2 d c) = c • fourierTestLp d := by
  apply circleFourierCLE.injective
  rw [circleFourierCLE.apply_symm_apply, map_smul, circleFourierCLE_fourierTestLp]
  ext e
  rw [lp.coeFn_smul, Pi.smul_apply, lp.coeFn_single, lp.coeFn_single, smul_eq_mul,
    Pi.single_apply, Pi.single_apply]
  split_ifs <;> simp

lemma physCoeffCLM_fourierTestLp (m d : ℤ) :
    physCoeffCLM m (fourierTestLp d) = circleFourierCoeff sigmaField (m - d) := by
  rw [physCoeffCLM_apply, circleFourierCoeff_sigmaMul_fourierTestLp]

lemma convCoeffCLM_fourierTestLp (m d : ℤ) :
    convCoeffCLM m (fourierTestLp d) = circleFourierCoeff sigmaField (m - d) := by
  simp only [convCoeffCLM, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    innerSL_apply_apply, circleFourierCLE_fourierTestLp, lp.inner_single_right,
    sigmaKernelSeq_apply]
  rw [RCLike.inner_apply, starRingEnd_self_apply, one_mul]

/-- For every circle `L²` input, multiplication by `sigmaField` gives convolution
of Fourier coefficients: `coeff(σ·F)(m) = ∑ ĉ(m-d) F̂(d)`. The result follows by
agreement on Fourier modes and continuity; it requires no frequency-support
hypothesis on `F`. -/
theorem circleFourierCoeff_sigmaMul (F : Lp ℂ 2 circleMeasure) (m : ℤ) :
    circleFourierCoeff (sigmaMul F) m
      = ∑' d : ℤ, circleFourierCoeff sigmaField (m - d) * circleFourierCoeff F d := by
  set a := circleFourierCLE F with ha
  let L : lp (fun _ : ℤ => ℂ) 2 →L[ℂ] ℂ :=
    (physCoeffCLM m).comp circleFourierCLE.symm.toContinuousLinearMap
  let R : lp (fun _ : ℤ => ℂ) 2 →L[ℂ] ℂ :=
    (convCoeffCLM m).comp circleFourierCLE.symm.toContinuousLinearMap
  have he : ∀ (d : ℤ) (c : ℂ), L (lp.single 2 d c) = R (lp.single 2 d c) := by
    intro d c
    simp only [L, R, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [circleFourierCLE_symm_single d c, map_smul, map_smul, physCoeffCLM_fourierTestLp,
      convCoeffCLM_fourierTestLp]
  have hsum := lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) a
  have hl := L.hasSum hsum
  have hr := R.hasSum hsum
  have hh : (fun d : ℤ => L (lp.single 2 d (a d))) = (fun d => R (lp.single 2 d (a d))) :=
    funext fun d => he d (a d)
  rw [hh] at hl
  have hLa : L a = circleFourierCoeff (sigmaMul F) m := by
    simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, ha,
      circleFourierCLE.symm_apply_apply, physCoeffCLM_apply]
  have hRa : R a = ∑' d : ℤ, circleFourierCoeff sigmaField (m - d) * circleFourierCoeff F d := by
    simp only [R, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, ha,
      circleFourierCLE.symm_apply_apply]
    rw [convCoeffCLM_apply]
  rw [← hLa, ← hRa]
  exact hl.unique hr

end KsIndex.Trace
