module

/-
Complex H¹ functions on the open unit disk, built from TauCeti real Sobolev spaces.
The carrier pairs two real W¹,² functions with the Euclidean product norm.
The module supplies complex scalar and inner-product structures, characterizes
the carrier by L² values and weak coordinate derivatives, and defines the
Dirichlet and bounded-real-potential forms. Smooth functions with L² values
and derivatives realize these forms without a boundary smoothness assumption.
-/
public import TauCeti.Analysis.Sobolev.W1p.Multiplication
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

@[expose] public section


noncomputable section
open MeasureTheory TopologicalSpace TauCeti
open scoped ENNReal ContDiff InnerProductSpace Gradient

namespace KsIndex.WeakH1

def disk : Opens ℂ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩
abbrev RealH1 : Type := W1p (volume : Measure ℂ) disk 2
abbrev ComplexH1 := WithLp 2 (RealH1 × RealH1)

def rePart (u : ComplexH1) : RealH1 := u.fst
def imPart (u : ComplexH1) : RealH1 := u.snd

def pair (a b : RealH1) : ComplexH1 := WithLp.toLp 2 (a, b)

@[simp] lemma re_pair (a b : RealH1) : rePart (pair a b) = a := rfl
@[simp] lemma im_pair (a b : RealH1) : imPart (pair a b) = b := rfl

/-- A representative of the complex L² value; theorems about it use a.e. equality. -/
def value (u : ComplexH1) (x : ℂ) : ℂ :=
  (W1p.value (rePart u) x : ℂ) + Complex.I * (W1p.value (imPart u) x : ℂ)

@[simp] lemma value_re (u : ComplexH1) (x : ℂ) :
    (value u x).re = W1p.value (rePart u) x := by simp [value]
@[simp] lemma value_im (u : ComplexH1) (x : ℂ) :
    (value u x).im = W1p.value (imPart u) x := by simp [value]

lemma value_memLp (u : ComplexH1) : MemLp (value u) 2 (volume.restrict (disk : Set ℂ)) := by
  have hr : MemLp (fun x : ℂ => (W1p.value (rePart u) x : ℂ)) 2
      (volume.restrict (disk : Set ℂ)) := (Lp.memLp (W1p.value (rePart u))).ofReal
  have hi : MemLp (fun x : ℂ => (W1p.value (imPart u) x : ℂ)) 2
      (volume.restrict (disk : Set ℂ)) := (Lp.memLp (W1p.value (imPart u))).ofReal
  exact hr.add (hi.const_mul Complex.I)

def valueLp (u : ComplexH1) : Lp ℂ 2 (volume.restrict (disk : Set ℂ)) :=
  (value_memLp u).toLp (value u)

lemma valueLp_ae (u : ComplexH1) : valueLp u =ᵐ[volume.restrict (disk : Set ℂ)] value u :=
  MemLp.coeFn_toLp _

/-- The reconstructed value determines the full weak Sobolev jet. -/
lemma value_ae_injective {u v : ComplexH1}
    (h : value u =ᵐ[volume.restrict (disk : Set ℂ)] value v) : u = v := by
  have hr : rePart u = rePart v := W1p.ext_value (Lp.ext (by
    filter_upwards [h] with x hx
    simpa using congrArg Complex.re hx))
  have hi : imPart u = imPart v := W1p.ext_value (Lp.ext (by
    filter_upwards [h] with x hx
    simpa using congrArg Complex.im hx))
  exact (WithLp.ext_iff 2).mpr (Prod.ext hr hi)

lemma valueLp_injective : Function.Injective valueLp := by
  intro u v h
  apply value_ae_injective
  have he : valueLp u =ᵐ[volume.restrict (disk : Set ℂ)] valueLp v := by rw [h]
  exact (valueLp_ae u).symm.trans (he.trans (valueLp_ae v))

/-- Multiplication by i, on the real-pair carrier. -/
def mulI (u : ComplexH1) : ComplexH1 := pair (-imPart u) (rePart u)

lemma mulI_sq (u : ComplexH1) : mulI (mulI u) = -u := by
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext <;> rfl

lemma norm_sq (u : ComplexH1) :
    ‖u‖ ^ 2 = ‖rePart u‖ ^ 2 + ‖imPart u‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 u

lemma norm_mulI (u : ComplexH1) : ‖mulI u‖ = ‖u‖ := by
  have h : ‖mulI u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [norm_sq, norm_sq]
    simp [mulI, add_comm]
  nlinarith [norm_nonneg (mulI u), norm_nonneg u]

/-- The carrier norm is the four-component Hilbert graph norm. -/
lemma graph_norm_sq (u : ComplexH1) :
    ‖u‖ ^ 2 = ‖W1p.value (rePart u)‖ ^ 2 + ‖W1p.gradient (rePart u)‖ ^ 2 +
      (‖W1p.value (imPart u)‖ ^ 2 + ‖W1p.gradient (imPart u)‖ ^ 2) := by
  rw [norm_sq, W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq,
    W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq]

/-- The i-action agrees with complex multiplication on a.e. values. -/
lemma mulI_value_ae (u : ComplexH1) :
    value (mulI u) =ᵐ[volume.restrict (disk : Set ℂ)] fun x => Complex.I * value u x := by
  have hn : W1p.value (-imPart u) = -W1p.value (imPart u) := by
    simpa only [W1p.valueL_apply] using
      (W1p.valueL (mu := (volume : Measure ℂ)) (Omega := disk) (p := 2)).map_neg (imPart u)
  filter_upwards [Lp.coeFn_neg (W1p.value (imPart u))] with x hx
  apply Complex.ext
  · simp only [value_re, mulI, re_pair, hn, Complex.mul_re, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, zero_sub, value_im]
    exact hx
  · simp only [value_im, mulI, im_pair, Complex.mul_im, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, zero_add, value_re]

lemma lp_norm_sq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : Lp F 2 (volume.restrict (disk : Set ℂ))) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂volume.restrict (disk : Set ℂ) := by
  simpa only [real_inner_self_eq_norm_sq] using (L2.inner_def (𝕜 := ℝ) f f)

/-- The squared complex L² norm is the sum of the squared component L² norms. -/
lemma valueLp_norm_sq (u : ComplexH1) :
    ‖valueLp u‖ ^ 2 = ‖W1p.value (rePart u)‖ ^ 2 + ‖W1p.value (imPart u)‖ ^ 2 := by
  rw [lp_norm_sq]
  calc
    _ = ∫ x, (W1p.value (rePart u) x) ^ 2 + (W1p.value (imPart u) x) ^ 2
        ∂volume.restrict (disk : Set ℂ) := by
      apply integral_congr_ae
      filter_upwards [valueLp_ae u] with x hx
      rw [hx, Complex.sq_norm, Complex.normSq_apply, value_re, value_im]
      ring
    _ = _ := by
      rw [integral_add (Lp.memLp (W1p.value (rePart u))).integrable_sq
        (Lp.memLp (W1p.value (imPart u))).integrable_sq]
      rw [W1p.integral_value_sq_eq_norm_value_sq, W1p.integral_value_sq_eq_norm_value_sq]

/-- The squared complex L² value norm plus the two real-gradient energies
equals the squared carrier norm. -/
lemma complex_graph_norm_sq (u : ComplexH1) :
    ‖u‖ ^ 2 = ‖valueLp u‖ ^ 2 +
      (‖W1p.gradient (rePart u)‖ ^ 2 + ‖W1p.gradient (imPart u)‖ ^ 2) := by
  rw [graph_norm_sq, valueLp_norm_sq]
  ring

/-- Postcomposition of a real weak derivative by a real-linear complex embedding. -/
lemma weakLine_comp (L : ℝ →L[ℝ] ℂ) {f g : ℂ → ℝ} {v : ℂ}
    (h : HasWeakLineDerivOn volume disk f g v) :
    HasWeakLineDerivOn volume disk (fun x => L (f x)) (fun x => L (g x)) v := by
  rw [hasWeakLineDerivOn_iff_testFunction]
  refine ⟨inferInstance, L.locallyIntegrableOn_comp h.locallyIntegrableOn,
    L.locallyIntegrableOn_comp h.locallyIntegrableOn_deriv, ?_⟩
  intro φ
  have hl := integrable_lineDeriv_smul_of_locallyIntegrableOn h.locallyIntegrableOn φ v
  have hr := integrable_smul_of_locallyIntegrableOn h.locallyIntegrableOn_deriv φ
  calc
    _ = L (∫ x, lineDeriv ℝ (φ : ℂ → ℝ) x v • f x) := by
      simpa only [map_smul] using L.integral_comp_comm hl
    _ = -L (∫ x, (φ : ℂ → ℝ) x • g x) := by
      rw [h.integral_lineDeriv_smul_eq_neg_integral_smul φ, map_neg]
    _ = _ := by rw [← L.integral_comp_comm hr]; simp only [map_smul]

lemma weakF_comp (L : ℝ →L[ℝ] ℂ) {f : ℂ → ℝ} {U : ℂ → ℂ →L[ℝ] ℝ}
    (h : HasWeakFDerivOn volume disk f U) :
    HasWeakFDerivOn volume disk (fun x => L (f x)) (fun x => L.comp (U x)) := by
  rw [hasWeakFDerivOn_iff]
  intro v
  exact weakLine_comp L (h.hasWeakLineDerivOn v)

def weakDerivative (u : ComplexH1) (x : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (innerSL ℝ (W1p.gradient (rePart u) x)) +
  (Complex.I • Complex.ofRealCLM).comp (innerSL ℝ (W1p.gradient (imPart u) x))

lemma hasWeakDerivative (u : ComplexH1) :
    HasWeakFDerivOn volume disk (value u) (weakDerivative u) := by
  have hr := weakF_comp Complex.ofRealCLM (W1p.hasWeakFDerivOn (rePart u))
  have hi := weakF_comp (Complex.I • Complex.ofRealCLM) (W1p.hasWeakFDerivOn (imPart u))
  convert hr.add hi using 1 <;> rfl

/-- A smooth real multiplier, with bounded value and gradient on the disk,
applied separately to real and imaginary parts. -/
def smoothMul (ψ : ℂ → ℝ) (hψ : ContDiff ℝ ∞ ψ) {M : ℝ}
    (hM : 0 ≤ M) (hv : ∀ x ∈ disk, |ψ x| ≤ M)
    (hg : ∀ x ∈ disk, ‖∇ ψ x‖ ≤ M) (u : ComplexH1) : ComplexH1 :=
  pair (W1p.contDiffSMul ψ hψ hM hv hg (rePart u))
    (W1p.contDiffSMul ψ hψ hM hv hg (imPart u))

lemma smoothMul_value_ae (ψ : ℂ → ℝ) (hψ : ContDiff ℝ ∞ ψ) {M : ℝ}
    (hM : 0 ≤ M) (hv : ∀ x ∈ disk, |ψ x| ≤ M)
    (hg : ∀ x ∈ disk, ‖∇ ψ x‖ ≤ M) (u : ComplexH1) :
    value (smoothMul ψ hψ hM hv hg u) =ᵐ[volume.restrict (disk : Set ℂ)]
      fun x => ψ x • value u x := by
  filter_upwards [W1p.value_contDiffSMul_ae hψ hM hv hg (rePart u),
    W1p.value_contDiffSMul_ae hψ hM hv hg (imPart u)] with x hr hi
  simp only [value, smoothMul, re_pair, im_pair, hr, hi, smul_eq_mul,
    Complex.ofReal_mul, Complex.real_smul]
  ring

lemma smoothMul_weak_rule (ψ : ℂ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (u : ComplexH1) :
    HasWeakFDerivOn volume disk (fun x => ψ x • value u x)
      (fun x => ψ x • weakDerivative u x + (fderiv ℝ ψ x).smulRight (value u x)) :=
  (hasWeakDerivative u).contDiff_smul hψ

/-- The carrier multiplier has exactly the product-rule weak derivative a.e. -/
lemma smoothMul_weakDerivative_ae (ψ : ℂ → ℝ) (hψ : ContDiff ℝ ∞ ψ) {M : ℝ}
    (hM : 0 ≤ M) (hv : ∀ x ∈ disk, |ψ x| ≤ M)
    (hg : ∀ x ∈ disk, ‖∇ ψ x‖ ≤ M) (u : ComplexH1) :
    weakDerivative (smoothMul ψ hψ hM hv hg u) =ᵐ[volume.restrict (disk : Set ℂ)]
      fun x => ψ x • weakDerivative u x + (fderiv ℝ ψ x).smulRight (value u x) := by
  exact ((hasWeakDerivative (smoothMul ψ hψ hM hv hg u)).congr_ae
    (smoothMul_value_ae ψ hψ hM hv hg u)).ae_eq (smoothMul_weak_rule ψ hψ u)

/-! ## Complex scalars and continuous linear maps -/

/-- The usual complex action on a real/imaginary pair. -/
def complexSMul (z : ℂ) (u : ComplexH1) : ComplexH1 :=
  pair (z.re • rePart u - z.im • imPart u)
    (z.im • rePart u + z.re • imPart u)

instance instComplexModule : Module ℂ ComplexH1 where
  smul := complexSMul
  one_smul u := by
    change complexSMul 1 u = u
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext <;> simp [complexSMul, pair, rePart, imPart]
  mul_smul z w u := by
    change complexSMul (z * w) u = complexSMul z (complexSMul w u)
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext <;> simp [complexSMul, pair, rePart, imPart,
      Complex.mul_re, Complex.mul_im] <;> module
  smul_zero z := by
    change complexSMul z 0 = 0
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext <;> simp [complexSMul, pair, rePart, imPart]
  smul_add z u v := by
    change complexSMul z (u + v) = complexSMul z u + complexSMul z v
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext <;> simp [complexSMul, pair, rePart, imPart] <;> module
  add_smul z w u := by
    change complexSMul (z + w) u = complexSMul z u + complexSMul w u
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext <;> simp [complexSMul, pair, rePart, imPart] <;> module
  zero_smul u := by
    change complexSMul 0 u = 0
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext <;> simp [complexSMul, pair, rePart, imPart]

@[simp] lemma complex_smul_re (z : ℂ) (u : ComplexH1) :
    rePart (z • u) = z.re • rePart u - z.im • imPart u := rfl
@[simp] lemma complex_smul_im (z : ℂ) (u : ComplexH1) :
    imPart (z • u) = z.im • rePart u + z.re • imPart u := rfl

lemma complex_smul_decompose (z : ℂ) (u : ComplexH1) :
    z • u = z.re • u + z.im • mulI u := by
  change complexSMul z u = _
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext <;> simp [complexSMul, mulI, pair, rePart, imPart, sub_eq_add_neg, add_comm]

lemma inner_mulI (u : ComplexH1) : inner ℝ u (mulI u) = 0 := by
  rw [WithLp.prod_inner_apply]
  change inner ℝ (rePart u) (-imPart u) + inner ℝ (imPart u) (rePart u) = 0
  rw [inner_neg_right, real_inner_comm (imPart u) (rePart u)]
  ring

lemma norm_complex_smul (z : ℂ) (u : ComplexH1) : ‖z • u‖ = ‖z‖ * ‖u‖ := by
  have hcross : inner ℝ (z.re • u) (z.im • mulI u) = 0 := by
    rw [WithLp.prod_inner_apply]
    change inner ℝ (z.re • rePart u) (z.im • (-imPart u)) +
      inner ℝ (z.re • imPart u) (z.im • rePart u) = 0
    rw [real_inner_smul_left (rePart u) (z.im • (-imPart u)) z.re,
      real_inner_smul_left (imPart u) (z.im • rePart u) z.re,
      real_inner_smul_right (rePart u) (-imPart u) z.im,
      real_inner_smul_right (imPart u) (rePart u) z.im,
      inner_neg_right, real_inner_comm (imPart u) (rePart u)]
    ring
  have hsq : ‖z • u‖ ^ 2 = (‖z‖ * ‖u‖) ^ 2 := by
    rw [complex_smul_decompose, norm_add_sq_real, norm_smul, norm_smul,
      hcross, norm_mulI]
    simp only [Real.norm_eq_abs, mul_zero, add_zero]
    rw [mul_pow, mul_pow, sq_abs, sq_abs, mul_pow, Complex.sq_norm, Complex.normSq_apply]
    ring
  nlinarith [norm_nonneg (z • u), mul_nonneg (norm_nonneg z) (norm_nonneg u)]

instance instComplexNormedSpace : NormedSpace ℂ ComplexH1 where
  norm_smul_le z u := (norm_complex_smul z u).le

/-- The complex action restricts to the pre-existing real action. -/
lemma ofReal_smul (r : ℝ) (u : ComplexH1) : (r : ℂ) • u = r • u := by
  rw [complex_smul_decompose, Complex.ofReal_re, Complex.ofReal_im,
    zero_smul ℝ (mulI u), add_zero]

instance instRealComplexScalarTower : IsScalarTower ℝ ℂ ComplexH1 where
  smul_assoc r z u := by
    rw [← ofReal_smul r (z • u), smul_smul, Complex.real_smul]

/-- Value reconstruction as a continuous real-linear map. -/
def valueRealCLM : ComplexH1 →L[ℝ] Lp ℂ 2 (volume.restrict (disk : Set ℂ)) :=
  (Complex.ofRealCLM.compLpL 2 (volume.restrict (disk : Set ℂ))).comp
    (W1p.valueL.comp (WithLp.fstL 2 ℝ RealH1 RealH1)) +
  ((Complex.I • Complex.ofRealCLM).compLpL 2 (volume.restrict (disk : Set ℂ))).comp
    (W1p.valueL.comp (WithLp.sndL 2 ℝ RealH1 RealH1))

lemma valueRealCLM_eq (u : ComplexH1) : valueRealCLM u = valueLp u := by
  simp only [valueRealCLM, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, W1p.valueL_apply]
  change Complex.ofRealCLM.compLpL 2 _ (W1p.value (rePart u)) +
    (Complex.I • Complex.ofRealCLM).compLpL 2 _ (W1p.value (imPart u)) = valueLp u
  apply Lp.ext
  filter_upwards [Lp.coeFn_add
      (Complex.ofRealCLM.compLpL 2 (volume.restrict (disk : Set ℂ)) (W1p.value (rePart u)))
      ((Complex.I • Complex.ofRealCLM).compLpL 2 (volume.restrict (disk : Set ℂ))
        (W1p.value (imPart u))),
    Complex.ofRealCLM.coeFn_compLpL (W1p.value (rePart u)),
    (Complex.I • Complex.ofRealCLM).coeFn_compLpL (W1p.value (imPart u)),
    valueLp_ae u] with x ha hr hi hv
  simp only [ha, Pi.add_apply, hr, hi, hv]
  rfl

lemma valueLp_mulI (u : ComplexH1) : valueLp (mulI u) = Complex.I • valueLp u := by
  apply Lp.ext
  filter_upwards [valueLp_ae (mulI u), mulI_value_ae u, valueLp_ae u,
    Lp.coeFn_smul Complex.I (valueLp u)] with x ha hb hc hd
  rw [ha, hb, ← hc, hd]
  rfl

lemma valueLp_smul (z : ℂ) (u : ComplexH1) : valueLp (z • u) = z • valueLp u := by
  rw [complex_smul_decompose, ← valueRealCLM_eq, map_add, map_smul, map_smul]
  rw [valueRealCLM_eq, valueRealCLM_eq, valueLp_mulI]
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (z.re • valueLp u) (z.im • (Complex.I • valueLp u)),
    Lp.coeFn_smul z.re (valueLp u), Lp.coeFn_smul z.im (Complex.I • valueLp u),
    Lp.coeFn_smul Complex.I (valueLp u), Lp.coeFn_smul z (valueLp u)] with x ha hr hi hI hz
  simp only [ha, Pi.add_apply, hr, hi, Pi.smul_apply, hI, hz, Complex.real_smul, smul_eq_mul]
  rw [← mul_assoc, ← add_mul, Complex.re_add_im]

lemma norm_valueLp_le (u : ComplexH1) : ‖valueLp u‖ ≤ ‖u‖ := by
  have h := complex_graph_norm_sq u
  nlinarith [norm_nonneg u, norm_nonneg (valueLp u),
    sq_nonneg ‖W1p.gradient (rePart u)‖, sq_nonneg ‖W1p.gradient (imPart u)‖]

/-- The complex-linear continuous injection of the carrier into complex L². -/
def valueCLM : ComplexH1 →L[ℂ] Lp ℂ 2 (volume.restrict (disk : Set ℂ)) :=
  LinearMap.mkContinuous
    { toFun := valueLp
      map_add' := fun u v => by
        simpa only [valueRealCLM_eq] using valueRealCLM.map_add u v
      map_smul' := valueLp_smul }
    1 (fun u => by simpa using norm_valueLp_le u)

lemma valueCLM_injective : Function.Injective valueCLM := valueLp_injective

/-- The paired multiplier inherits the real multiplier's quantitative bound. -/
lemma norm_smoothMul_le (ψ : ℂ → ℝ) (hψ : ContDiff ℝ ∞ ψ) {M : ℝ}
    (hM : 0 ≤ M) (hv : ∀ x ∈ disk, |ψ x| ≤ M)
    (hg : ∀ x ∈ disk, ‖∇ ψ x‖ ≤ M) (u : ComplexH1) :
    ‖smoothMul ψ hψ hM hv hg u‖ ≤ 2 * M * ‖u‖ := by
  let T := W1p.contDiffSMulL (mu := (volume : Measure ℂ)) (Omega := disk) (p := 2) ψ hψ hM hv hg
  have hr : ‖T (rePart u)‖ ≤ 2 * M * ‖rePart u‖ := by
    simpa only [T, W1p.contDiffSMulL_apply] using
      W1p.norm_contDiffSMul_le hψ hM hv hg _
  have hi : ‖T (imPart u)‖ ≤ 2 * M * ‖imPart u‖ := by
    simpa only [T, W1p.contDiffSMulL_apply] using
      W1p.norm_contDiffSMul_le hψ hM hv hg _
  have hrs := mul_self_le_mul_self (norm_nonneg _) hr
  have his := mul_self_le_mul_self (norm_nonneg _) hi
  have hnorm : ‖smoothMul ψ hψ hM hv hg u‖ ^ 2 =
      ‖T (rePart u)‖ ^ 2 + ‖T (imPart u)‖ ^ 2 := by
    simpa only [T, W1p.contDiffSMulL_apply, smoothMul, re_pair, im_pair] using norm_sq (smoothMul ψ hψ hM hv hg u)
  have hu := norm_sq u
  have hsq : ‖smoothMul ψ hψ hM hv hg u‖ ^ 2 ≤ (2 * M * ‖u‖) ^ 2 := by
    rw [hnorm, mul_pow, hu]
    nlinarith
  nlinarith [norm_nonneg (smoothMul ψ hψ hM hv hg u), norm_nonneg u,
    mul_nonneg (by positivity : 0 ≤ 2 * M) (norm_nonneg u)]

/-- Smooth real multipliers act as bounded complex-linear operators on the carrier. -/
def smoothMulCLM (ψ : ℂ → ℝ) (hψ : ContDiff ℝ ∞ ψ) {M : ℝ}
    (hM : 0 ≤ M) (hv : ∀ x ∈ disk, |ψ x| ≤ M)
    (hg : ∀ x ∈ disk, ‖∇ ψ x‖ ≤ M) : ComplexH1 →L[ℂ] ComplexH1 :=
  let T := W1p.contDiffSMulL (mu := (volume : Measure ℂ)) (Omega := disk) (p := 2) ψ hψ hM hv hg
  LinearMap.mkContinuous
    { toFun := smoothMul ψ hψ hM hv hg
      map_add' := fun u v => by
        simp only [smoothMul, ← W1p.contDiffSMulL_apply]
        apply (WithLp.ext_iff 2).mpr
        apply Prod.ext
        · change T (rePart u + rePart v) = T (rePart u) + T (rePart v)
          exact T.map_add _ _
        · change T (imPart u + imPart v) = T (imPart u) + T (imPart v)
          exact T.map_add _ _
      map_smul' := fun z u => by
        simp only [smoothMul, ← W1p.contDiffSMulL_apply]
        apply (WithLp.ext_iff 2).mpr
        apply Prod.ext
        · change T (z.re • rePart u - z.im • imPart u) =
            z.re • T (rePart u) - z.im • T (imPart u)
          rw [map_sub, map_smul, map_smul]
        · change T (z.im • rePart u + z.re • imPart u) =
            z.im • T (rePart u) + z.re • T (imPart u)
          rw [map_add, map_smul, map_smul] }
    (2 * M) (norm_smoothMul_le ψ hψ hM hv hg)

lemma smoothMulCLM_apply (ψ : ℂ → ℝ) (hψ : ContDiff ℝ ∞ ψ) {M : ℝ}
    (hM : 0 ≤ M) (hv : ∀ x ∈ disk, |ψ x| ≤ M)
    (hg : ∀ x ∈ disk, ‖∇ ψ x‖ ≤ M) (u : ComplexH1) :
    smoothMulCLM ψ hψ hM hv hg u = smoothMul ψ hψ hM hv hg u := rfl

/-! ## Characterization by complex distributional derivatives -/

abbrev L2C := Lp ℂ 2 (volume.restrict (disk : Set ℂ))
abbrev L2R := Lp ℝ 2 (volume.restrict (disk : Set ℂ))

def reLp (f : L2C) : L2R := Complex.reCLM.compLpL 2 _ f
def imLp (f : L2C) : L2R := Complex.imCLM.compLpL 2 _ f
def joinLp (a b : L2R) : L2C := Complex.ofRealCLM.compLpL 2 _ a +
  (Complex.I • Complex.ofRealCLM).compLpL 2 _ b

lemma reLp_ae (f : L2C) : reLp f =ᵐ[volume.restrict (disk : Set ℂ)] fun x => (f x).re :=
  Complex.reCLM.coeFn_compLpL f
lemma imLp_ae (f : L2C) : imLp f =ᵐ[volume.restrict (disk : Set ℂ)] fun x => (f x).im :=
  Complex.imCLM.coeFn_compLpL f
lemma joinLp_ae (a b : L2R) : joinLp a b =ᵐ[volume.restrict (disk : Set ℂ)]
    fun x => (a x : ℂ) + Complex.I * (b x : ℂ) := by
  filter_upwards [Lp.coeFn_add (Complex.ofRealCLM.compLpL 2 _ a)
      ((Complex.I • Complex.ofRealCLM).compLpL 2 _ b),
    Complex.ofRealCLM.coeFn_compLpL a,
    (Complex.I • Complex.ofRealCLM).coeFn_compLpL b] with x ha hr hi
  simp only [joinLp, ha, Pi.add_apply, hr, hi]
  rfl

def Dxy (dx dy : ℂ → ℂ) (x : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.reCLM.smulRight (dx x) + Complex.imCLM.smulRight (dy x)

lemma Dxy_apply (dx dy : ℂ → ℂ) (x v : ℂ) :
    Dxy dx dy x v = v.re • dx x + v.im • dy x := rfl
@[simp] lemma Dxy_one (dx dy : ℂ → ℂ) (x : ℂ) : Dxy dx dy x 1 = dx x := by
  simp [Dxy_apply]
@[simp] lemma Dxy_I (dx dy : ℂ → ℂ) (x : ℂ) : Dxy dx dy x Complex.I = dy x := by
  simp [Dxy_apply]

lemma realLinear_coordinates (L : ℂ →L[ℝ] ℂ) (v : ℂ) :
    L v = v.re • L 1 + v.im • L Complex.I := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    simp [Complex.real_smul, Complex.re_add_im]
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul]

/-- Complex L² values with independent L² coordinate distributional derivatives. -/
def HasComplexH1Jet (f dx dy : L2C) : Prop :=
  HasWeakFDerivOn volume disk f (Dxy dx dy)

lemma weakJet_congr_ae {f g dx dy ex ey : ℂ → ℂ}
    (hf : f =ᵐ[volume.restrict (disk : Set ℂ)] g)
    (hx : dx =ᵐ[volume.restrict (disk : Set ℂ)] ex)
    (hy : dy =ᵐ[volume.restrict (disk : Set ℂ)] ey) :
    HasWeakFDerivOn volume disk f (Dxy dx dy) ↔
      HasWeakFDerivOn volume disk g (Dxy ex ey) := by
  have hD : Dxy dx dy =ᵐ[volume.restrict (disk : Set ℂ)] Dxy ex ey := by
    filter_upwards [hx, hy] with x hx hy
    simp only [Dxy, hx, hy]
  exact ⟨fun h => (h.congr_ae hf).congr_ae_deriv hD,
    fun h => (h.congr_ae hf.symm).congr_ae_deriv hD.symm⟩

lemma real_inner_coordinates (a v : ℂ) : inner ℝ a v = a.re * v.re + a.im * v.im := by
  rw [real_inner_eq_re_inner, RCLike.inner_apply]
  simp
  ring

def dxLp (u : ComplexH1) : L2C :=
  joinLp (reLp (W1p.gradient (rePart u))) (reLp (W1p.gradient (imPart u)))
def dyLp (u : ComplexH1) : L2C :=
  joinLp (imLp (W1p.gradient (rePart u))) (imLp (W1p.gradient (imPart u)))

lemma dxLp_ae (u : ComplexH1) : dxLp u =ᵐ[volume.restrict (disk : Set ℂ)]
    fun x => ((W1p.gradient (rePart u) x).re : ℂ) +
      Complex.I * ((W1p.gradient (imPart u) x).re : ℂ) := by
  filter_upwards [joinLp_ae (reLp (W1p.gradient (rePart u)))
      (reLp (W1p.gradient (imPart u))), reLp_ae (W1p.gradient (rePart u)),
    reLp_ae (W1p.gradient (imPart u))] with x h hr hi
  simpa only [dxLp, hr, hi] using h
lemma dyLp_ae (u : ComplexH1) : dyLp u =ᵐ[volume.restrict (disk : Set ℂ)]
    fun x => ((W1p.gradient (rePart u) x).im : ℂ) +
      Complex.I * ((W1p.gradient (imPart u) x).im : ℂ) := by
  filter_upwards [joinLp_ae (imLp (W1p.gradient (rePart u)))
      (imLp (W1p.gradient (imPart u))), imLp_ae (W1p.gradient (rePart u)),
    imLp_ae (W1p.gradient (imPart u))] with x h hr hi
  simpa only [dyLp, hr, hi] using h

lemma weakDerivative_coordinates (u : ComplexH1) :
    weakDerivative u =ᵐ[volume.restrict (disk : Set ℂ)] Dxy (dxLp u) (dyLp u) := by
  filter_upwards [dxLp_ae u, dyLp_ae u] with x hx hy
  ext v
  simp only [weakDerivative, add_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, Complex.ofRealCLM_apply, smul_apply, smul_eq_mul,
    real_inner_coordinates, Dxy_apply, hx, hy, Complex.real_smul,
    Complex.ofReal_add, Complex.ofReal_mul]
  ring

lemma carrier_hasJet (u : ComplexH1) : HasComplexH1Jet (valueCLM u) (dxLp u) (dyLp u) := by
  exact ((hasWeakDerivative u).congr_ae (valueLp_ae u).symm).congr_ae_deriv
    (weakDerivative_coordinates u)

lemma jet_derivatives_unique {f dx dy ex ey : L2C}
    (h : HasComplexH1Jet f dx dy) (h' : HasComplexH1Jet f ex ey) : dx = ex ∧ dy = ey := by
  have he := h.ae_eq h'
  constructor
  · apply Lp.ext
    filter_upwards [he] with x hx
    simpa using congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) hx
  · apply Lp.ext
    filter_upwards [he] with x hx
    simpa using congrArg (fun L : ℂ →L[ℝ] ℂ => L Complex.I) hx

/-- Postcomposition of a complex weak directional derivative by a continuous
real-linear functional. -/
lemma weakLine_project (L : ℂ →L[ℝ] ℝ) {f g : ℂ → ℂ} {v : ℂ}
    (h : HasWeakLineDerivOn volume disk f g v) :
    HasWeakLineDerivOn volume disk (fun x => L (f x)) (fun x => L (g x)) v := by
  rw [hasWeakLineDerivOn_iff_testFunction]
  refine ⟨inferInstance, L.locallyIntegrableOn_comp h.locallyIntegrableOn,
    L.locallyIntegrableOn_comp h.locallyIntegrableOn_deriv, ?_⟩
  intro φ
  have hl := integrable_lineDeriv_smul_of_locallyIntegrableOn h.locallyIntegrableOn φ v
  have hr := integrable_smul_of_locallyIntegrableOn h.locallyIntegrableOn_deriv φ
  calc
    _ = L (∫ x, lineDeriv ℝ (φ : ℂ → ℝ) x v • f x) := by
      simpa only [map_smul] using L.integral_comp_comm hl
    _ = -L (∫ x, (φ : ℂ → ℝ) x • g x) := by
      rw [h.integral_lineDeriv_smul_eq_neg_integral_smul φ, map_neg]
    _ = _ := by rw [← L.integral_comp_comm hr]; simp only [map_smul]

lemma weakF_project (L : ℂ →L[ℝ] ℝ) {f : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (h : HasWeakFDerivOn volume disk f U) :
    HasWeakFDerivOn volume disk (fun x => L (f x)) (fun x => L.comp (U x)) := by
  rw [hasWeakFDerivOn_iff]
  intro v
  exact weakLine_project L (h.hasWeakLineDerivOn v)

def projectedGradient (L : ℂ →L[ℝ] ℝ) (dx dy : L2C) : L2C :=
  joinLp (L.compLpL 2 _ dx) (L.compLpL 2 _ dy)

lemma projectedGradient_ae (L : ℂ →L[ℝ] ℝ) (dx dy : L2C) :
    projectedGradient L dx dy =ᵐ[volume.restrict (disk : Set ℂ)]
      fun x => (L (dx x) : ℂ) + Complex.I * (L (dy x) : ℂ) := by
  filter_upwards [joinLp_ae (L.compLpL 2 _ dx) (L.compLpL 2 _ dy),
    L.coeFn_compLpL dx, L.coeFn_compLpL dy] with x h hx hy
  simpa only [projectedGradient, hx, hy] using h

lemma projected_hasWeak (L : ℂ →L[ℝ] ℝ) {f dx dy : L2C}
    (h : HasComplexH1Jet f dx dy) :
    HasWeakFDerivOn volume disk (L.compLpL 2 (volume.restrict (disk : Set ℂ)) f)
      (fun x => innerSL ℝ (projectedGradient L dx dy x)) := by
  apply ((weakF_project L h).congr_ae (L.coeFn_compLpL f).symm).congr_ae_deriv
  filter_upwards [projectedGradient_ae L dx dy] with x hx
  ext v
  change L (Dxy dx dy x v) = inner ℝ (projectedGradient L dx dy x) v
  rw [hx, real_inner_coordinates]
  simp only [Dxy_apply, map_add, map_smul]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, mul_zero, sub_zero,
    Complex.add_im, Complex.mul_im, zero_add, add_zero, smul_eq_mul]
  ring

def projectedH1 (L : ℂ →L[ℝ] ℝ) (f dx dy : L2C) (h : HasComplexH1Jet f dx dy) : RealH1 :=
  W1p.mk (L.compLpL 2 _ f) (projectedGradient L dx dy) (projected_hasWeak L h)

lemma projectedH1_value (L : ℂ →L[ℝ] ℝ) (f dx dy : L2C) (h : HasComplexH1Jet f dx dy) :
    W1p.value (projectedH1 L f dx dy h) = L.compLpL 2 _ f := W1p.value_mk _ _ _

def reconstruct (f dx dy : L2C) (h : HasComplexH1Jet f dx dy) : ComplexH1 :=
  pair (projectedH1 Complex.reCLM f dx dy h) (projectedH1 Complex.imCLM f dx dy h)

lemma reconstruct_value (f dx dy : L2C) (h : HasComplexH1Jet f dx dy) :
    valueCLM (reconstruct f dx dy h) = f := by
  apply Lp.ext
  filter_upwards [valueLp_ae (reconstruct f dx dy h), reLp_ae f, imLp_ae f] with x hv hr hi
  change valueLp (reconstruct f dx dy h) x = f x
  rw [hv, value]
  simp only [reconstruct, re_pair, im_pair, projectedH1_value]
  change ((reLp f x : ℝ) : ℂ) + Complex.I * ((imLp f x : ℝ) : ℂ) = f x
  rw [hr, hi, mul_comm Complex.I, Complex.re_add_im]

/-- Every independent distributional jet has a unique carrier realization. -/
theorem exists_unique_carrier_of_jet (f dx dy : L2C) (h : HasComplexH1Jet f dx dy) :
    ∃! u : ComplexH1, valueCLM u = f ∧ dxLp u = dx ∧ dyLp u = dy := by
  let u := reconstruct f dx dy h
  have hu : valueCLM u = f := reconstruct_value f dx dy h
  have hj : HasComplexH1Jet f (dxLp u) (dyLp u) := by rw [← hu]; exact carrier_hasJet u
  have hd := jet_derivatives_unique hj h
  refine ⟨u, ⟨hu, hd⟩, ?_⟩
  intro v hv
  exact valueCLM_injective (hv.1.trans hu.symm)

/-- The carrier is characterized by complex L² data with genuine weak derivatives. -/
theorem hasComplexH1Jet_iff (f dx dy : L2C) : HasComplexH1Jet f dx dy ↔
    ∃ u : ComplexH1, valueCLM u = f ∧ dxLp u = dx ∧ dyLp u = dy := by
  constructor
  · intro h
    exact (exists_unique_carrier_of_jet f dx dy h).exists
  · rintro ⟨u, rfl, rfl, rfl⟩
    exact carrier_hasJet u

lemma coordinate_gradient_norm_sq (u : ComplexH1) :
    ‖dxLp u‖ ^ 2 + ‖dyLp u‖ ^ 2 =
      ‖W1p.gradient (rePart u)‖ ^ 2 + ‖W1p.gradient (imPart u)‖ ^ 2 := by
  have hint (f : L2C) : Integrable (fun x => ‖f x‖ ^ 2)
      (volume.restrict (disk : Set ℂ)) :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp f).aestronglyMeasurable).mp (Lp.memLp f)
  simp only [lp_norm_sq]
  rw [← integral_add (hint (dxLp u)) (hint (dyLp u)),
    ← integral_add (hint (W1p.gradient (rePart u))) (hint (W1p.gradient (imPart u)))]
  apply integral_congr_ae
  filter_upwards [dxLp_ae u, dyLp_ae u] with x hx hy
  rw [hx, hy]
  simp [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- Exact coordinate graph norm, with no change to the carrier norm. -/
theorem coordinate_graph_norm_sq (u : ComplexH1) :
    ‖u‖ ^ 2 = ‖valueCLM u‖ ^ 2 + ‖dxLp u‖ ^ 2 + ‖dyLp u‖ ^ 2 := by
  change ‖u‖ ^ 2 = ‖valueLp u‖ ^ 2 + ‖dxLp u‖ ^ 2 + ‖dyLp u‖ ^ 2
  rw [complex_graph_norm_sq, ← coordinate_gradient_norm_sq]
  ring

theorem jet_graph_norm_sq {u : ComplexH1} {f dx dy : L2C}
    (hf : valueCLM u = f) (hx : dxLp u = dx) (hy : dyLp u = dy) :
    ‖u‖ ^ 2 = ‖f‖ ^ 2 + ‖dx‖ ^ 2 + ‖dy‖ ^ 2 := by
  rw [← hf, ← hx, ← hy]
  exact coordinate_graph_norm_sq u

/-- Apply a real gradient coordinate to each component, then reconstruct complex values. -/
def coordinateRealCLM (L : ℂ →L[ℝ] ℝ) : ComplexH1 →L[ℝ] L2C :=
  let T : RealH1 →L[ℝ] L2R := (L.compLpL 2 _).comp W1p.gradientL
  (Complex.ofRealCLM.compLpL 2 _).comp (T.comp (WithLp.fstL 2 ℝ RealH1 RealH1)) +
  ((Complex.I • Complex.ofRealCLM).compLpL 2 _).comp
    (T.comp (WithLp.sndL 2 ℝ RealH1 RealH1))

lemma coordinateRealCLM_apply (L : ℂ →L[ℝ] ℝ) (u : ComplexH1) :
    coordinateRealCLM L u = joinLp
      (L.compLpL 2 _ (W1p.gradient (rePart u)))
      (L.compLpL 2 _ (W1p.gradient (imPart u))) := by
  simp only [coordinateRealCLM, joinLp, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, W1p.gradientL_apply]
  rfl

lemma coordinateRealCLM_mulI (L : ℂ →L[ℝ] ℝ) (u : ComplexH1) :
    coordinateRealCLM L (mulI u) = Complex.I • coordinateRealCLM L u := by
  let a := L.compLpL 2 (volume.restrict (disk : Set ℂ)) (W1p.gradient (rePart u))
  let b := L.compLpL 2 (volume.restrict (disk : Set ℂ)) (W1p.gradient (imPart u))
  have h : coordinateRealCLM L (mulI u) = joinLp (-b) a := by
    simp only [coordinateRealCLM_apply, mulI, re_pair, im_pair,
      ← W1p.gradientL_apply, map_neg]
    simp only [W1p.gradientL_apply]
    rfl
  rw [h]
  rw [coordinateRealCLM_apply]
  change joinLp (-b) a = Complex.I • joinLp a b
  apply Lp.ext
  filter_upwards [joinLp_ae (-b) a, joinLp_ae a b, Lp.coeFn_neg b,
    Lp.coeFn_smul Complex.I (joinLp a b)] with x h1 h2 h3 h4
  simp only [h1, h4, Pi.smul_apply, h2, smul_eq_mul, h3, Pi.neg_apply, Complex.ofReal_neg]
  rw [mul_add, ← mul_assoc, Complex.I_mul_I]
  ring

lemma coordinateRealCLM_smul (L : ℂ →L[ℝ] ℝ) (z : ℂ) (u : ComplexH1) :
    coordinateRealCLM L (z • u) = z • coordinateRealCLM L u := by
  rw [complex_smul_decompose, map_add, map_smul, map_smul, coordinateRealCLM_mulI]
  apply Lp.ext
  let f := coordinateRealCLM L u
  change (z.re • f + z.im • (Complex.I • f) : L2C) =ᵐ[_] (z • f : L2C)
  filter_upwards [Lp.coeFn_add (z.re • f) (z.im • (Complex.I • f)),
    Lp.coeFn_smul z.re f, Lp.coeFn_smul z.im (Complex.I • f),
    Lp.coeFn_smul Complex.I f, Lp.coeFn_smul z f] with x ha hr hi hI hz
  simp only [ha, Pi.add_apply, hr, hi, Pi.smul_apply, hI, hz, Complex.real_smul, smul_eq_mul]
  rw [← mul_assoc, ← add_mul, Complex.re_add_im]

lemma norm_dxLp_le (u : ComplexH1) : ‖dxLp u‖ ≤ ‖u‖ := by
  have h := coordinate_graph_norm_sq u
  nlinarith [norm_nonneg u, norm_nonneg (dxLp u), sq_nonneg ‖valueCLM u‖,
    sq_nonneg ‖dyLp u‖]

lemma norm_dyLp_le (u : ComplexH1) : ‖dyLp u‖ ≤ ‖u‖ := by
  have h := coordinate_graph_norm_sq u
  nlinarith [norm_nonneg u, norm_nonneg (dyLp u), sq_nonneg ‖valueCLM u‖,
    sq_nonneg ‖dxLp u‖]

def dxCLM : ComplexH1 →L[ℂ] L2C :=
  LinearMap.mkContinuous
    { toFun := dxLp
      map_add' := fun u v => by
        simpa only [coordinateRealCLM_apply, dxLp, reLp, RingHom.id_apply] using
          (coordinateRealCLM Complex.reCLM).map_add u v
      map_smul' := fun z u => by
        simpa only [coordinateRealCLM_apply, dxLp, reLp, RingHom.id_apply] using
          coordinateRealCLM_smul Complex.reCLM z u }
    1 (fun u => by change ‖dxLp u‖ ≤ 1 * ‖u‖; simpa using norm_dxLp_le u)

def dyCLM : ComplexH1 →L[ℂ] L2C :=
  LinearMap.mkContinuous
    { toFun := dyLp
      map_add' := fun u v => by
        simpa only [coordinateRealCLM_apply, dyLp, imLp, RingHom.id_apply] using
          (coordinateRealCLM Complex.imCLM).map_add u v
      map_smul' := fun z u => by
        simpa only [coordinateRealCLM_apply, dyLp, imLp, RingHom.id_apply] using
          coordinateRealCLM_smul Complex.imCLM z u }
    1 (fun u => by change ‖dyLp u‖ ≤ 1 * ‖u‖; simpa using norm_dyLp_le u)

def mass (u v : ComplexH1) : ℂ := inner ℂ (valueCLM u) (valueCLM v)
def dirichlet (u v : ComplexH1) : ℂ :=
  inner ℂ (dxCLM u) (dxCLM v) + inner ℂ (dyCLM u) (dyCLM v)
def h1Pair (u v : ComplexH1) : ℂ := mass u v + dirichlet u v

lemma h1Pair_add_left (u v w : ComplexH1) :
    h1Pair (u + v) w = h1Pair u w + h1Pair v w := by
  simp only [h1Pair, mass, dirichlet, map_add, inner_add_left]
  ring

lemma h1Pair_add_right (u v w : ComplexH1) :
    h1Pair u (v + w) = h1Pair u v + h1Pair u w := by
  simp only [h1Pair, mass, dirichlet, map_add, inner_add_right]
  ring

lemma h1Pair_smul_left (z : ℂ) (u v : ComplexH1) :
    h1Pair (z • u) v = (starRingEnd ℂ) z * h1Pair u v := by
  simp only [h1Pair, mass, dirichlet, map_smul, inner_smul_left]
  ring

lemma h1Pair_smul_right (z : ℂ) (u v : ComplexH1) :
    h1Pair u (z • v) = z * h1Pair u v := by
  simp only [h1Pair, mass, dirichlet, map_smul, inner_smul_right]
  ring

lemma h1Pair_conj (u v : ComplexH1) : (starRingEnd ℂ) (h1Pair v u) = h1Pair u v := by
  simp only [h1Pair, mass, dirichlet, map_add, inner_conj_symm]

lemma h1Pair_self (u : ComplexH1) : h1Pair u u = (‖u‖ ^ 2 : ℝ) := by
  simp only [h1Pair, mass, dirichlet, inner_self_eq_norm_sq_to_K]
  change (‖valueCLM u‖ : ℂ) ^ 2 + ((‖dxLp u‖ : ℂ) ^ 2 + (‖dyLp u‖ : ℂ) ^ 2) = _
  rw [coordinate_graph_norm_sq]
  push_cast
  ring

/-- The real part of the complex pairing equals the inherited real inner product. -/
lemma h1Pair_re (u v : ComplexH1) : (h1Pair u v).re = inner ℝ u v := by
  have h := congrArg Complex.re (h1Pair_self (u + v))
  rw [h1Pair_add_left, h1Pair_add_right, h1Pair_add_right,
    h1Pair_self, h1Pair_self] at h
  have hc := congrArg Complex.re (h1Pair_conj u v)
  simp only [Complex.add_re, Complex.ofReal_re] at h
  simp only [Complex.conj_re] at hc
  have hn := norm_add_sq_real u v
  nlinarith

instance instComplexInnerProductSpace : InnerProductSpace ℂ ComplexH1 where
  inner := h1Pair
  norm_sq_eq_re_inner u := by rw [h1Pair_self]; rfl
  conj_inner_symm := h1Pair_conj
  add_left := h1Pair_add_left
  smul_left u v z := h1Pair_smul_left z u v

lemma complex_inner_eq_h1Pair (u v : ComplexH1) : inner ℂ u v = h1Pair u v := rfl

lemma continuous_h1Pair : Continuous (fun p : ComplexH1 × ComplexH1 => h1Pair p.1 p.2) :=
  continuous_inner (𝕜 := ℂ) (E := ComplexH1)

lemma norm_h1Pair_le (u v : ComplexH1) : ‖h1Pair u v‖ ≤ ‖u‖ * ‖v‖ :=
  norm_inner_le_norm (𝕜 := ℂ) u v

/-- A real potential with an a.e.-strongly measurable representative and an a.e. bound. -/
structure BoundedRealPotential where
  V : ℂ → ℝ
  C : ℝ
  nonneg : 0 ≤ C
  measurable : AEStronglyMeasurable V (volume.restrict (disk : Set ℂ))
  bound : ∀ᵐ x ∂volume.restrict (disk : Set ℂ), |V x| ≤ C

lemma weighted_memLp (V : BoundedRealPotential) (f : L2C) :
    MemLp (fun x => (V.V x : ℂ) * f x) 2 (volume.restrict (disk : Set ℂ)) := by
  apply (Lp.memLp f).of_le_mul (c := V.C)
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable V.measurable).mul
      (Lp.memLp f).aestronglyMeasurable)
  filter_upwards [V.bound] with x hx
  simpa only [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_right hx (norm_nonneg (f x))

def weightedLp (V : BoundedRealPotential) (f : L2C) : L2C := (weighted_memLp V f).toLp _
lemma weightedLp_ae (V : BoundedRealPotential) (f : L2C) :
    weightedLp V f =ᵐ[volume.restrict (disk : Set ℂ)] fun x => (V.V x : ℂ) * f x :=
  MemLp.coeFn_toLp _

lemma weightedLp_add (V : BoundedRealPotential) (f g : L2C) :
    weightedLp V (f + g) = weightedLp V f + weightedLp V g := by
  apply Lp.ext
  filter_upwards [weightedLp_ae V (f + g), weightedLp_ae V f, weightedLp_ae V g,
    Lp.coeFn_add f g, Lp.coeFn_add (weightedLp V f) (weightedLp V g)] with x h hf hg ha hb
  simp only [h, hb, Pi.add_apply, hf, hg, ha, mul_add]

lemma weightedLp_smul (V : BoundedRealPotential) (z : ℂ) (f : L2C) :
    weightedLp V (z • f) = z • weightedLp V f := by
  apply Lp.ext
  filter_upwards [weightedLp_ae V (z • f), weightedLp_ae V f,
    Lp.coeFn_smul z f, Lp.coeFn_smul z (weightedLp V f)] with x h hf ha hb
  simp only [h, hb, Pi.smul_apply, hf, ha, smul_eq_mul]
  ring

lemma norm_weightedLp_le (V : BoundedRealPotential) (f : L2C) :
    ‖weightedLp V f‖ ≤ V.C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [weightedLp_ae V f, V.bound] with x hx hV
  rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hV (norm_nonneg _)

def weightedCLM (V : BoundedRealPotential) : L2C →L[ℂ] L2C :=
  LinearMap.mkContinuous
    { toFun := weightedLp V
      map_add' := weightedLp_add V
      map_smul' := weightedLp_smul V }
    V.C (fun f => norm_weightedLp_le V f)

def potential (V : BoundedRealPotential) (u v : ComplexH1) : ℂ :=
  inner ℂ (valueCLM u) (weightedCLM V (valueCLM v))
def weakJacobi (V : BoundedRealPotential) (u v : ComplexH1) : ℂ :=
  dirichlet u v - potential V u v

lemma potential_integrable (V : BoundedRealPotential) (u v : ComplexH1) :
    Integrable (fun x => (V.V x : ℂ) * (starRingEnd ℂ) (valueCLM u x) * valueCLM v x)
      (volume.restrict (disk : Set ℂ)) := by
  apply (L2.integrable_inner (𝕜 := ℂ) (valueCLM u) (weightedLp V (valueCLM v))).congr
  filter_upwards [weightedLp_ae V (valueCLM v)] with x hx
  simp only [RCLike.inner_apply, hx]
  ring

lemma potential_integral (V : BoundedRealPotential) (u v : ComplexH1) :
    potential V u v = ∫ x in (disk : Set ℂ),
      (V.V x : ℂ) * (starRingEnd ℂ) (valueCLM u x) * valueCLM v x := by
  rw [potential, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [weightedLp_ae V (valueCLM v)] with x hx
  change inner ℂ (valueCLM u x) (weightedLp V (valueCLM v) x) = _
  rw [hx, RCLike.inner_apply]
  ring

lemma potential_conj (V : BoundedRealPotential) (u v : ComplexH1) :
    (starRingEnd ℂ) (potential V v u) = potential V u v := by
  rw [potential_integral, potential_integral, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring

lemma weakJacobi_add_left (V : BoundedRealPotential) (u v w : ComplexH1) :
    weakJacobi V (u + v) w = weakJacobi V u w + weakJacobi V v w := by
  simp only [weakJacobi, dirichlet, potential, map_add, inner_add_left]
  ring
lemma weakJacobi_add_right (V : BoundedRealPotential) (u v w : ComplexH1) :
    weakJacobi V u (v + w) = weakJacobi V u v + weakJacobi V u w := by
  simp only [weakJacobi, dirichlet, potential, map_add, inner_add_right]
  ring
lemma weakJacobi_smul_left (V : BoundedRealPotential) (z : ℂ) (u v : ComplexH1) :
    weakJacobi V (z • u) v = (starRingEnd ℂ) z * weakJacobi V u v := by
  simp only [weakJacobi, dirichlet, potential, map_smul, inner_smul_left]
  ring
lemma weakJacobi_smul_right (V : BoundedRealPotential) (z : ℂ) (u v : ComplexH1) :
    weakJacobi V u (z • v) = z * weakJacobi V u v := by
  simp only [weakJacobi, dirichlet, potential, map_smul, inner_smul_right]
  ring
lemma weakJacobi_conj (V : BoundedRealPotential) (u v : ComplexH1) :
    (starRingEnd ℂ) (weakJacobi V v u) = weakJacobi V u v := by
  simp only [weakJacobi, map_sub, potential_conj, dirichlet, map_add, inner_conj_symm]

lemma weakJacobi_self_im (V : BoundedRealPotential) (u : ComplexH1) :
    (weakJacobi V u u).im = 0 := by
  have h := congrArg Complex.im (weakJacobi_conj V u u)
  simp only [Complex.conj_im] at h
  linarith

lemma norm_potential_le (V : BoundedRealPotential) (u v : ComplexH1) :
    ‖potential V u v‖ ≤ V.C * ‖u‖ * ‖v‖ := by
  calc
    _ ≤ ‖valueCLM u‖ * ‖weightedLp V (valueCLM v)‖ := norm_inner_le_norm _ _
    _ ≤ ‖valueCLM u‖ * (V.C * ‖valueCLM v‖) :=
      mul_le_mul_of_nonneg_left (norm_weightedLp_le V _) (norm_nonneg _)
    _ ≤ ‖u‖ * (V.C * ‖v‖) := by
      exact mul_le_mul (norm_valueLp_le u)
        (mul_le_mul_of_nonneg_left (norm_valueLp_le v) V.nonneg)
        (mul_nonneg V.nonneg (norm_nonneg _)) (norm_nonneg u)
    _ = _ := by ring

lemma norm_weakJacobi_le (V : BoundedRealPotential) (u v : ComplexH1) :
    ‖weakJacobi V u v‖ ≤ (2 + V.C) * ‖u‖ * ‖v‖ := by
  have hd : ‖dirichlet u v‖ ≤ 2 * ‖u‖ * ‖v‖ := by
    calc
      _ ≤ ‖inner ℂ (dxCLM u) (dxCLM v)‖ + ‖inner ℂ (dyCLM u) (dyCLM v)‖ := norm_add_le _ _
      _ ≤ ‖dxLp u‖ * ‖dxLp v‖ + ‖dyLp u‖ * ‖dyLp v‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ ≤ ‖u‖ * ‖v‖ + ‖u‖ * ‖v‖ := by
        gcongr
        · exact norm_dxLp_le u
        · exact norm_dxLp_le v
        · exact norm_dyLp_le u
        · exact norm_dyLp_le v
      _ = _ := by ring
  exact (norm_sub_le _ _).trans (by linarith [norm_potential_le V u v])

lemma continuous_weakJacobi (V : BoundedRealPotential) :
    Continuous (fun p : ComplexH1 × ComplexH1 => weakJacobi V p.1 p.2) := by
  unfold weakJacobi dirichlet potential
  fun_prop

/-- All hypotheses concern the open disk; no smoothness across its boundary. -/
structure SmoothH1Data where
  F : ℂ → ℂ
  smooth : ContDiffOn ℝ ∞ F (disk : Set ℂ)
  value_mem : MemLp F 2 (volume.restrict (disk : Set ℂ))
  dx_mem : MemLp (fun x => fderiv ℝ F x 1) 2 (volume.restrict (disk : Set ℂ))
  dy_mem : MemLp (fun x => fderiv ℝ F x Complex.I) 2 (volume.restrict (disk : Set ℂ))

lemma smooth_hasWeak (F : SmoothH1Data) :
    HasWeakFDerivOn volume disk F.F (fderiv ℝ F.F) := by
  apply hasWeakFDerivOn_of_differentiableOn
  · exact F.smooth.continuousOn.locallyIntegrableOn disk.isOpen.measurableSet
  · exact (F.smooth.continuousOn_fderiv_of_isOpen disk.isOpen (by simp)).locallyIntegrableOn
      disk.isOpen.measurableSet
  · intro x hx
    exact (F.smooth.differentiableOn (by simp)).differentiableAt (disk.isOpen.mem_nhds hx)

lemma smooth_hasJet (F : SmoothH1Data) :
    HasComplexH1Jet (F.value_mem.toLp F.F) (F.dx_mem.toLp _) (F.dy_mem.toLp _) := by
  apply ((smooth_hasWeak F).congr_ae (MemLp.coeFn_toLp F.value_mem).symm).congr_ae_deriv
  filter_upwards [MemLp.coeFn_toLp F.dx_mem, MemLp.coeFn_toLp F.dy_mem] with x hx hy
  ext v
  rw [Dxy_apply, hx, hy]
  exact realLinear_coordinates (fderiv ℝ F.F x) v

def smoothToH1 (F : SmoothH1Data) : ComplexH1 :=
  reconstruct (F.value_mem.toLp F.F) (F.dx_mem.toLp _) (F.dy_mem.toLp _) (smooth_hasJet F)

lemma smoothToH1_coordinates (F : SmoothH1Data) :
    valueCLM (smoothToH1 F) = F.value_mem.toLp F.F ∧
      dxLp (smoothToH1 F) = F.dx_mem.toLp _ ∧ dyLp (smoothToH1 F) = F.dy_mem.toLp _ := by
  have hv : valueCLM (smoothToH1 F) = F.value_mem.toLp F.F := reconstruct_value _ _ _ _
  refine ⟨hv, ?_⟩
  apply jet_derivatives_unique (h' := smooth_hasJet F)
  rw [← hv]
  exact carrier_hasJet _

lemma smoothToH1_value_ae (F : SmoothH1Data) :
    valueCLM (smoothToH1 F) =ᵐ[volume.restrict (disk : Set ℂ)] F.F := by
  rw [(smoothToH1_coordinates F).1]
  exact MemLp.coeFn_toLp _
lemma smoothToH1_dx_ae (F : SmoothH1Data) :
    dxCLM (smoothToH1 F) =ᵐ[volume.restrict (disk : Set ℂ)] fun x => fderiv ℝ F.F x 1 := by
  change dxLp (smoothToH1 F) =ᵐ[_] _
  rw [(smoothToH1_coordinates F).2.1]
  exact MemLp.coeFn_toLp _
lemma smoothToH1_dy_ae (F : SmoothH1Data) :
    dyCLM (smoothToH1 F) =ᵐ[volume.restrict (disk : Set ℂ)] fun x => fderiv ℝ F.F x Complex.I := by
  change dyLp (smoothToH1 F) =ᵐ[_] _
  rw [(smoothToH1_coordinates F).2.2]
  exact MemLp.coeFn_toLp _

lemma dirichlet_integrable (u v : ComplexH1) :
    Integrable (fun x => (starRingEnd ℂ) (dxCLM u x) * dxCLM v x +
      (starRingEnd ℂ) (dyCLM u x) * dyCLM v x) (volume.restrict (disk : Set ℂ)) := by
  apply ((L2.integrable_inner (𝕜 := ℂ) (dxCLM u) (dxCLM v)).add
    (L2.integrable_inner (𝕜 := ℂ) (dyCLM u) (dyCLM v))).congr
  filter_upwards with x
  simp only [Pi.add_apply, RCLike.inner_apply]
  exact congrArg₂ (· + ·) (mul_comm _ _) (mul_comm _ _)

lemma dirichlet_integral (u v : ComplexH1) :
    dirichlet u v = ∫ x in (disk : Set ℂ),
      (starRingEnd ℂ) (dxCLM u x) * dxCLM v x +
      (starRingEnd ℂ) (dyCLM u x) * dyCLM v x := by
  rw [dirichlet, L2.inner_def, L2.inner_def,
    ← integral_add (L2.integrable_inner (𝕜 := ℂ) _ _) (L2.integrable_inner (𝕜 := ℂ) _ _)]
  apply integral_congr_ae
  filter_upwards with x
  simp only [RCLike.inner_apply]
  exact congrArg₂ (· + ·) (mul_comm _ _) (mul_comm _ _)

/-- Explicit representative invariance of both terms of the form. -/
lemma weakJacobi_integral_representatives (V : BoundedRealPotential) (u v : ComplexH1)
    {f g a b c d : ℂ → ℂ}
    (hf : valueCLM u =ᵐ[volume.restrict (disk : Set ℂ)] f)
    (hg : valueCLM v =ᵐ[volume.restrict (disk : Set ℂ)] g)
    (ha : dxCLM u =ᵐ[volume.restrict (disk : Set ℂ)] a)
    (hb : dyCLM u =ᵐ[volume.restrict (disk : Set ℂ)] b)
    (hc : dxCLM v =ᵐ[volume.restrict (disk : Set ℂ)] c)
    (hd : dyCLM v =ᵐ[volume.restrict (disk : Set ℂ)] d) :
    weakJacobi V u v =
      (∫ x in (disk : Set ℂ), (starRingEnd ℂ) (a x) * c x + (starRingEnd ℂ) (b x) * d x) -
      ∫ x in (disk : Set ℂ), (V.V x : ℂ) * (starRingEnd ℂ) (f x) * g x := by
  rw [weakJacobi, dirichlet_integral, potential_integral]
  congr 1
  · apply integral_congr_ae
    filter_upwards [ha, hb, hc, hd] with x h1 h2 h3 h4
    rw [h1, h2, h3, h4]
  · apply integral_congr_ae
    filter_upwards [hf, hg] with x h1 h2
    rw [h1, h2]

lemma potential_congr_ae (V W : BoundedRealPotential)
    (h : V.V =ᵐ[volume.restrict (disk : Set ℂ)] W.V) (u v : ComplexH1) :
    potential V u v = potential W u v := by
  rw [potential_integral, potential_integral]
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

lemma smooth_classical_gradient_integrable (F G : SmoothH1Data) :
    Integrable (fun x => (starRingEnd ℂ) (fderiv ℝ F.F x 1) * fderiv ℝ G.F x 1 +
      (starRingEnd ℂ) (fderiv ℝ F.F x Complex.I) * fderiv ℝ G.F x Complex.I)
      (volume.restrict (disk : Set ℂ)) := by
  apply (dirichlet_integrable (smoothToH1 F) (smoothToH1 G)).congr
  filter_upwards [smoothToH1_dx_ae F, smoothToH1_dy_ae F,
    smoothToH1_dx_ae G, smoothToH1_dy_ae G] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]

lemma smooth_classical_potential_integrable (V : BoundedRealPotential) (F G : SmoothH1Data) :
    Integrable (fun x => (V.V x : ℂ) * (starRingEnd ℂ) (F.F x) * G.F x)
      (volume.restrict (disk : Set ℂ)) := by
  apply (potential_integrable V (smoothToH1 F) (smoothToH1 G)).congr
  filter_upwards [smoothToH1_value_ae F, smoothToH1_value_ae G] with x h1 h2
  rw [h1, h2]

/-- Agreement with the classical gradient-minus-potential integral for smooth
functions whose values and coordinate derivatives are L² on the open disk. -/
theorem smooth_weakJacobi_eq_classical (V : BoundedRealPotential) (F G : SmoothH1Data) :
    weakJacobi V (smoothToH1 F) (smoothToH1 G) =
      (∫ x in (disk : Set ℂ),
        (starRingEnd ℂ) (fderiv ℝ F.F x 1) * fderiv ℝ G.F x 1 +
        (starRingEnd ℂ) (fderiv ℝ F.F x Complex.I) * fderiv ℝ G.F x Complex.I) -
      ∫ x in (disk : Set ℂ), (V.V x : ℂ) * (starRingEnd ℂ) (F.F x) * G.F x :=
  weakJacobi_integral_representatives V _ _ (smoothToH1_value_ae F) (smoothToH1_value_ae G)
    (smoothToH1_dx_ae F) (smoothToH1_dy_ae F) (smoothToH1_dx_ae G) (smoothToH1_dy_ae G)

lemma mass_add_left (u v w : ComplexH1) : mass (u + v) w = mass u w + mass v w := by
  simp only [mass, map_add, inner_add_left]
lemma mass_add_right (u v w : ComplexH1) : mass u (v + w) = mass u v + mass u w := by
  simp only [mass, map_add, inner_add_right]
lemma mass_smul_left (z : ℂ) (u v : ComplexH1) :
    mass (z • u) v = (starRingEnd ℂ) z * mass u v := by
  simp only [mass, map_smul, inner_smul_left]
lemma mass_smul_right (z : ℂ) (u v : ComplexH1) : mass u (z • v) = z * mass u v := by
  simp only [mass, map_smul, inner_smul_right]
lemma mass_conj (u v : ComplexH1) : (starRingEnd ℂ) (mass v u) = mass u v := by
  simp only [mass, inner_conj_symm]
lemma continuous_mass : Continuous (fun p : ComplexH1 × ComplexH1 => mass p.1 p.2) := by
  unfold mass
  fun_prop
lemma dirichlet_add_left (u v w : ComplexH1) :
    dirichlet (u + v) w = dirichlet u w + dirichlet v w := by
  simp only [dirichlet, map_add, inner_add_left]
  ring
lemma dirichlet_add_right (u v w : ComplexH1) :
    dirichlet u (v + w) = dirichlet u v + dirichlet u w := by
  simp only [dirichlet, map_add, inner_add_right]
  ring
lemma dirichlet_smul_left (z : ℂ) (u v : ComplexH1) :
    dirichlet (z • u) v = (starRingEnd ℂ) z * dirichlet u v := by
  simp only [dirichlet, map_smul, inner_smul_left]
  ring
lemma dirichlet_smul_right (z : ℂ) (u v : ComplexH1) :
    dirichlet u (z • v) = z * dirichlet u v := by
  simp only [dirichlet, map_smul, inner_smul_right]
  ring
lemma dirichlet_conj (u v : ComplexH1) :
    (starRingEnd ℂ) (dirichlet v u) = dirichlet u v := by
  simp only [dirichlet, map_add, inner_conj_symm]
lemma continuous_dirichlet : Continuous (fun p : ComplexH1 × ComplexH1 => dirichlet p.1 p.2) := by
  unfold dirichlet
  fun_prop

end KsIndex.WeakH1
