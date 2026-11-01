module

public import KsIndexLean.NodeCPsi
public import KsIndexLean.ArcWitness
public import KsIndexLean.FourierMode

@[expose] public section


/-!
# Fourier coefficients and the mixed-boundary trial pairing

The circle Fourier coefficients of `1 − conj w` are `δ_{n,0} − δ_{n,-1}`.
For `u ∈ dnSpace 1`, the trial function has the same pairing with `u` as this
trigonometric polynomial: the two integrands agree on the right semicircle,
and `u` vanishes almost everywhere on the left semicircle.

With the unnormalized circle measure, the resulting identity is
`⟨Ψ, u⟩ = 2π · (û(0) − û(−1))`. The inner product conjugates its first argument.
The proof identifies angular and circle Fourier coefficients and uses the
`H^{-1/2}` dual element supported at indices `0` and `-1`.

-/

noncomputable section
open MeasureTheory Complex
namespace KsIndex.NodeC
open KsIndex.Trace KsIndex.Parseval KsIndex.CircleSobolev KsIndex.WeakH1

/-- `circleFourierCoeff` is `fc` of the angular pullback (same `fourierCoeffOn`). -/
lemma circleFourierCoeff_eq_fc (f : Circle₁ → ℂ) (n : ℤ) :
    circleFourierCoeff f n = fc (fun θ => f (circleParam θ)) n := by
  unfold circleFourierCoeff
  rw [fc_eq_fourierCoeffOn]

/-- The constant function's Fourier coefficient is `δ_{n,0}`. -/
lemma fc_one (n : ℤ) : fc (fun _ : ℝ => (1 : ℂ)) n = if n = 0 then 1 else 0 := by
  unfold fc
  simp only [one_mul]
  split_ifs with h
  · subst h
    simp only [Int.cast_zero, neg_zero, zero_mul, Complex.exp_zero,
      intervalIntegral.integral_const, sub_zero]
    rw [Complex.real_smul, mul_one, ← Complex.ofReal_mul,
      inv_mul_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), Complex.ofReal_one]
  · rw [KsIndex.FourierMode.integral_exp_period n h, mul_zero]

/-- `conj (circleParam θ) = e^{-θ i}` in the `((-1)·i·θ)` normal form. -/
lemma conj_circleParam (θ : ℝ) :
    (starRingEnd ℂ) (circleParam θ : ℂ) = Complex.exp (((-1 : ℤ) : ℂ) * Complex.I * θ) := by
  rw [circleParam_coe, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Int.cast_neg, Int.cast_one]
  ring

/-- `conj w`'s Fourier coefficient is `δ_{n,-1}`. -/
lemma fc_conj_circleParam (n : ℤ) :
    fc (fun θ => (starRingEnd ℂ) (circleParam θ : ℂ)) n = if n = -1 then 1 else 0 := by
  have hcong : ∀ θ : ℝ, (starRingEnd ℂ) (circleParam θ : ℂ) *
      Complex.exp (-((n : ℤ) : ℂ) * Complex.I * θ)
      = Complex.exp (-(((n + 1 : ℤ)) : ℂ) * Complex.I * θ) := by
    intro θ
    rw [conj_circleParam, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold fc
  rw [intervalIntegral.integral_congr (fun θ _ => hcong θ)]
  split_ifs with h
  · rw [show n + 1 = 0 by omega]
    simp only [Int.cast_zero, neg_zero, zero_mul, Complex.exp_zero,
      intervalIntegral.integral_const, sub_zero]
    rw [Complex.real_smul, mul_one, ← Complex.ofReal_mul,
      inv_mul_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), Complex.ofReal_one]
  · rw [KsIndex.FourierMode.integral_exp_period (n + 1) (by omega), mul_zero]

/-- `circleFourierCoeff (1 − conj w) n = δ_{n,0} − δ_{n,-1}`. -/
lemma circleFourierCoeff_one_sub_conj (n : ℤ) :
    circleFourierCoeff (fun w : Circle₁ => 1 - (starRingEnd ℂ) (w : ℂ)) n
      = (if n = 0 then 1 else 0) - (if n = -1 then 1 else 0) := by
  rw [circleFourierCoeff_eq_fc]
  show fc (fun θ => (1 : ℂ) - (starRingEnd ℂ) (circleParam θ : ℂ)) n = _
  have hc1 : Continuous (fun _ : ℝ => (1 : ℂ)) := continuous_const
  have hc2 : Continuous (fun θ : ℝ => (starRingEnd ℂ) (circleParam θ : ℂ)) :=
    Complex.continuous_conj.comp (continuous_subtype_val.comp continuous_circleParam)
  rw [KsIndex.ArcWitness.fc_sub hc1 hc2, fc_one, fc_conj_circleParam]

/-! ### The pairing identity `û(0) − û(−1) = (1/2π)⟨Ψ, u⟩` for DN data -/


/-- The `L²` realization of the trial function. -/
def trialPsiLp : Lp ℂ 2 circleMeasure := trialPsi_memLp.toLp trialPsi

/-- The trig polynomial `1 − conj w` is in `L²`. -/
lemma oneSubConj_memLp :
    MemLp (fun w : Circle₁ => 1 - (starRingEnd ℂ) (w : ℂ)) 2 circleMeasure := by
  have hcont : Continuous (fun w : Circle₁ => 1 - (starRingEnd ℂ) (w : ℂ)) :=
    continuous_const.sub (Complex.continuous_conj.comp continuous_subtype_val)
  refine MemLp.of_bound hcont.aestronglyMeasurable 2 ?_
  filter_upwards with w
  have hw : ‖(w : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
  calc ‖1 - (starRingEnd ℂ) (w : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖(starRingEnd ℂ) (w : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_one, starRingEnd_apply, norm_star, hw]; norm_num

/-- Its `L²` realization. -/
def oneSubConjLp : Lp ℂ 2 circleMeasure := oneSubConj_memLp.toLp _

lemma circleFourierCoeff_oneSubConjLp (n : ℤ) :
    circleFourierCoeff (oneSubConjLp : Circle₁ → ℂ) n
      = (if n = 0 then 1 else 0) - (if n = -1 then 1 else 0) := by
  have hae : (oneSubConjLp : Circle₁ → ℂ) =ᵐ[circleMeasure]
      (fun w => 1 - (starRingEnd ℂ) (w : ℂ)) := oneSubConj_memLp.coeFn_toLp
  rw [congrFun (circleFourierCoeff_congr_ae hae) n, circleFourierCoeff_one_sub_conj]

/-- The dual coefficient sequence `δ_{n,0} − δ_{n,-1}` (finite support). -/
def psiDualCoeff (n : ℤ) : ℂ := (if n = 0 then 1 else 0) - (if n = -1 then 1 else 0)

lemma psiDualCoeff_summable :
    Summable (fun n : ℤ => weight (-(1 / 2) : ℝ) n ^ 2 * ‖psiDualCoeff n‖ ^ 2) := by
  apply summable_of_ne_finset_zero (s := ({0, -1} : Finset ℤ))
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  simp [psiDualCoeff, hn.1, hn.2]

/-- The dual element of `H^{-1/2}` with coefficients `δ_{n,0} − δ_{n,-1}`. -/
def psiDual : Space (-(1 / 2) : ℝ) := ofCoefficients (-(1 / 2)) psiDualCoeff psiDualCoeff_summable

lemma psiDual_coeff (n : ℤ) : coeff (-(1 / 2)) psiDual n = psiDualCoeff n :=
  coeff_ofCoefficients _ _ _ n

/-- DN data vanish a.e. on the left semicircle `boundaryArc 1 0` (= `Re w < 0`). -/
lemma dnSpace_vanish_ae (u : Space (1 / 2 : ℝ)) (hu : u ∈ dnSpace 1) :
    ∀ᵐ w ∂circleMeasure, w ∈ boundaryArc 1 0 → (toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) u : Circle₁ → ℂ) w = 0 := by
  have hdn : (toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) u : Circle₁ → ℂ) =ᵐ[circleMeasure.restrict (boundaryArc 1 0)] 0 :=
    (mem_arcZero_iff (by norm_num : (0 : ℝ) ≤ 1 / 2) (boundaryArc 1 0) u).mp hu
  have hdn' : ∀ᵐ w ∂(circleMeasure.restrict (boundaryArc 1 0)),
      (toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) u : Circle₁ → ℂ) w = 0 := hdn
  exact (ae_restrict_iff' (measurableSet_boundaryArc 1 0)).mp hdn'

/-- The `⟨Ψ, ·⟩` and `⟨1 − conj w, ·⟩` integrands agree a.e. against DN data. -/
lemma trialPsi_inner_ae (u : Space (1 / 2 : ℝ)) (hu : u ∈ dnSpace 1) :
    (fun w => inner ℂ ((trialPsiLp : Circle₁ → ℂ) w) ((toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) u : Circle₁ → ℂ) w))
      =ᵐ[circleMeasure]
      (fun w => inner ℂ ((oneSubConjLp : Circle₁ → ℂ) w) ((toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) u : Circle₁ → ℂ) w)) := by
  have hc1 : (trialPsiLp : Circle₁ → ℂ) =ᵐ[circleMeasure] trialPsi := trialPsi_memLp.coeFn_toLp
  have hc2 : (oneSubConjLp : Circle₁ → ℂ) =ᵐ[circleMeasure]
      (fun w => 1 - (starRingEnd ℂ) (w : ℂ)) := oneSubConj_memLp.coeFn_toLp
  filter_upwards [hc1, hc2, dnSpace_vanish_ae u hu] with w h1 h2 h3
  simp only [RCLike.inner_apply', h1, h2]
  by_cases hre : 0 ≤ (w : ℂ).re
  · rw [trialPsi_of_re_nonneg hre]
  · have hmem : w ∈ boundaryArc 1 0 := by rw [mem_boundaryArc]; simpa using not_le.mp hre
    rw [h3 hmem, mul_zero, mul_zero]

/-- **The pairing identity**: for DN data, `⟨Ψ, u⟩ = 2π·(û(0) − û(−1))`. -/
lemma trialPsi_pairing (u : Space (1 / 2 : ℝ)) (hu : u ∈ dnSpace 1) :
    inner ℂ trialPsiLp (toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) u)
      = (2 * Real.pi : ℂ) * (coeff (1 / 2) u 0 - coeff (1 / 2) u (-1)) := by
  have hinner : inner ℂ trialPsiLp (toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) u) = inner ℂ oneSubConjLp (toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) u) := by
    rw [L2.inner_def, L2.inner_def]
    exact integral_congr_ae (trialPsi_inner_ae u hu)
  have hdual : inner ℂ oneSubConjLp (toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) u) = duality (1 / 2) psiDual u := by
    rw [duality_eq_integral_of_coefficients (1 / 2) psiDual u oneSubConjLp (toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) u)
      (fun n => by rw [psiDual_coeff]; exact (circleFourierCoeff_oneSubConjLp n).symm)
      (fun n => (fourierCoeff_toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) u n).symm), L2.inner_def]
    simp only [RCLike.inner_apply']
  rw [hinner, hdual, duality_eq_tsum]
  congr 1
  simp only [psiDual_coeff]
  rw [tsum_eq_sum (s := ({0, -1} : Finset ℤ)) ?_]
  · rw [Finset.sum_pair (by decide : (0 : ℤ) ≠ -1)]
    have e0 : psiDualCoeff 0 = 1 := by simp [psiDualCoeff]
    have e1 : psiDualCoeff (-1) = -1 := by simp [psiDualCoeff]
    rw [e0, e1]
    simp only [map_one, map_neg]
    ring
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [psiDualCoeff, hn.1, hn.2]

end KsIndex.NodeC
