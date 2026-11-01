module

public import KsIndexLean.JacobiProfileBound
public import KsIndexLean.JacobiModeRotation
public import KsIndexLean.JacobiShiftCoercivity

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Radial KsIndex.DtNCircle

lemma normalizedJacobiMode_pointwise_bound {k : ℕ} (hk : 2 ≤ k) (n : NZ)
    {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖(n.val.natAbs : ℂ)⁻¹ * signedModeU k n w‖ ≤ (k : ℝ) := by
  have hm : 1 ≤ n.val.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr n.property)
  have hm0 : (0 : ℝ) < n.val.natAbs := by exact_mod_cast (by omega : 0 < n.val.natAbs)
  have hf : ‖fourierAmbient n w‖ = ‖w‖ ^ n.val.natAbs := by
    obtain ⟨n, hn⟩ := n
    cases n <;> simp [fourierAmbient, norm_pow]
  have hb := abs_phiExt_le hk hm (norm_nonneg w) hw
  have hr := pow_le_one₀ (norm_nonneg w) hw (n := n.val.natAbs)
  rw [signedModeU_eq_radial_fourier, norm_mul, norm_inv, Complex.norm_natCast,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, hf]
  have he : |JacobiExtension.phiExt k n.val.natAbs ‖w‖| =
      (n.val.natAbs : ℝ)⁻¹ * (|gRad k n.val.natAbs ‖w‖| * ‖w‖ ^ n.val.natAbs) := by
    rw [JacobiExtension.phiExt, uRad, abs_div, abs_mul,
      abs_of_nonneg (pow_nonneg (norm_nonneg w) _), abs_of_pos hm0]
    ring
  rw [← he]
  exact hb.trans (by nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k])

/-- A fixed reference norm avoids any dependence on the number or sizes of frequencies. -/
def jacobiModeL2Bound (k : ℕ) : ℝ :=
  (k : ℝ) * ‖valueCLM (globalSmoothH1 (fun _ => (1 : ℂ)) contDiff_const)‖

lemma normalizedJacobiMode_value_bound {k : ℕ} (hk : 2 ≤ k) (n : NZ) :
    ‖valueCLM (normalizedJacobiMode hk n)‖ ≤ jacobiModeL2Bound k := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  rw [normalizedJacobiMode, map_smul]
  filter_upwards [Lp.coeFn_smul (n.val.natAbs : ℂ)⁻¹
      (valueCLM (globalSmoothH1 (signedModeU k n) (signedModeU_smooth hk n))),
    globalSmoothH1_value (signedModeU k n) (signedModeU_smooth hk n),
    globalSmoothH1_value (fun _ => (1 : ℂ)) contDiff_const,
    ae_restrict_mem (disk.isOpen.measurableSet)] with w hs hu h1 hw
  rw [hs, Pi.smul_apply, smul_eq_mul, hu, h1, norm_one, mul_one]
  exact normalizedJacobiMode_pointwise_bound hk n
    (le_of_lt (KsIndex.SurfaceForm.mem_disk_iff.mp hw))

def jacobiModeH1Constant (k : ℕ) : ℝ :=
  2 * Real.pi + ((surfacePotential k).C + 1) * jacobiModeL2Bound k ^ 2

lemma jacobiModeH1Constant_nonneg (k : ℕ) : 0 ≤ jacobiModeH1Constant k := by
  unfold jacobiModeH1Constant
  have := (surfacePotential k).nonneg
  positivity

/-- Linear frequency growth of the squared H1 norm, with an explicit finite constant. -/
lemma normalizedJacobiMode_norm_sq_le {k : ℕ} (hk : 2 ≤ k) (n : NZ) :
    ‖normalizedJacobiMode hk n‖ ^ 2 ≤ jacobiModeH1Constant k * (1 + |(n.val : ℝ)|) := by
  have hb := normalizedJacobiMode_value_bound hk n
  have hM : ‖valueCLM (normalizedJacobiMode hk n)‖ ^ 2 ≤ jacobiModeL2Bound k ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb 2
  have h := weakJacobi_shift_coercive (surfacePotential k) (normalizedJacobiMode hk n) hM
  rw [normalizedJacobiMode_pairing] at h
  simp only [Pi.single_eq_same, mul_one] at h
  have hr : ((2 * Real.pi : ℂ) * (dtnSymbol k n : ℂ)).re = 2 * Real.pi * dtnSymbol k n := by
    simp [Complex.mul_re]
  rw [hr] at h
  have hs : dtnSymbol k n ≤ |(n.val : ℝ)| := by
    rw [dtnSymbol, div_le_iff₀ (absval_pos n)]
    nlinarith [sq_abs (n.val : ℝ), sq_nonneg ((k : ℝ) - 1)]
  have hc : 0 ≤ ((surfacePotential k).C + 1) * jacobiModeL2Bound k ^ 2 := by
    have := (surfacePotential k).nonneg
    positivity
  unfold jacobiModeH1Constant
  nlinarith [Real.pi_pos, mul_nonneg hc (abs_nonneg (n.val : ℝ))]

end KsIndex.Trace
