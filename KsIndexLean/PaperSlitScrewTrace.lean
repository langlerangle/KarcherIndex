module

public import KsIndexLean.PaperSlitAdapterAssembly
public import KsIndexLean.CircleFourierRotation
public import KsIndexLean.DiskTraceCovariance

@[expose] public section


/-! The phase factor relating a rotated upper slit trace to the circle involution.
The statement concerns the analytic slit pair; geometric pullback identification
is a separate transport through the disk-copy encoding. -/
noncomputable section
open MeasureTheory KsIndex.Trace KsIndex.WeakH1 KsIndex.Sector
namespace KsIndex.PaperSlitAdapter

private lemma fourier_screw_class (n r : ℤ) :
    fourier (6*n+r) ((-Real.pi/3 : ℝ) : AddCircle (2*Real.pi)) =
      Complex.exp ((r : ℂ) * (-(Real.pi : ℂ)/3) * Complex.I) := by
  rw [fourier_coe_apply]
  have he : (2 * Real.pi * Complex.I * (6 * n + r) * (-Real.pi / 3) / (2 * Real.pi) : ℂ) =
      ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) +
        (r : ℂ) * (-(Real.pi : ℂ)/3) * Complex.I := by
    push_cast
    field_simp
    ring
  calc
    _ = Complex.exp (((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) +
        (r : ℂ) * (-(Real.pi : ℂ)/3) * Complex.I) := by
      congr 1
      convert he using 1
      push_cast
      ring
    _ = _ := by rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

private lemma fourier_screw_four (n : ℤ) :
    fourier (6*n+4) ((-Real.pi/3 : ℝ) : AddCircle (2*Real.pi)) =
      -Complex.exp (-(Real.pi : ℂ)/3 * Complex.I) := by
  rw [fourier_screw_class]
  have he : (4 : ℂ) * (-(Real.pi : ℂ)/3) * Complex.I =
      -(Real.pi : ℂ)/3 * Complex.I + -(Real.pi : ℂ) * Complex.I := by ring
  norm_num only [Int.cast_ofNat]
  rw [he, Complex.exp_add]
  have hm : Complex.exp (-(Real.pi : ℂ) * Complex.I) = -1 := by
    rw [neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  rw [hm, mul_neg_one]

/-- The negative half-angle shift is a scalar multiple of sector parity. -/
lemma screw_rotation_coeff (f : Lp ℂ 2 circleMeasure) :
    (fun i : Idx => circleFourierCoeff (boundaryRotation (-Real.pi/3) f) (idxToNZ i).val) =
      Complex.exp (-(Real.pi : ℂ)/3 * Complex.I) •
        parity (fun i : Idx => circleFourierCoeff f (idxToNZ i).val) := by
  funext i
  have hc := circleFourierCLE_boundaryRotation (-Real.pi/3) f (idxToNZ i).val
  simp only [circleFourierCLE_apply] at hc
  rw [hc]
  cases i with
  | inl n =>
    simp only [idxToNZ_inl_val, fourier_screw_class, Int.cast_one, one_mul,
      Pi.smul_apply, smul_eq_mul, parity_inl]
  | inr n =>
    simp only [idxToNZ_inr_val, fourier_screw_four, Pi.smul_apply, smul_eq_mul, parity_inr]
    ring

/-- The rotated upper weak trace equals the phase-scaled involution of the lower trace.
This is the analytic slit-pair identity, before transport from geometric functions. -/
theorem rotated_upper_trace_eq_rop {α : ℝ} {j : ℕ} (hj : j % 3 = 2)
    (u : paperSlitCharacterDomain α j) :
    (fun i : Idx => circleFourierCoeff
      (diskTraceCLM (diskRotation (-Real.pi/3) u.val.1)) (idxToNZ i).val) =
      (-(Complex.exp (-(Real.pi : ℂ)/3 * Complex.I) *
        Complex.exp (Complex.I * (α * Real.pi)))) •
        rop α (fun i : Idx => circleFourierCoeff (diskTraceCLM u.val.2) (idxToNZ i).val) := by
  rw [diskTrace_rotation, screw_rotation_coeff, paperSlit_seam_coeff_eq_mulA hj u,
    parity_smul, ← mulAdag_parity]
  simp only [rop, smul_neg, neg_smul, neg_neg, smul_smul]

/-- The normalization phase in the j=2 character convention. -/
lemma screw_trace_phase (α : ℝ) :
    -(Complex.exp (-(Real.pi : ℂ)/3 * Complex.I) *
      Complex.exp (Complex.I * (α * Real.pi))) =
      Complex.exp (Complex.I * (Real.pi * (α + 2/3))) := by
  calc
    _ = Complex.exp ((Real.pi : ℂ) * Complex.I) *
        (Complex.exp (-(Real.pi : ℂ)/3 * Complex.I) *
          Complex.exp (Complex.I * (α * Real.pi))) := by
      rw [Complex.exp_pi_mul_I, neg_one_mul]
    _ = _ := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      ring

/-- Exact phase-normalized trace comparison, on the analytic paper slit domain. -/
theorem rotated_upper_trace_eq_phase_rop {α : ℝ} {j : ℕ} (hj : j % 3 = 2)
    (u : paperSlitCharacterDomain α j) :
    (fun i : Idx => circleFourierCoeff
      (diskTraceCLM (diskRotation (-Real.pi/3) u.val.1)) (idxToNZ i).val) =
      Complex.exp (Complex.I * (Real.pi * (α + 2/3))) •
        rop α (fun i : Idx => circleFourierCoeff (diskTraceCLM u.val.2) (idxToNZ i).val) := by
  rw [rotated_upper_trace_eq_rop hj u, screw_trace_phase]

end KsIndex.PaperSlitAdapter
