module

public import KsIndexLean.KarcherSectorRotation
public import Mathlib.RingTheory.RootsOfUnity.Complex

@[expose] public section


/-! A finite rotation brings a parameter with nonnegative powered real part
into the fundamental wedge. -/
noncomputable section
namespace KsIndex.KarcherData
open Complex Set

lemma principal_root_arg_bound {k : ℕ} (hk : 2 ≤ k) {u : ℂ} (hu : u ≠ 0)
    (hr : 0 ≤ u.re) :
    (u ^ ((k : ℂ)⁻¹)).arg ∈ Icc (-(Real.pi / (2 * k))) (Real.pi / (2 * k)) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hkpos : (0 : ℝ) < k := by linarith
  have ha := (abs_le.mp (Complex.abs_arg_le_pi_div_two_iff.mpr hr))
  have hm : (Complex.log u * (k : ℂ)⁻¹).im = u.arg / k := by
    simp [Complex.mul_im, Complex.log_im, ← Complex.ofReal_natCast,
      ← Complex.ofReal_inv, div_eq_mul_inv]
  have hl : -(Real.pi / 2) ≤ u.arg / k := by
    apply (le_div_iff₀ hkpos).mpr
    nlinarith [Real.pi_pos]
  have hh : u.arg / k ≤ Real.pi / 2 := by
    apply (div_le_iff₀ hkpos).mpr
    nlinarith [Real.pi_pos]
  have he : (u ^ ((k : ℂ)⁻¹)).arg = u.arg / k := by
    rw [Complex.cpow_def_of_ne_zero hu]
    have hlog := congrArg Complex.im (Complex.log_exp
      (show -Real.pi < (Complex.log u * (k : ℂ)⁻¹).im by rw [hm]; linarith [Real.pi_pos])
      (show (Complex.log u * (k : ℂ)⁻¹).im ≤ Real.pi by rw [hm]; linarith [Real.pi_pos]))
    simpa only [Complex.log_im, hm] using hlog
  rw [he]
  constructor
  · have hh := div_le_div_of_nonneg_right ha.1 hkpos.le
    convert hh using 1; ring
  · have hh := div_le_div_of_nonneg_right ha.2 hkpos.le
    convert hh using 1; ring

lemma exists_rotation_into_wedge {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : 0 ≤ (w ^ k).re) :
    ∃ n : ℕ, n < k ∧
      (Complex.exp (((-2 * Real.pi / k : ℝ) : ℂ) * I) ^ n * w).arg ∈
        Icc (-(Real.pi / (2 * k))) (Real.pi / (2 * k)) := by
  have hk0 : k ≠ 0 := by omega
  let : NeZero k := ⟨hk0⟩
  by_cases hw0 : w = 0
  · refine ⟨0, by omega, ?_⟩
    simp only [hw0, mul_zero, Complex.arg_zero, Set.mem_Icc]
    constructor
    · exact neg_nonpos.mpr (by positivity)
    · positivity
  let v := (w ^ k) ^ ((k : ℂ)⁻¹)
  have hvpow : v ^ k = w ^ k := Complex.cpow_nat_inv_pow _ hk0
  have hvarg := principal_root_arg_bound hk (pow_ne_zero _ hw0) hw
  have hr : (v / w) ^ k = 1 := by
    rw [div_pow, hvpow, div_self (pow_ne_zero _ hw0)]
  have hprim : IsPrimitiveRoot (Complex.exp (((-2 * Real.pi / k : ℝ) : ℂ) * I)) k := by
    have hh := (Complex.isPrimitiveRoot_exp k hk0).inv
    rw [← Complex.exp_neg] at hh
    have he : (((-2 * Real.pi / k : ℝ) : ℂ) * I) = -(2 * Real.pi * I / (k : ℂ)) := by
      push_cast
      ring
    rw [he]
    exact hh
  obtain ⟨n, hn, he⟩ := hprim.eq_pow_of_pow_eq_one hr
  refine ⟨n, hn, ?_⟩
  rw [he, div_mul_cancel₀ _ hw0]
  exact hvarg

end KsIndex.KarcherData
