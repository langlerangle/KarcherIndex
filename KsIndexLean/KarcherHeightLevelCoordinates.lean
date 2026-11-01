module

public import KsIndexLean.KarcherHeightLevelDifferential
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section


/-! Explicit logarithmic coordinates for the fundamental sector.
This module proves the inverse identities and the derivative of the inverse coordinate. -/
noncomputable section
namespace KsIndex.KarcherData
open Complex

def heightSectorCoordinate (k : ℕ) (w : ℂ) : ℂ := Complex.log (heightCayley k w)

def heightSectorParameter (k : ℕ) (ζ : ℂ) : ℂ :=
  heightCayleyInverse (Complex.exp ζ) ^ ((k : ℂ)⁻¹)

lemma heightCayleyInverse_heightCayley {k : ℕ} {w : ℂ}
    (hw : w ∉ Surface.punctures k) : heightCayleyInverse (heightCayley k w) = w ^ k := by
  have hd := (height_factors_ne hw).2
  have he : heightCayley k w + 1 = 2 / (1 - I * w ^ k) := by
    unfold heightCayley
    field_simp
    ring
  unfold heightCayleyInverse
  rw [he]
  unfold heightCayley
  field_simp
  linear_combination -(2 * w ^ k) * Complex.I_sq

/-- The principal kth root gives the exact inverse on the chosen parameter sector. -/
lemma heightSectorParameter_coordinate {k : ℕ} (hk : k ≠ 0) {w : ℂ}
    (hw : w ∉ Surface.punctures k)
    (hlo : -(Real.pi / k) < w.arg) (hhi : w.arg ≤ Real.pi / k) :
    heightSectorParameter k (heightSectorCoordinate k w) = w := by
  unfold heightSectorParameter heightSectorCoordinate
  rw [Complex.exp_log (heightCayley_ne_zero hw), heightCayleyInverse_heightCayley hw]
  exact Complex.pow_cpow_nat_inv hk hlo hhi

lemma heightCayley_sectorParameter {k : ℕ} (hk : k ≠ 0) {ζ : ℂ}
    (hζ : Complex.exp ζ + 1 ≠ 0) :
    heightCayley k (heightSectorParameter k ζ) = Complex.exp ζ := by
  unfold heightCayley heightSectorParameter
  rw [Complex.cpow_nat_inv_pow _ hk]
  exact heightCayleyInverse_apply hζ

lemma heightSectorCoordinate_parameter {k : ℕ} (hk : k ≠ 0) {ζ : ℂ}
    (hζ : Complex.exp ζ + 1 ≠ 0) (hlo : -Real.pi < ζ.im) (hhi : ζ.im ≤ Real.pi) :
    heightSectorCoordinate k (heightSectorParameter k ζ) = ζ := by
  unfold heightSectorCoordinate
  rw [heightCayley_sectorParameter hk hζ]
  exact Complex.log_exp hlo hhi

/-- Interior points of the logarithmic half-strip map to the powered
fundamental sector before taking the principal kth root. -/
lemma heightSector_powered_interior {ζ : ℂ}
    (hs : ζ.re < 0) (ha : 0 < ζ.im) (hb : ζ.im < Real.pi / 2) :
    0 < (heightCayleyInverse (Complex.exp ζ)).re ∧
    0 < (heightCayleyInverse (Complex.exp ζ)).im ∧
      ‖heightCayleyInverse (Complex.exp ζ)‖ < 1 := by
  apply heightCayleyInverse_quarter
  · rw [Complex.exp_re]
    exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hb⟩)
  · rw [Complex.exp_im]
    exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi ha (by linarith [Real.pi_pos]))
  · rw [Complex.norm_exp]
    exact Real.exp_lt_one_iff.mpr hs

lemma heightSectorParameter_differentiable {k : ℕ} {ζ : ℂ}
    (hζ : Complex.exp ζ + 1 ≠ 0)
    (hu : heightCayleyInverse (Complex.exp ζ) ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (heightSectorParameter k) ζ := by
  unfold heightSectorParameter
  apply DifferentiableAt.cpow_const (f := fun x => heightCayleyInverse (Complex.exp x))
    (c := (k : ℂ)⁻¹) _ hu
  unfold heightCayleyInverse
  fun_prop

/-- The actual derivative of the explicit inverse coordinate is exactly the
direction used in the EW slope formulas. The regularity premises are explicit. -/
lemma hasDerivAt_heightSectorParameter {k : ℕ} (hk : 2 ≤ k) {ζ : ℂ}
    (hζ : Complex.exp ζ + 1 ≠ 0)
    (hu : heightCayleyInverse (Complex.exp ζ) ∈ Complex.slitPlane)
    (hw : heightSectorParameter k ζ ∉ Surface.punctures k)
    (hw0 : heightSectorParameter k ζ ≠ 0) :
    HasDerivAt (heightSectorParameter k)
      (I * coeff3 k (heightSectorParameter k ζ))⁻¹ ζ := by
  have hd := (heightSectorParameter_differentiable (k := k) hζ hu).hasDerivAt
  have hc := (hasDerivAt_heightCayley hw).comp ζ hd
  have he : (fun x => heightCayley k (heightSectorParameter k x)) =ᶠ[nhds ζ] Complex.exp := by
    have hn : ∀ᶠ x in nhds ζ, Complex.exp x + 1 ≠ 0 :=
      (Complex.continuous_exp.continuousAt.add_const 1).eventually_ne hζ
    filter_upwards [hn] with x hx
    exact heightCayley_sectorParameter (by omega) hx
  have hv := (hc.congr_of_eventuallyEq he.symm).unique (Complex.hasDerivAt_exp ζ)
  rw [heightCayley_sectorParameter (by omega) hζ] at hv
  have hg : gauss k (heightSectorParameter k ζ) ≠ 0 := pow_ne_zero _ hw0
  have hcoeff : coeff3 k (heightSectorParameter k ζ) ≠ 0 := by
    unfold coeff3 Weierstrass.phi3
    exact mul_ne_zero (mul_ne_zero (by norm_num) hg) (etaTarget_ne_zero hk hw)
  have hdval : deriv (heightSectorParameter k) ζ =
      (I * coeff3 k (heightSectorParameter k ζ))⁻¹ := by
    apply mul_left_cancel₀ (mul_ne_zero Complex.I_ne_zero hcoeff)
    rw [mul_inv_cancel₀ (mul_ne_zero Complex.I_ne_zero hcoeff)]
    apply mul_right_cancel₀ (Complex.exp_ne_zero ζ)
    linear_combination hv
  rw [hdval] at hd
  exact hd

end KsIndex.KarcherData
