module

public import KsIndexLean.SmoothWeakGreen
public import KsIndexLean.ModeDiag
public import KsIndexLean.RadialNeumannClassification

@[expose] public section


noncomputable section
open Set Filter
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.JacobiMode KsIndex.ModeDiag KsIndex.Radial

lemma modeU_radial_ray (k ℓ : ℕ) {r : ℝ} (hr : 0 ≤ r) {w : ℂ} (hw : ‖w‖ = 1) :
    modeU k ℓ ((r : ℂ) * w) = (uRad k ℓ r : ℂ) * w ^ ℓ := by
  rw [modeU, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
    hw, mul_one, mul_pow, uRad]
  push_cast
  ring

lemma modeU_normal {k : ℕ} (hk : 2 ≤ k) (ℓ : ℕ) {w : ℂ} (hw : ‖w‖ = 1) :
    fderiv ℝ (modeU k ℓ) w w = ((ℓ : ℝ) ^ 2 - kap k ^ 2 : ℝ) * w ^ ℓ := by
  apply fderiv_radial_of_hasDerivAt (modeU k ℓ)
    ((modeU_contDiff (by omega : 1 ≤ k) ℓ).differentiable (by simp) w)
  have h := ((uRad_hasDerivAt hk ℓ (by norm_num : (1 : ℝ) ≠ 0)).ofReal_comp).mul_const (w ^ ℓ)
  rw [uD_one hk] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)] with r hr
  exact modeU_radial_ray k ℓ hr.le hw

lemma conjugate_modeU_normal {k : ℕ} (hk : 2 ≤ k) (ℓ : ℕ) {w : ℂ} (hw : ‖w‖ = 1) :
    fderiv ℝ (fun z => (starRingEnd ℂ) (modeU k ℓ z)) w w =
      (((ℓ : ℝ) ^ 2 - kap k ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ) w ^ ℓ := by
  have hd := Complex.conjCLE.hasFDerivAt.comp w
    ((modeU_contDiff (by omega : 1 ≤ k) ℓ).differentiable (by simp) w).hasFDerivAt
  change fderiv ℝ (Complex.conjCLE ∘ modeU k ℓ) w w = _
  rw [hd.fderiv]
  change (starRingEnd ℂ) (fderiv ℝ (modeU k ℓ) w w) = _
  rw [modeU_normal hk ℓ hw, map_mul, map_pow, Complex.conj_ofReal]

/-- Explicit modes with both signs of frequency. Global smoothness for `k ≥ 2`
is proved by `signedModeU_smooth`. -/
def signedModeU (k : ℕ) : ℤ → ℂ → ℂ
  | .ofNat m => modeU k m
  | .negSucc m => fun z => (starRingEnd ℂ) (modeU k (m + 1) z)

lemma signedModeU_smooth {k : ℕ} (hk : 2 ≤ k) (n : ℤ) :
    ContDiff ℝ ∞ (signedModeU k n) := by
  cases n with
  | ofNat m => exact modeU_contDiff (by omega) m
  | negSucc m => exact Complex.conjCLE.contDiff.comp (modeU_contDiff (by omega) (m + 1))

lemma signedModeU_normal {k : ℕ} (hk : 2 ≤ k) (n : ℤ) (w : Circle₁) :
    fderiv ℝ (signedModeU k n) w w =
      (((n.natAbs : ℝ) ^ 2 - kap k ^ 2 : ℝ) : ℂ) * fourierAmbient n w := by
  have hw : ‖(w : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
  cases n with
  | ofNat m => exact modeU_normal hk m hw
  | negSucc m => exact conjugate_modeU_normal hk (m + 1) hw

lemma signedModeU_flux_nonzero {k : ℕ} (hk : 2 ≤ k) (n : ℤ)
    (hn : n.natAbs ≠ k - 1) :
    (((n.natAbs : ℝ) ^ 2 - kap k ^ 2 : ℝ) : ℂ) ≠ 0 := by
  rw [← uD_one hk]
  exact Complex.ofReal_ne_zero.mpr (uD_one_ne_zero hk hn)

end KsIndex.Trace
