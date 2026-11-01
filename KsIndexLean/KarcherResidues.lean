module

/-
Local residues of the normalized Karcher differential.
The factor +2πi uses positive, counterclockwise orientation. Its real-part
identities below are algebraic; no contour integral or global period is asserted.
Components may have removable singularities: residues are allowed to vanish.
-/
public import KsIndexLean.KarcherData

@[expose] public section


noncomputable section
open Complex Filter
open scoped Topology
namespace KsIndex.KarcherData

def coeff1 (k : ℕ) (w : ℂ) := Weierstrass.phi1 (gauss k w) (etaTarget k w)
def coeff2 (k : ℕ) (w : ℂ) := Weierstrass.phi2 (gauss k w) (etaTarget k w)
def coeff3 (k : ℕ) (w : ℂ) := Weierstrass.phi3 (gauss k w) (etaTarget k w)
def denominator (k : ℕ) (w : ℂ) := 1 + w ^ (2 * k)
def denominatorDeriv (k : ℕ) (w : ℂ) : ℂ := (2 * k : ℕ) * w ^ (2 * k - 1)

lemma puncture_ne_zero {k : ℕ} (hk : 2 ≤ k) {z : ℂ}
    (hz : z ∈ Surface.punctures k) : z ≠ 0 := by
  intro h
  subst z
  simp [Surface.punctures, show 2 * k ≠ 0 by omega] at hz

lemma puncture_norm {k : ℕ} (hk : 2 ≤ k) {z : ℂ}
    (hz : z ∈ Surface.punctures k) : ‖z‖ = 1 := by
  have h := congrArg norm hz
  simp only [norm_pow, norm_neg, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) (by omega : 2 * k ≠ 0)).1 h

lemma puncture_power_sign {k : ℕ} {z : ℂ} (hz : z ∈ Surface.punctures k) :
    z ^ k = I ∨ z ^ k = -I := by
  have h : (z ^ k - I) * (z ^ k + I) = 0 := by
    have hp : (z ^ k) ^ 2 = -1 := by
      rw [← pow_mul, mul_comm k 2]
      exact hz
    calc
      _ = (z ^ k) ^ 2 - I ^ 2 := by ring
      _ = 0 := by rw [hp, I_sq]; ring
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

lemma hasDerivAt_denominator (k : ℕ) (z : ℂ) :
    HasDerivAt (denominator k) (denominatorDeriv k z) z := by
  change HasDerivAt (fun w : ℂ => 1 + w ^ (2 * k))
    ((↑(2 * k) : ℂ) * z ^ (2 * k - 1)) z
  simpa only [Pi.pow_apply, id_eq, mul_one] using
    ((hasDerivAt_id z).pow (2 * k)).const_add (1 : ℂ)

lemma denominatorDeriv_ne_zero {k : ℕ} (hk : 2 ≤ k) {z : ℂ}
    (hz : z ∈ Surface.punctures k) : denominatorDeriv k z ≠ 0 := by
  exact mul_ne_zero (by exact_mod_cast (show 2 * k ≠ 0 by omega))
    (pow_ne_zero _ (puncture_ne_zero hk hz))

lemma denominatorDeriv_at_puncture {k : ℕ} (hk : 2 ≤ k) {z : ℂ}
    (hz : z ∈ Surface.punctures k) :
    denominatorDeriv k z = -(2 * (k : ℂ)) * z⁻¹ := by
  unfold denominatorDeriv
  rw [pow_sub₀ z (puncture_ne_zero hk hz) (by omega : 1 ≤ 2 * k), pow_one, hz]
  push_cast
  ring

lemma gauss_sq_at_puncture {k : ℕ} (hk : 2 ≤ k) {z : ℂ}
    (hz : z ∈ Surface.punctures k) : (gauss k z) ^ 2 = -(z⁻¹ ^ 2) := by
  unfold gauss
  rw [← pow_mul, show (k - 1) * 2 = 2 * k - 2 by omega,
    pow_sub₀ z (puncture_ne_zero hk hz) (by omega : 2 ≤ 2 * k), hz, inv_pow]
  ring

lemma differentiableAt_etaTarget {k : ℕ} {w : ℂ} (hw : w ∉ Surface.punctures k) :
    DifferentiableAt ℂ (etaTarget k) w := by
  have he : etaTarget k = fun z => (k : ℂ) * etaRaw k z := funext (etaTarget_eq_scale k)
  rw [he]
  exact (differentiableAt_etaRaw hw).const_mul _

lemma differentiableAt_coeff1 {k : ℕ} {w : ℂ} (hw : w ∉ Surface.punctures k) :
    DifferentiableAt ℂ (coeff1 k) w := by
  unfold coeff1 Weierstrass.phi1 gauss
  exact ((differentiableAt_const _).sub ((differentiableAt_id.pow _).pow 2)).mul
    (differentiableAt_etaTarget hw)

lemma differentiableAt_coeff2 {k : ℕ} {w : ℂ} (hw : w ∉ Surface.punctures k) :
    DifferentiableAt ℂ (coeff2 k) w := by
  unfold coeff2 Weierstrass.phi2 gauss
  exact (((differentiableAt_const _).add ((differentiableAt_id.pow _).pow 2)).const_mul I).mul
    (differentiableAt_etaTarget hw)

lemma differentiableAt_coeff3 {k : ℕ} {w : ℂ} (hw : w ∉ Surface.punctures k) :
    DifferentiableAt ℂ (coeff3 k) w := by
  unfold coeff3 Weierstrass.phi3 gauss
  exact ((differentiableAt_id.pow _).const_mul 2).mul (differentiableAt_etaTarget hw)

/-- Reciprocal slope at a simple zero; all functions are the actual rational data. -/
lemma tendsto_puncture_ratio {k : ℕ} (hk : 2 ≤ k) {z : ℂ}
    (hz : z ∈ Surface.punctures k) :
    Tendsto (fun w => (w - z) / denominator k w) (𝓝[≠] z)
      (𝓝 ((denominatorDeriv k z)⁻¹)) := by
  have hzero : denominator k z = 0 := by
    change 1 + z ^ (2 * k) = 0
    rw [show z ^ (2 * k) = -1 from hz]
    ring
  have h := (hasDerivAt_denominator k z).tendsto_slope.inv₀ (denominatorDeriv_ne_zero hk hz)
  simpa only [slope_def_field, hzero, sub_zero, inv_div] using h

lemma residue1_value {k : ℕ} (hk : 2 ≤ k) {z : ℂ} (hz : z ∈ Surface.punctures k) :
    (1 - (gauss k z) ^ 2) * (k : ℂ) / denominatorDeriv k z = -(z.re : ℂ) := by
  have hz0 := puncture_ne_zero hk hz
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [gauss_sq_at_puncture hk hz, denominatorDeriv_at_puncture hk hz]
  calc
    _ = -(z + z⁻¹) / 2 := by field_simp; ring
    _ = _ := by rw [Complex.inv_eq_conj (puncture_norm hk hz)]; apply Complex.ext <;> simp

lemma residue2_value {k : ℕ} (hk : 2 ≤ k) {z : ℂ} (hz : z ∈ Surface.punctures k) :
    I * (1 + (gauss k z) ^ 2) * (k : ℂ) / denominatorDeriv k z = (z.im : ℂ) := by
  have hz0 := puncture_ne_zero hk hz
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [gauss_sq_at_puncture hk hz, denominatorDeriv_at_puncture hk hz]
  calc
    _ = -I * (z - z⁻¹) / 2 := by field_simp; ring
    _ = _ := by rw [Complex.inv_eq_conj (puncture_norm hk hz)]; apply Complex.ext <;> simp

lemma residue3_value {k : ℕ} (hk : 2 ≤ k) {z : ℂ} (hz : z ∈ Surface.punctures k) :
    2 * gauss k z * (k : ℂ) / denominatorDeriv k z = 1 / z ^ k := by
  have hz0 := puncture_ne_zero hk hz
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [denominatorDeriv_at_puncture hk hz]
  have hg : gauss k z * z = z ^ k := by unfold gauss; rw [← pow_succ]; congr 1; omega
  have hsq : (z ^ k) ^ 2 = -1 := by rw [← pow_mul, mul_comm k 2]; exact hz
  calc
    _ = -(gauss k z * z) := by field_simp
    _ = -(z ^ k) := by rw [hg]
    _ = 1 / z ^ k := by apply (eq_div_iff (pow_ne_zero _ hz0)).2; linear_combination -hsq

/-- Local numerator multiplication of the actual reciprocal-slope limit. -/
lemma tendsto_weighted_ratio {k : ℕ} (hk : 2 ≤ k) {z : ℂ}
    (hz : z ∈ Surface.punctures k) {A : ℂ → ℂ} (hA : ContinuousAt A z) :
    Tendsto (fun w => (w - z) * (A w * (k : ℂ) / denominator k w)) (𝓝[≠] z)
      (𝓝 (A z * (k : ℂ) / denominatorDeriv k z)) := by
  have ha : Tendsto (fun w => A w * (k : ℂ)) (𝓝[≠] z) (𝓝 (A z * (k : ℂ))) :=
    (hA.mul continuousAt_const).tendsto.mono_left nhdsWithin_le_nhds
  have h := ha.mul (tendsto_puncture_ratio hk hz)
  convert h using 1
  · funext w
    ring
  · simp only [div_eq_mul_inv]

lemma residue1_limit {k : ℕ} (hk : 2 ≤ k) {z : ℂ} (hz : z ∈ Surface.punctures k) :
    Tendsto (fun w => (w - z) * coeff1 k w) (𝓝[≠] z) (𝓝 (-(z.re : ℂ))) := by
  have hA : ContinuousAt (fun w => 1 - (gauss k w) ^ 2) z := by unfold gauss; fun_prop
  have h := tendsto_weighted_ratio hk hz hA
  rw [residue1_value hk hz] at h
  simpa only [coeff1, Weierstrass.phi1, etaTarget, denominator, div_eq_mul_inv, mul_assoc] using h

lemma residue2_limit {k : ℕ} (hk : 2 ≤ k) {z : ℂ} (hz : z ∈ Surface.punctures k) :
    Tendsto (fun w => (w - z) * coeff2 k w) (𝓝[≠] z) (𝓝 (z.im : ℂ)) := by
  have hA : ContinuousAt (fun w => I * (1 + (gauss k w) ^ 2)) z := by unfold gauss; fun_prop
  have h := tendsto_weighted_ratio hk hz hA
  rw [residue2_value hk hz] at h
  simpa only [coeff2, Weierstrass.phi2, etaTarget, denominator, div_eq_mul_inv, mul_assoc] using h

lemma residue3_limit {k : ℕ} (hk : 2 ≤ k) {z : ℂ} (hz : z ∈ Surface.punctures k) :
    Tendsto (fun w => (w - z) * coeff3 k w) (𝓝[≠] z) (𝓝 (1 / z ^ k)) := by
  have hA : ContinuousAt (fun w => 2 * gauss k w) z := by unfold gauss; fun_prop
  have h := tendsto_weighted_ratio hk hz hA
  rw [residue3_value hk hz] at h
  simpa only [coeff3, Weierstrass.phi3, etaTarget, denominator, div_eq_mul_inv, mul_assoc] using h

lemma residue3_sign {k : ℕ} {z : ℂ} (hz : z ∈ Surface.punctures k) :
    1 / z ^ k = I ∨ 1 / z ^ k = -I := by
  rcases puncture_power_sign hz with h | h
  · right; simp [h]
  · left; simp [h]

/-- +2πi corresponds to counterclockwise orientation; this is only scalar algebra. -/
lemma residue1_real_factor (z : ℂ) :
    ((2 * Real.pi : ℂ) * I * (-(z.re : ℂ))).re = 0 := by
  simp [Complex.mul_re, Complex.mul_im]

lemma residue2_real_factor (z : ℂ) :
    ((2 * Real.pi : ℂ) * I * (z.im : ℂ)).re = 0 := by
  simp [Complex.mul_re, Complex.mul_im]

/-- The algebraic ±2π values; an actual loop-integral bridge is a separate theorem. -/
lemma residue3_real_factor {k : ℕ} {z : ℂ} (hz : z ∈ Surface.punctures k) :
    ((2 * Real.pi : ℂ) * I * (1 / z ^ k)).re = -(2 * Real.pi) ∨
    ((2 * Real.pi : ℂ) * I * (1 / z ^ k)).re = 2 * Real.pi := by
  rcases residue3_sign hz with h | h
  · left; simp [h, Complex.mul_re, Complex.mul_im]
  · right; simp [h, Complex.mul_re, Complex.mul_im]

end KsIndex.KarcherData
