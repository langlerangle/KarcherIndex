module

/-
Karcher, Embedded minimal surfaces derived from Scherk's examples (1988):
§1.1 p84 uses X = Re ∫(1/g-g, i(1/g+g), 2) dh; §2.3.1 p88 supplies the data.
Karcher's complex variable z is our w; the paper's z is the ambient height.
The coefficient eta is (dh/dw)/g, not Karcher's half-height h.
This file constructs finite-chart differential data, not a global immersion.
-/
public import KsIndexLean.WeierstrassAlgebra
public import KsIndexLean.Surface

@[expose] public section


noncomputable section
namespace KsIndex.KarcherData

/-- Karcher's literal Gauss-map datum. -/
def gauss (k : ℕ) (w : ℂ) : ℂ := w ^ (k - 1)

/-- Literal coefficient of dh = (w^k + w^(-k))⁻¹ dw/w, valid away from zero. -/
def dhLiteral (k : ℕ) (w : ℂ) : ℂ := (w ^ k + (w ^ k)⁻¹)⁻¹ / w

/-- The unsimplified quotient; its totalized value at zero is not the extension. -/
def etaLiteral (k : ℕ) (w : ℂ) : ℂ := dhLiteral k w / gauss k w

/-- Rational expression extending the raw differential coefficient over zero. -/
def etaRaw (k : ℕ) (w : ℂ) : ℂ := 1 / (1 + w ^ (2 * k))

/-- Differential coefficient after the ambient homothety of factor k. -/
def etaTarget (k : ℕ) (w : ℂ) : ℂ := (k : ℂ) / (1 + w ^ (2 * k))

lemma denominator_ne_zero {k : ℕ} {w : ℂ} (hw : w ∉ Surface.punctures k) :
    1 + w ^ (2 * k) ≠ 0 := by
  intro h
  apply hw
  change w ^ (2 * k) = -1
  linear_combination h

lemma etaRaw_ne_zero {k : ℕ} {w : ℂ} (hw : w ∉ Surface.punctures k) :
    etaRaw k w ≠ 0 := one_div_ne_zero (denominator_ne_zero hw)

lemma etaTarget_eq_scale (k : ℕ) (w : ℂ) :
    etaTarget k w = (k : ℂ) * etaRaw k w := by
  simp [etaTarget, etaRaw, div_eq_mul_inv]

lemma etaTarget_ne_zero {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : w ∉ Surface.punctures k) : etaTarget k w ≠ 0 := by
  rw [etaTarget_eq_scale]
  exact mul_ne_zero (by exact_mod_cast (show k ≠ 0 by omega)) (etaRaw_ne_zero hw)

lemma dhLiteral_eq_gauss_mul_etaRaw {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : w ≠ 0) (hp : w ∉ Surface.punctures k) :
    dhLiteral k w = gauss k w * etaRaw k w := by
  have hx : w ^ k ≠ 0 := pow_ne_zero _ hw
  have hpow : w ^ (2 * k) = (w ^ k) ^ 2 := by rw [mul_comm 2 k, pow_mul]
  have hd : 1 + (w ^ k) ^ 2 ≠ 0 := by simpa only [hpow] using denominator_ne_zero hp
  have hs : w ^ k + (w ^ k)⁻¹ ≠ 0 := by
    intro h
    apply hd
    have he := congrArg (fun z : ℂ => z * w ^ k) h
    simp only [add_mul, inv_mul_cancel₀ hx, zero_mul] at he
    linear_combination he
  have hg : w ^ (k - 1) * w = w ^ k := by
    rw [← pow_succ]; congr 1; omega
  have hi : (w ^ k + (w ^ k)⁻¹)⁻¹ = w ^ k / (1 + (w ^ k) ^ 2) := by
    apply (eq_div_iff hd).2
    apply (inv_mul_eq_iff_eq_mul₀ hs).2
    field_simp [hx]
    ring
  unfold dhLiteral gauss etaRaw
  rw [hi, hpow, ← hg]
  field_simp [hw]

lemma etaLiteral_eq_etaRaw {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : w ≠ 0) (hp : w ∉ Surface.punctures k) :
    etaLiteral k w = etaRaw k w := by
  unfold etaLiteral
  rw [dhLiteral_eq_gauss_mul_etaRaw hk hw hp]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ hw)

lemma etaRaw_zero {k : ℕ} (hk : 2 ≤ k) : etaRaw k 0 = 1 := by
  simp [etaRaw, show 2 * k ≠ 0 by omega]

lemma etaLiteral_zero (k : ℕ) : etaLiteral k 0 = 0 := by
  simp [etaLiteral, dhLiteral]

/-- The simplified expression is holomorphic at every finite nonpunctured point. -/
lemma differentiableAt_etaRaw {k : ℕ} {w : ℂ} (hw : w ∉ Surface.punctures k) :
    DifferentiableAt ℂ (etaRaw k) w := by
  exact (differentiableAt_const (1 : ℂ)).div
    ((differentiableAt_const (1 : ℂ)).add (differentiableAt_id.pow _)) (denominator_ne_zero hw)

lemma etaRaw_tendsto_one_at_zero {k : ℕ} (hk : 2 ≤ k) :
    Filter.Tendsto (etaRaw k) (nhds 0) (nhds 1) := by
  have hp : (0 : ℂ) ∉ Surface.punctures k := by
    simp [Surface.punctures, show 2 * k ≠ 0 by omega]
  simpa only [ContinuousAt, etaRaw_zero hk] using (differentiableAt_etaRaw hp).continuousAt

/-- The actual literal quotient has removable limit 1, despite its totalized value 0. -/
lemma etaLiteral_tendsto_one_at_zero {k : ℕ} (hk : 2 ≤ k) :
    Filter.Tendsto (etaLiteral k) (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds 1) := by
  have hc : ContinuousAt (fun w : ℂ => 1 + w ^ (2 * k)) 0 := by fun_prop
  have he := hc.eventually_ne (y := 0) (by simp [show 2 * k ≠ 0 by omega])
  apply ((etaRaw_tendsto_one_at_zero hk).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hd hw
  have hw0 : w ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hw
  have hp : w ∉ Surface.punctures k := by
    intro hp
    apply hd
    change w ^ (2 * k) = -1 at hp
    rw [hp]
    ring
  exact (etaLiteral_eq_etaRaw hk hw0 hp).symm

/-- Exact identification with the existing rho, derived from the literal data. -/
lemma metric_coefficient_eq_rho {k : ℕ} (hk : 2 ≤ k) (w : ℂ) :
    ‖etaTarget k w‖ * (1 + ‖gauss k w‖ ^ 2) = Surface.rho k w := by
  have he : (k - 1) * 2 = 2 * k - 2 := by omega
  simp only [etaTarget, gauss, norm_div, norm_pow, ← pow_mul, he]
  rw [Complex.norm_natCast]
  unfold Surface.rho
  rw [add_comm (1 : ℂ), add_comm (1 : ℝ)]
  ring

lemma real_metric_eq_rho_sq {k : ℕ} (hk : 2 ≤ k) (w : ℂ) :
    Weierstrass.realSq (Weierstrass.phi1 (gauss k w) (etaTarget k w))
      (Weierstrass.phi2 (gauss k w) (etaTarget k w))
      (Weierstrass.phi3 (gauss k w) (etaTarget k w)) = Surface.rho k w ^ 2 := by
  rw [Weierstrass.weierstrass_real_metric, ← mul_pow, metric_coefficient_eq_rho hk]

lemma imag_metric_eq_rho_sq {k : ℕ} (hk : 2 ≤ k) (w : ℂ) :
    Weierstrass.imagSq (Weierstrass.phi1 (gauss k w) (etaTarget k w))
      (Weierstrass.phi2 (gauss k w) (etaTarget k w))
      (Weierstrass.phi3 (gauss k w) (etaTarget k w)) = Surface.rho k w ^ 2 := by
  rw [← Weierstrass.weierstrass_equal_lengths]
  exact real_metric_eq_rho_sq hk w

end KsIndex.KarcherData
