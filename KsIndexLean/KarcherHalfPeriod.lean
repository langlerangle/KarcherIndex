module

public import KsIndexLean.KarcherSymmetryConstants
public import KsIndexLean.KarcherLocalPrimitive
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

@[expose] public section


/-!
# Vertical displacements of the screw and rotation symmetries

The screw parameter map `w ↦ β·(conj w)⁻¹` (β^k = -1) and the rotation parameter map
`w ↦ a·w` (a^k = 1) give affine displacement constants
`Dscrew = descendedIntegral 1 β` and `Drot = descendedIntegral 1 a`.
Their vertical components are computed along the radial chain `1 → 0 → c`:
under `u = w^k`, the vertical form `coeff3` is `2 du/(1+u²)`, with primitive
`2·arctan(w^k)` on the relevant segments. Its integral is `2·arctan(c^k) − π/2`.
Thus the screw displacement is `−π`, whose class modulo `2π` is `+π`, and the
rotation displacement is zero.

The proof derives the complex arctangent derivative on its slit-plane domain
and evaluates the radial integrals. The final algebraic lemma shows that the
reflection phase constraint forces a horizontal displacement to be a real
multiple of `β⁻¹ - 1`; identifying the geometric center uses this separately.
-/
noncomputable section
namespace KsIndex.KarcherData
open Complex

/-- The complex arctangent has derivative `1/(1+z²)` wherever the two Cayley factors are nonzero and
their ratio lies in the slit plane (in particular at every real `z`). Derived from the defining
`arctan z = -I/2·log((1+zI)/(1-zI))`. -/
lemma hasDerivAt_carctan {z : ℂ} (hz1 : (1 : ℂ) + z * I ≠ 0) (hz2 : (1 : ℂ) - z * I ≠ 0)
    (hs : (1 + z * I) / (1 - z * I) ∈ Complex.slitPlane) :
    HasDerivAt Complex.arctan (1 / (1 + z ^ 2)) z := by
  have hfac : (1 + z * I) * (1 - z * I) = 1 + z ^ 2 := by
    linear_combination (-z ^ 2 : ℂ) * Complex.I_sq
  have hsq : (1 : ℂ) + z ^ 2 ≠ 0 := by
    intro h
    rw [← hfac] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact hz1 h'
    · exact hz2 h'
  have hf1 : HasDerivAt (fun w : ℂ => 1 + w * I) I z := by
    simpa using ((hasDerivAt_id z).mul_const I).const_add 1
  have hf2 : HasDerivAt (fun w : ℂ => 1 - w * I) (-I) z := by
    have h := (hasDerivAt_id z).mul_const I
    simpa using h.const_sub 1
  have hg : HasDerivAt (fun w : ℂ => (1 + w * I) / (1 - w * I))
      (2 * I / (1 - z * I) ^ 2) z := by
    have h := hf1.div hf2 hz2
    have e : (I * (1 - z * I) - (1 + z * I) * -I) / (1 - z * I) ^ 2
        = 2 * I / (1 - z * I) ^ 2 := by
      rw [div_eq_div_iff (pow_ne_zero 2 hz2) (pow_ne_zero 2 hz2)]; ring
    rw [e] at h
    exact h
  have hlog : HasDerivAt (fun w : ℂ => Complex.log ((1 + w * I) / (1 - w * I)))
      (2 * I / (1 + z ^ 2)) z := by
    have h := (Complex.hasDerivAt_log hs).comp z hg
    have e : ((1 + z * I) / (1 - z * I))⁻¹ * (2 * I / (1 - z * I) ^ 2)
        = 2 * I / (1 + z ^ 2) := by
      rw [inv_div, div_mul_div_comm,
        div_eq_div_iff (mul_ne_zero hz1 (pow_ne_zero 2 hz2)) hsq]
      linear_combination (2 * I * z ^ 2 * (1 - z * I)) * Complex.I_sq
    rw [e] at h
    exact h
  have hfin := hlog.const_mul (-I / 2)
  have hval : (-I / 2) * (2 * I / (1 + z ^ 2)) = 1 / (1 + z ^ 2) := by
    rw [← mul_div_assoc, show (-I / 2) * (2 * I) = (1 : ℂ) from by
      linear_combination (-1 : ℂ) * Complex.I_sq]
  rw [← hval]
  exact hfin

/-- For real `z` the Cayley argument `(1+zI)/(1-zI)` lies in the slit plane. -/
lemma slit_of_imZero {z : ℂ} (hz : z.im = 0) :
    (1 + z * I) / (1 - z * I) ∈ Complex.slitPlane := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp [Complex.mem_slitPlane_iff]
  · have hre0 : z.re ≠ 0 := fun h => hz0 (Complex.ext h hz)
    have hz2 : (1 : ℂ) - z * I ≠ 0 := by
      intro hc
      have hc2 := congrArg Complex.re hc
      simp [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, hz] at hc2
    have hzr : (1 : ℂ) + z ^ 2 = ((1 + z.re ^ 2 : ℝ) : ℂ) := by
      apply Complex.ext <;>
        simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, hz]
    have hrpos : (0 : ℝ) < 1 + z.re ^ 2 := by positivity
    have hsq : (1 : ℂ) + z ^ 2 ≠ 0 := by rw [hzr]; exact_mod_cast hrpos.ne'
    have hquot : (1 + z * I) / (1 - z * I) = (1 + z * I) ^ 2 / (1 + z ^ 2) := by
      rw [div_eq_div_iff hz2 hsq]
      linear_combination ((1 + z * I) * z ^ 2) * Complex.I_sq
    rw [hquot, hzr, Complex.mem_slitPlane_iff]
    right
    rw [Complex.div_ofReal_im]
    apply div_ne_zero _ hrpos.ne'
    have him : ((1 + z * I) ^ 2).im = 2 * z.re := by
      simp only [pow_two, Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im,
        Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, hz]
      ring
    rw [him]
    exact mul_ne_zero two_ne_zero hre0

/-- The derivative of the primitive `2·arctan(w^k)` is `coeff3` wherever `w^k` is real. -/
lemma hasDerivAt_coeff3_prim {k : ℕ} {w : ℂ} (hr : (w ^ k).im = 0) :
    HasDerivAt (fun v : ℂ => 2 * Complex.arctan (v ^ k)) (coeff3 k w) w := by
  have hz1 : (1 : ℂ) + w ^ k * I ≠ 0 := by
    have hre : ((1 : ℂ) + w ^ k * I).re = 1 := by
      simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, hr]
    intro hc; rw [hc, Complex.zero_re] at hre; norm_num at hre
  have hz2 : (1 : ℂ) - w ^ k * I ≠ 0 := by
    have hre : ((1 : ℂ) - w ^ k * I).re = 1 := by
      simp [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, hr]
    intro hc; rw [hc, Complex.zero_re] at hre; norm_num at hre
  have harc := hasDerivAt_carctan hz1 hz2 (slit_of_imZero hr)
  have hpow : HasDerivAt (fun v : ℂ => v ^ k) ((k : ℂ) * w ^ (k - 1)) w := by
    simpa using hasDerivAt_pow k w
  have hfin := (harc.comp w hpow).const_mul (2 : ℂ)
  have e : (2 : ℂ) * (1 / (1 + (w ^ k) ^ 2) * ((k : ℂ) * w ^ (k - 1))) = coeff3 k w := by
    unfold coeff3 Weierstrass.phi3 gauss etaTarget
    rw [show (w ^ k) ^ 2 = w ^ (2 * k) by rw [← pow_mul, mul_comm]]
    ring
  rw [← e]
  exact hfin

open Piecewise

/-- The two-segment radial chain `1 → 0 → c`. -/
def radialChain (c : ℂ) : Chain :=
  (Chain.singleton (linePiece 1 0)).append (Chain.singleton (linePiece 0 c)) (by simp)

@[simp] lemma radialChain_start (c : ℂ) : (radialChain c).start = 1 := by
  simp [radialChain]

@[simp] lemma radialChain_finish (c : ℂ) : (radialChain c).finish = c := by
  simp [radialChain]

/-- The radial chain `1→0→c` avoids every puncture when `c^{2k}=1` (both segments carry
`w^{2k} ≥ 0`, while punctures have `w^{2k}=-1`). -/
lemma radialChain_avoids_punctures {k : ℕ} {c : ℂ} (hc : c ^ (2 * k) = 1) :
    ∀ z ∈ Surface.punctures k, (radialChain c).Avoids z := by
  have hbad : ∀ x : ℝ, 0 ≤ x → ((x : ℂ) ≠ -1) := by
    intro x hx hcon
    have := congrArg Complex.re hcon
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.one_re] at this
    linarith
  intro z hz
  have hzp : z ^ (2 * k) = -1 := hz
  apply Chain.append_avoids
  · refine Chain.singleton_avoids _ (linePiece_avoids (fun s hcon => ?_))
    rw [hcon] at hzp
    have hcast : (1 : ℂ) + (s : ℂ) * (0 - 1) = ((1 - s : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, ← Complex.ofReal_pow] at hzp
    exact hbad _ (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) k) hzp
  · refine Chain.singleton_avoids _ (linePiece_avoids (fun s hcon => ?_))
    rw [hcon] at hzp
    simp only [zero_add, sub_zero, mul_pow, hc, mul_one] at hzp
    rw [← Complex.ofReal_pow] at hzp
    exact hbad _ (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) k) hzp

/-- The contour of `coeff3` along the radial chain `1→0→c` equals `2·arctan(c^k) − 2·arctan 1`
(the two `arctan(0^k)` endpoint contributions cancel). Requires `c^{2k}=1` (avoids punctures) and
`c^k` real (so `w^k` is real on both segments, where the `2·arctan(w^k)` primitive applies). -/
lemma radialChain_contour_coeff3 {k : ℕ} (hk : 2 ≤ k) {c : ℂ} (hc : c ^ (2 * k) = 1)
    (hck : (c ^ k).im = 0) :
    (radialChain c).contour (coeff3 k)
      = 2 * Complex.arctan (c ^ k) - 2 * Complex.arctan 1 := by
  have him1 : ∀ z ∈ (linePiece (1 : ℂ) 0).image, (z ^ k).im = 0 := by
    rintro _ ⟨t, _, rfl⟩
    have hcast : (linePiece (1 : ℂ) 0).curve t = ((1 - t : ℝ) : ℂ) := by
      simp only [linePiece]; push_cast; ring
    rw [hcast, ← Complex.ofReal_pow]; exact Complex.ofReal_im _
  have him2 : ∀ z ∈ (linePiece (0 : ℂ) c).image, (z ^ k).im = 0 := by
    rintro _ ⟨t, _, rfl⟩
    have hcast : (linePiece (0 : ℂ) c).curve t = (t : ℂ) * c := by
      simp only [linePiece]; push_cast; ring
    rw [hcast, mul_pow, show ((t : ℂ)) ^ k = ((t ^ k : ℝ) : ℂ) from (Complex.ofReal_pow t k).symm]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hck, mul_zero, zero_mul,
      add_zero]
  have hnp1 : ∀ z ∈ (linePiece (1 : ℂ) 0).image, z ∉ Surface.punctures k := by
    rintro _ ⟨t, _, rfl⟩ hp
    have hzp : ((linePiece (1 : ℂ) 0).curve t) ^ (2 * k) = -1 := hp
    have hcast : (linePiece (1 : ℂ) 0).curve t = ((1 - t : ℝ) : ℂ) := by
      simp only [linePiece]; push_cast; ring
    rw [hcast, ← Complex.ofReal_pow] at hzp
    have hre := congrArg Complex.re hzp
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.one_re] at hre
    have hnn : (0 : ℝ) ≤ (1 - t) ^ (2 * k) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) k
    linarith
  have hnp2 : ∀ z ∈ (linePiece (0 : ℂ) c).image, z ∉ Surface.punctures k := by
    rintro _ ⟨t, _, rfl⟩ hp
    have hzp : ((linePiece (0 : ℂ) c).curve t) ^ (2 * k) = -1 := hp
    have hcast : (linePiece (0 : ℂ) c).curve t = (t : ℂ) * c := by
      simp only [linePiece]; push_cast; ring
    rw [hcast, mul_pow, hc, mul_one, ← Complex.ofReal_pow] at hzp
    have hre := congrArg Complex.re hzp
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.one_re] at hre
    have hnn : (0 : ℝ) ≤ t ^ (2 * k) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) k
    linarith
  have hf1 : ContinuousOn (coeff3 k) (linePiece (1 : ℂ) 0).image :=
    fun z hz => (differentiableAt_coeff3 (hnp1 z hz)).continuousAt.continuousWithinAt
  have hf2 : ContinuousOn (coeff3 k) (linePiece (0 : ℂ) c).image :=
    fun z hz => (differentiableAt_coeff3 (hnp2 z hz)).continuousAt.continuousWithinAt
  rw [radialChain,
    Chain.append_contour _ _ _
      (Chain.singleton_integrable (linePiece 1 0) ((linePiece 1 0).integrable_of_continuousOn hf1))
      (Chain.singleton_integrable (linePiece 0 c) ((linePiece 0 c).integrable_of_continuousOn hf2)),
    Chain.singleton_contour, Chain.singleton_contour,
    linePiece_contour_eq_sub hf1 (fun z hz => hasDerivAt_coeff3_prim (him1 z hz)),
    linePiece_contour_eq_sub hf2 (fun z hz => hasDerivAt_coeff3_prim (him2 z hz))]
  simp only [one_pow]
  ring

/-- `Complex.arctan 1 = π/4`. -/
lemma carctan_one : Complex.arctan 1 = ((Real.pi / 4 : ℝ) : ℂ) := by
  rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) from by norm_num, ← Complex.ofReal_arctan, Real.arctan_one]

/-- `Complex.arctan (-1) = -π/4`. -/
lemma carctan_neg_one : Complex.arctan (-1) = ((-(Real.pi / 4) : ℝ) : ℂ) := by
  rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) from by norm_num, ← Complex.ofReal_arctan,
    show (-1 : ℝ) = -(1 : ℝ) from by norm_num, Real.arctan_neg, Real.arctan_one]

/-- `↑(-π) = ↑π` in `AddCircle (2π)` (half-period 2-torsion). -/
lemma coe_neg_pi_eq_pi :
    ((-Real.pi : ℝ) : AddCircle (2 * Real.pi)) = ((Real.pi : ℝ) : AddCircle (2 * Real.pi)) := by
  have h := AddCircle.coe_add_period (p := 2 * Real.pi) (-Real.pi)
  rw [show (-Real.pi) + 2 * Real.pi = Real.pi from by ring] at h
  exact h.symm

/-- **Screw vertical displacement modulo `2π` is `+π`.** For `c^k = -1` (the screw image of the basepoint 1),
the vertical component of `descendedIntegral 1 c` is the half-period `π`. -/
theorem descendedIntegral_vertical_screw {k : ℕ} (hk : 2 ≤ k) {c : ℂ} (hck : c ^ k = -1)
    (h1 : (1 : ℂ) ∉ Surface.punctures k) (hc' : c ∉ Surface.punctures k) :
    (descendedIntegral hk ⟨1, h1⟩ ⟨c, hc'⟩).2.2 = ((Real.pi : ℝ) : AddCircle (2 * Real.pi)) := by
  have hc2k : c ^ (2 * k) = 1 := by rw [mul_comm, pow_mul, hck]; norm_num
  have hckim : (c ^ k).im = 0 := by rw [hck]; simp
  rw [descendedIntegral_eq hk ⟨1, h1⟩ ⟨c, hc'⟩ (radialChain c) (by simp) (by simp)
      (radialChain_avoids_punctures hc2k)]
  show (↑(((radialChain c).contour (coeff3 k)).re) : AddCircle (2 * Real.pi)) = _
  rw [radialChain_contour_coeff3 hk hc2k hckim, hck, carctan_neg_one, carctan_one,
    show (2 * ((-(Real.pi / 4) : ℝ) : ℂ) - 2 * ((Real.pi / 4 : ℝ) : ℂ)).re = -Real.pi from by
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.re_ofNat, Complex.im_ofNat]; ring]
  exact coe_neg_pi_eq_pi

/-- **Rotation vertical displacement is zero.** For `c^k = 1` (the rotation image of the basepoint
1), the vertical component of `descendedIntegral 1 c` vanishes. -/
theorem descendedIntegral_vertical_rot {k : ℕ} (hk : 2 ≤ k) {c : ℂ} (hck : c ^ k = 1)
    (h1 : (1 : ℂ) ∉ Surface.punctures k) (hc' : c ∉ Surface.punctures k) :
    (descendedIntegral hk ⟨1, h1⟩ ⟨c, hc'⟩).2.2 = (0 : AddCircle (2 * Real.pi)) := by
  have hc2k : c ^ (2 * k) = 1 := by rw [mul_comm, pow_mul, hck]; norm_num
  have hckim : (c ^ k).im = 0 := by rw [hck]; simp
  rw [descendedIntegral_eq hk ⟨1, h1⟩ ⟨c, hc'⟩ (radialChain c) (by simp) (by simp)
      (radialChain_avoids_punctures hc2k)]
  show (↑(((radialChain c).contour (coeff3 k)).re) : AddCircle (2 * Real.pi)) = _
  rw [radialChain_contour_coeff3 hk hc2k hckim, hck]
  simp

/-! ### Horizontal center constraint

The reflection phase constraint forces a
displacement to be a real multiple of `β⁻¹ - 1`, which is exactly the range of `(R_β - I)` on the x-axis. -/

/-- If `conj x = -β·x` (the refl_y constraint) with `conj β = β⁻¹`, `β ≠ 0`, `β⁻¹ ≠ 1`, then `x` is a
real multiple of `β⁻¹ - 1` (both satisfy `conj y = -β y`, so their ratio is real). -/
lemma exists_real_multiple_of_conj {β x : ℂ} (hβ0 : β ≠ 0) (hβc : starRingEnd ℂ β = β⁻¹)
    (hv : β⁻¹ - 1 ≠ 0) (hx : starRingEnd ℂ x = -β * x) :
    ∃ t : ℝ, x = (t : ℂ) * (β⁻¹ - 1) := by
  have hconjv : starRingEnd ℂ (β⁻¹ - 1) = -β * (β⁻¹ - 1) := by
    rw [map_sub, map_one, map_inv₀, hβc, inv_inv]; field_simp; ring
  have hreal : starRingEnd ℂ (x / (β⁻¹ - 1)) = x / (β⁻¹ - 1) := by
    rw [map_div₀, hx, hconjv, mul_div_mul_left _ _ (neg_ne_zero.mpr hβ0)]
  obtain ⟨t, ht⟩ := Complex.conj_eq_iff_real.mp hreal
  exact ⟨t, (div_eq_iff hv).mp ht⟩

end KsIndex.KarcherData
