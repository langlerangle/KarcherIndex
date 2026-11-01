module

public import KsIndexLean.KarcherNormalization
public import KsIndexLean.KarcherHalfPeriod

@[expose] public section


/-!
# Horizontal center normalization

Positional normalization of the EW immersion: one horizontal translation `T = (t, 0, 0)` centers
both the rotation deck (`a = β²`, `a^k = 1`) and the screw deck (`β`, `β^k = -1`), discharging the
two displacement equations consumed by `normalize_affine_symmetries`:

* `Dr + T - rotate a T = 0`               (rotation offset killed)
* `Ds + T - rotate β T = (0, 0, ↑π)`      (screw offset → vertical half-period)

with `Dr = descendedIntegral 1 β²`, `Ds = descendedIntegral 1 β`.

The vertical components follow from `descendedIntegral_vertical_screw` and
`descendedIntegral_vertical_rot`. The horizontal calculation uses the finite
`descendedIntegral` symmetry identities:

* **(A)** `descendedIntegral_conjMap` (refl_y) ∘ `descendedIntegral_screwMap` ∘ antisymmetry force
  `conj(Ds_c) = -β · Ds_c` on the horizontal complex coordinate `Ds_c`;
* **(B)** hence `Ds_c = t·(β⁻¹ - 1)` for a real `t` (`exists_real_multiple_of_conj`);
* **(C)** the cocycle + screw equivariance (`screw² = rotation(β²)`) give
  `Dr_c = (1 + β⁻¹)·Ds_c = t·(β⁻² - 1)` — the same `t` centers the rotation.

Here `PeriodTarget.rotate a` acts on the horizontal complex coordinate by multiplication
by `a⁻¹`; this convention accounts for the inverse powers in the displacement formulas.
-/
noncomputable section
namespace KsIndex.KarcherData
open Complex

/-! ### Horizontal-complex coordinate on `PeriodTarget = ℝ × ℝ × AddCircle (2π)`. -/

/-- The horizontal position of a `PeriodTarget` as a single complex number `x + y·i`. -/
def horizC (p : PeriodTarget) : ℂ := (p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I

lemma horizC_add (p q : PeriodTarget) : horizC (p + q) = horizC p + horizC q := by
  simp only [horizC, Prod.fst_add, Prod.snd_add, Complex.ofReal_add]; ring

lemma horizC_sub (p q : PeriodTarget) : horizC (p - q) = horizC p - horizC q := by
  simp only [horizC, Prod.fst_sub, Prod.snd_sub, Complex.ofReal_sub]; ring

lemma horizC_neg (p : PeriodTarget) : horizC (-p) = - horizC p := by
  simp only [horizC, Prod.fst_neg, Prod.snd_neg, Complex.ofReal_neg]; ring

lemma horizC_rotate (a : ℂ) (p : PeriodTarget) :
    horizC (PeriodTarget.rotate a p) = a⁻¹ * horizC p := by
  simp only [horizC, PeriodTarget.rotate]
  exact Complex.re_add_im _

lemma horizC_reflY (p : PeriodTarget) :
    horizC (PeriodTarget.reflY p) = starRingEnd ℂ (horizC p) := by
  simp only [horizC, PeriodTarget.reflY, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.ofReal_neg]
  ring

lemma horizC_xaxis (t : ℝ) : horizC ((t, 0, 0) : PeriodTarget) = (t : ℂ) := by
  simp [horizC]

/-- Horizontal vanishing: `horizC p = 0` pins both real horizontal coordinates. -/
lemma periodTarget_horiz_eq_zero {p : PeriodTarget} (h : horizC p = 0) : p.1 = 0 ∧ p.2.1 = 0 := by
  refine ⟨?_, ?_⟩
  · have := congrArg Complex.re h; simpa [horizC] using this
  · have := congrArg Complex.im h; simpa [horizC] using this

/-- Vertical component of a horizontally-translated-and-rotated displacement equals the original
vertical: the x-axis translation and the vertical-fixing rotation contribute nothing vertically. -/
lemma vertical_translate_eq (D : PeriodTarget) (a : ℂ) (t : ℝ) :
    (D + ((t, 0, 0) : PeriodTarget) - PeriodTarget.rotate a (t, 0, 0)).2.2 = D.2.2 := by
  simp [PeriodTarget.rotate, Prod.snd_add, Prod.snd_sub]

/-! ### Abstract assembly: two displacement equations from the constraints. -/

/-- From the refl_y constraint `conj(Ds_c) = -β·Ds_c`, the
`screw²=rotation` relation `Dr_c = (1+β⁻¹)·Ds_c`, and the vertical values (`Dr` vertical `0`, `Ds`
vertical `↑π`), one horizontal translation `(t,0,0)` discharges both `normalize_affine_symmetries`
displacement equations. Pure `PeriodTarget` algebra; no surface data. -/
theorem center_translation_of_constraints {β : ℂ} (hβ0 : β ≠ 0)
    (hconjβ : starRingEnd ℂ β = β⁻¹) (hv : β⁻¹ - 1 ≠ 0) {Dr Ds : PeriodTarget}
    (hxDs : starRingEnd ℂ (horizC Ds) = -β * horizC Ds)
    (hCrel : horizC Dr = (1 + β⁻¹) * horizC Ds)
    (hvertDr : Dr.2.2 = (0 : AddCircle (2 * Real.pi)))
    (hvertDs : Ds.2.2 = ((Real.pi : ℝ) : AddCircle (2 * Real.pi))) :
    ∃ t : ℝ,
      Dr + ((t, 0, 0) : PeriodTarget) - PeriodTarget.rotate (β ^ 2) (t, 0, 0) = 0 ∧
      Ds + ((t, 0, 0) : PeriodTarget) - PeriodTarget.rotate β (t, 0, 0)
        = (0, 0, ((Real.pi : ℝ) : AddCircle (2 * Real.pi))) := by
  obtain ⟨t, ht⟩ := exists_real_multiple_of_conj hβ0 hconjβ hv hxDs
  refine ⟨t, ?_, ?_⟩
  · have hhoriz : horizC (Dr + ((t, 0, 0) : PeriodTarget)
        - PeriodTarget.rotate (β ^ 2) (t, 0, 0)) = 0 := by
      simp only [horizC_sub, horizC_add, horizC_rotate, horizC_xaxis]
      rw [hCrel, ht]; field_simp; ring
    obtain ⟨hc1, hc2⟩ := periodTarget_horiz_eq_zero hhoriz
    exact Prod.ext hc1 (Prod.ext hc2 (by rw [vertical_translate_eq]; exact hvertDr))
  · have hhoriz : horizC (Ds + ((t, 0, 0) : PeriodTarget)
        - PeriodTarget.rotate β (t, 0, 0)) = 0 := by
      simp only [horizC_sub, horizC_add, horizC_rotate, horizC_xaxis]
      rw [ht]; field_simp; ring
    obtain ⟨hc1, hc2⟩ := periodTarget_horiz_eq_zero hhoriz
    exact Prod.ext hc1 (Prod.ext hc2 (by rw [vertical_translate_eq]; exact hvertDs))

/-! ### Antisymmetry of `descendedIntegral` (from the cocycle + `descendedIntegral_self`). -/

lemma descendedIntegral_swap {k : ℕ} (hk : 2 ≤ k) (b w : PuncturedPlane k) :
    descendedIntegral hk w b = - descendedIntegral hk b w := by
  have h := descendedIntegral_basepoint hk b w b
  rw [descendedIntegral_self, eq_comm, add_eq_zero_iff_eq_neg] at h
  rw [h, neg_neg]

/-! ### Centering the EW displacement constants. -/

/-- Given the screw parameter `β` (`β^k = -1`, so `a := β²` has
`a^k = 1`), there is a real horizontal translation `t` whose `PeriodTarget` shift `(t, 0, 0)`
simultaneously kills the rotation displacement and reduces the screw displacement to the vertical
half-period `↑π`. These are exactly the hypotheses `hDr`/`hDs` of `normalize_affine_symmetries`
(with `a = β²`, `Dr = descendedIntegral 1 β²`, `Ds = descendedIntegral 1 β`). -/
theorem exists_center_translation {k : ℕ} (hk : 2 ≤ k) {β : ℂ} (hβk : β ^ k = -1)
    (h1 : (1 : ℂ) ∉ Surface.punctures k) (hβ : β ∉ Surface.punctures k)
    (hβ2 : β ^ 2 ∉ Surface.punctures k) :
    ∃ t : ℝ,
      descendedIntegral hk ⟨1, h1⟩ ⟨β ^ 2, hβ2⟩ + ((t, 0, 0) : PeriodTarget)
          - PeriodTarget.rotate (β ^ 2) ((t, 0, 0) : PeriodTarget) = 0 ∧
      descendedIntegral hk ⟨1, h1⟩ ⟨β, hβ⟩ + ((t, 0, 0) : PeriodTarget)
          - PeriodTarget.rotate β ((t, 0, 0) : PeriodTarget)
          = (0, 0, ((Real.pi : ℝ) : AddCircle (2 * Real.pi))) := by
  -- Basic facts about β.
  have hβ0 : β ≠ 0 := by
    intro h; rw [h, zero_pow (show k ≠ 0 by omega)] at hβk; exact absurd hβk (by norm_num)
  have hβnorm : ‖β‖ = 1 := by
    have hn : ‖β‖ ^ k = 1 := by rw [← norm_pow, hβk, norm_neg, norm_one]
    rcases lt_trichotomy ‖β‖ 1 with h | h | h
    · exact absurd hn (ne_of_lt (pow_lt_one₀ (norm_nonneg β) h (by omega)))
    · exact h
    · exact absurd hn (ne_of_gt (one_lt_pow₀ h (by omega)))
  have hconjβ : starRingEnd ℂ β = β⁻¹ := (Complex.inv_eq_conj hβnorm).symm
  have hβ2k : β ^ (2 * k) = 1 := by rw [mul_comm, pow_mul, hβk]; norm_num
  have hβne1 : β ≠ 1 := by intro h; rw [h, one_pow] at hβk; exact absurd hβk (by norm_num)
  have hv : β⁻¹ - 1 ≠ 0 := by
    rw [sub_ne_zero]; intro h; exact hβne1 (by rw [← inv_inv β, h, inv_one])
  have hβi : β⁻¹ ∉ Surface.punctures k := by
    intro h
    have hh : (β⁻¹) ^ (2 * k) = -1 := h
    rw [inv_pow, hβ2k, inv_one] at hh
    exact absurd hh (by norm_num)
  -- (A) conjMap at (1, β): descendedIntegral 1 β⁻¹ = reflY (descendedIntegral 1 β).
  have hA1 : descendedIntegral hk ⟨1, h1⟩ ⟨β⁻¹, hβi⟩
      = PeriodTarget.reflY (descendedIntegral hk ⟨1, h1⟩ ⟨β, hβ⟩) := by
    have hb : starRingEnd ℂ (⟨1, h1⟩ : PuncturedPlane k).val ∉ Surface.punctures k := by
      rw [show (⟨1, h1⟩ : PuncturedPlane k).val = 1 from rfl, map_one]; exact h1
    have hw : starRingEnd ℂ (⟨β, hβ⟩ : PuncturedPlane k).val ∉ Surface.punctures k := by
      rw [show (⟨β, hβ⟩ : PuncturedPlane k).val = β from rfl, hconjβ]; exact hβi
    have h := descendedIntegral_conjMap hk ⟨1, h1⟩ ⟨β, hβ⟩ hb hw
    rwa [show (⟨starRingEnd ℂ (⟨1, h1⟩ : PuncturedPlane k).val, hb⟩ : PuncturedPlane k) = ⟨1, h1⟩
          from Subtype.ext (show starRingEnd ℂ (1 : ℂ) = 1 by simp),
        show (⟨starRingEnd ℂ (⟨β, hβ⟩ : PuncturedPlane k).val, hw⟩ : PuncturedPlane k) = ⟨β⁻¹, hβi⟩
          from Subtype.ext (show starRingEnd ℂ β = β⁻¹ from hconjβ)] at h
  -- (A) screwMap at (β⁻¹, 1): descendedIntegral 1 β = rotate β (descendedIntegral β⁻¹ 1).
  have hA2 : descendedIntegral hk ⟨1, h1⟩ ⟨β, hβ⟩
      = PeriodTarget.rotate β (descendedIntegral hk ⟨β⁻¹, hβi⟩ ⟨1, h1⟩) := by
    have hb : β * (starRingEnd ℂ (⟨β⁻¹, hβi⟩ : PuncturedPlane k).val)⁻¹ ∉ Surface.punctures k := by
      rw [show β * (starRingEnd ℂ (⟨β⁻¹, hβi⟩ : PuncturedPlane k).val)⁻¹ = 1 from by
        rw [show (⟨β⁻¹, hβi⟩ : PuncturedPlane k).val = β⁻¹ from rfl, map_inv₀, hconjβ, inv_inv,
          mul_inv_cancel₀ hβ0]]
      exact h1
    have hw : β * (starRingEnd ℂ (⟨1, h1⟩ : PuncturedPlane k).val)⁻¹ ∉ Surface.punctures k := by
      rw [show β * (starRingEnd ℂ (⟨1, h1⟩ : PuncturedPlane k).val)⁻¹ = β from by
        rw [show (⟨1, h1⟩ : PuncturedPlane k).val = 1 from rfl, map_one, inv_one, mul_one]]
      exact hβ
    have h := descendedIntegral_screwMap hk hβk ⟨β⁻¹, hβi⟩ ⟨1, h1⟩
      (by rw [show (⟨β⁻¹, hβi⟩ : PuncturedPlane k).val = β⁻¹ from rfl]; exact inv_ne_zero hβ0)
      (by rw [show (⟨1, h1⟩ : PuncturedPlane k).val = 1 from rfl]; exact one_ne_zero) hb hw
    rwa [show (⟨β * (starRingEnd ℂ (⟨β⁻¹, hβi⟩ : PuncturedPlane k).val)⁻¹, hb⟩ : PuncturedPlane k)
            = ⟨1, h1⟩ from Subtype.ext
          (show β * (starRingEnd ℂ β⁻¹)⁻¹ = 1 by
            rw [map_inv₀, hconjβ, inv_inv, mul_inv_cancel₀ hβ0]),
        show (⟨β * (starRingEnd ℂ (⟨1, h1⟩ : PuncturedPlane k).val)⁻¹, hw⟩ : PuncturedPlane k)
            = ⟨β, hβ⟩ from Subtype.ext
          (show β * (starRingEnd ℂ (1 : ℂ))⁻¹ = β by rw [map_one, inv_one, mul_one])] at h
  -- Combine (A): conj(Ds_c) = -β · Ds_c.
  have hAc : horizC (descendedIntegral hk ⟨1, h1⟩ ⟨β, hβ⟩)
      = β⁻¹ * -(starRingEnd ℂ (horizC (descendedIntegral hk ⟨1, h1⟩ ⟨β, hβ⟩))) := by
    have hDseq : descendedIntegral hk ⟨1, h1⟩ ⟨β, hβ⟩
        = PeriodTarget.rotate β (-(PeriodTarget.reflY
            (descendedIntegral hk ⟨1, h1⟩ ⟨β, hβ⟩))) := by
      conv_lhs => rw [hA2]
      rw [descendedIntegral_swap hk ⟨1, h1⟩ ⟨β⁻¹, hβi⟩, hA1]
    have h := congrArg horizC hDseq
    rwa [horizC_rotate, horizC_neg, horizC_reflY] at h
  have hxDs : starRingEnd ℂ (horizC (descendedIntegral hk ⟨1, h1⟩ ⟨β, hβ⟩))
      = -β * horizC (descendedIntegral hk ⟨1, h1⟩ ⟨β, hβ⟩) := by
    have step : β * horizC (descendedIntegral hk ⟨1, h1⟩ ⟨β, hβ⟩)
        = -(starRingEnd ℂ (horizC (descendedIntegral hk ⟨1, h1⟩ ⟨β, hβ⟩))) := by
      conv_lhs => rw [hAc]
      rw [← mul_assoc, mul_inv_cancel₀ hβ0, one_mul]
    linear_combination step
  -- (C) screwMap at (1, β): descendedIntegral β β² = rotate β (descendedIntegral 1 β).
  have hsc : descendedIntegral hk ⟨β, hβ⟩ ⟨β ^ 2, hβ2⟩
      = PeriodTarget.rotate β (descendedIntegral hk ⟨1, h1⟩ ⟨β, hβ⟩) := by
    have hb : β * (starRingEnd ℂ (⟨1, h1⟩ : PuncturedPlane k).val)⁻¹ ∉ Surface.punctures k := by
      rw [show β * (starRingEnd ℂ (⟨1, h1⟩ : PuncturedPlane k).val)⁻¹ = β from by
        rw [show (⟨1, h1⟩ : PuncturedPlane k).val = 1 from rfl, map_one, inv_one, mul_one]]
      exact hβ
    have hw : β * (starRingEnd ℂ (⟨β, hβ⟩ : PuncturedPlane k).val)⁻¹ ∉ Surface.punctures k := by
      rw [show β * (starRingEnd ℂ (⟨β, hβ⟩ : PuncturedPlane k).val)⁻¹ = β ^ 2 from by
        rw [show (⟨β, hβ⟩ : PuncturedPlane k).val = β from rfl, hconjβ, inv_inv]; ring]
      exact hβ2
    have h := descendedIntegral_screwMap hk hβk ⟨1, h1⟩ ⟨β, hβ⟩
      (by rw [show (⟨1, h1⟩ : PuncturedPlane k).val = 1 from rfl]; exact one_ne_zero)
      (by rw [show (⟨β, hβ⟩ : PuncturedPlane k).val = β from rfl]; exact hβ0) hb hw
    rwa [show (⟨β * (starRingEnd ℂ (⟨1, h1⟩ : PuncturedPlane k).val)⁻¹, hb⟩ : PuncturedPlane k)
            = ⟨β, hβ⟩ from Subtype.ext
          (show β * (starRingEnd ℂ (1 : ℂ))⁻¹ = β by rw [map_one, inv_one, mul_one]),
        show (⟨β * (starRingEnd ℂ (⟨β, hβ⟩ : PuncturedPlane k).val)⁻¹, hw⟩ : PuncturedPlane k)
            = ⟨β ^ 2, hβ2⟩ from Subtype.ext
          (show β * (starRingEnd ℂ β)⁻¹ = β ^ 2 by rw [hconjβ, inv_inv]; ring)] at h
  have hCrel : horizC (descendedIntegral hk ⟨1, h1⟩ ⟨β ^ 2, hβ2⟩)
      = (1 + β⁻¹) * horizC (descendedIntegral hk ⟨1, h1⟩ ⟨β, hβ⟩) := by
    have hDreq : descendedIntegral hk ⟨1, h1⟩ ⟨β ^ 2, hβ2⟩
        = descendedIntegral hk ⟨1, h1⟩ ⟨β, hβ⟩
          + PeriodTarget.rotate β (descendedIntegral hk ⟨1, h1⟩ ⟨β, hβ⟩) := by
      rw [descendedIntegral_basepoint hk ⟨1, h1⟩ ⟨β, hβ⟩ ⟨β ^ 2, hβ2⟩, hsc]
    rw [hDreq, horizC_add, horizC_rotate]; ring
  -- Vertical displacement components.
  have hvertDr : (descendedIntegral hk ⟨1, h1⟩ ⟨β ^ 2, hβ2⟩).2.2 = (0 : AddCircle (2 * Real.pi)) :=
    descendedIntegral_vertical_rot hk
      (show (β ^ 2) ^ k = 1 by rw [← pow_mul, mul_comm, pow_mul, hβk]; norm_num) h1 hβ2
  have hvertDs : (descendedIntegral hk ⟨1, h1⟩ ⟨β, hβ⟩).2.2
      = ((Real.pi : ℝ) : AddCircle (2 * Real.pi)) :=
    descendedIntegral_vertical_screw hk hβk h1 hβ
  exact center_translation_of_constraints hβ0 hconjβ hv hxDs hCrel hvertDr hvertDs

end KsIndex.KarcherData
