module

/-
KsIndexLean — Amplitude bounds after the junction change of variables.

The real-valued amplitude is `Camp η t = 2 * s (t²) * wJ η (t²)`, where
`s = sqrt ∘ sinc`. Its first two derivative expressions are `Camp1` and
`Camp2`; the derivative identities hold when `t² ≤ 1`, for arbitrary `η`.

For `0 < η ≤ 1/4` and `0 ≤ t ≤ sqrt (πη)`, the module proves
`|Camp η t| ≤ 2`,
`|Camp1 η t| ≤ 4 * sqrt (πη) * (1 + Mψ/η)`, and
`|Camp2 η t| ≤ 50 * (1 + Mψ + Mψ₂)/η`.
The amplitude vanishes at `sqrt (πη)` because `2η ≤ sin (πη)` makes the
junction cutoff zero there. The zeroth-order bound only needs `t² ≤ πη`
and does not require `t ≥ 0`.

The factors `2t` from differentiating `t²`, together with the radius
`sqrt (πη)`, control the derivative estimates. In the later Fresnel bound,
the first derivative is multiplied by this radius and the second derivative
by its square. The resulting constant can be bounded independently of `η`
on the stated range; the individual derivative bounds need not be uniform.
-/
public import KsIndexLean.ArcJunction

@[expose] public section


noncomputable section

open Real Set
open KsIndex.SincKit KsIndex.JunctionCut KsIndex.ArcJunction
open KsIndex.PunctureCutoff KsIndex.CutLaplacian

namespace KsIndex.JunctionAmp

/-! ### Product-bound helpers -/

lemma abs_mul2_le {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) ((abs_nonneg a).trans ha)

lemma abs_mul3_le {a b c A B C : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) :
    |a * b * c| ≤ A * B * C :=
  abs_mul2_le (abs_mul2_le ha hb) hc

/-! ### The amplitude and its two derivatives -/

/-- The peeled junction amplitude `2·s(t²)·wJ η (t²)`. -/
def Camp (η t : ℝ) : ℝ := 2 * (s (t ^ 2) * wJ η (t ^ 2))

/-- Its derivative. -/
def Camp1 (η t : ℝ) : ℝ :=
  2 * (ds (t ^ 2) * (2 * t) * wJ η (t ^ 2) + s (t ^ 2) * (wJ1 η (t ^ 2) * (2 * t)))

/-- Its second derivative. -/
def Camp2 (η t : ℝ) : ℝ :=
  2 * ((d2s (t ^ 2) * (2 * t) * (2 * t) + ds (t ^ 2) * 2) * wJ η (t ^ 2)
    + ds (t ^ 2) * (2 * t) * (wJ1 η (t ^ 2) * (2 * t))
    + (ds (t ^ 2) * (2 * t) * (wJ1 η (t ^ 2) * (2 * t))
      + s (t ^ 2) * (wJ2 η (t ^ 2) * (2 * t) * (2 * t) + wJ1 η (t ^ 2) * 2)))

/-! ### The chain rule through `q = t²` -/

lemma hasDerivAt_sq (t : ℝ) : HasDerivAt (fun y : ℝ => y ^ 2) (2 * t) t := by
  simpa using hasDerivAt_pow 2 t

lemma hasDerivAt_Camp {η t : ℝ} (h1 : t ^ 2 ≤ 1) : HasDerivAt (Camp η) (Camp1 η t) t := by
  have hq := hasDerivAt_sq t
  have hs_q := HasDerivAt.comp (h := fun y : ℝ => y ^ 2) t (hasDerivAt_s (sq_nonneg t) h1) hq
  have hw_q := HasDerivAt.comp (h := fun y : ℝ => y ^ 2) t (hasDerivAt_wJ η (t ^ 2)) hq
  exact (hs_q.mul hw_q).const_mul 2

lemma hasDerivAt_Camp1 {η t : ℝ} (h1 : t ^ 2 ≤ 1) : HasDerivAt (Camp1 η) (Camp2 η t) t := by
  have hq := hasDerivAt_sq t
  have hs_q := HasDerivAt.comp (h := fun y : ℝ => y ^ 2) t (hasDerivAt_s (sq_nonneg t) h1) hq
  have hw_q := HasDerivAt.comp (h := fun y : ℝ => y ^ 2) t (hasDerivAt_wJ η (t ^ 2)) hq
  have hds_q := HasDerivAt.comp (h := fun y : ℝ => y ^ 2) t (hasDerivAt_ds (sq_nonneg t) h1) hq
  have hw1_q := HasDerivAt.comp (h := fun y : ℝ => y ^ 2) t (hasDerivAt_wJ1 η (t ^ 2)) hq
  have h2t : HasDerivAt (fun y : ℝ => 2 * y) 2 t := by
    simpa using (hasDerivAt_id t).const_mul 2
  exact (((hds_q.mul h2t).mul hw_q).add (hs_q.mul ((hw1_q.mul h2t)))).const_mul 2

/-! ### The endpoint vanishing -/

lemma Camp_root_eq_zero {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1/4) :
    Camp η (Real.sqrt (π * η)) = 0 := by
  rw [Camp, Real.sq_sqrt (by positivity : (0:ℝ) ≤ π * η),
    wJ_eq_zero hη0 (two_eta_le_sin_pi_eta hη0 hη), mul_zero, mul_zero]

/-! ### The pointwise budget bounds -/

section Bounds

variable {η t : ℝ} (hη0 : 0 < η) (hη : η ≤ 1/4) (ht0 : 0 ≤ t) (ht : t ^ 2 ≤ π * η)

include hη0 hη ht in
omit ht0 in
lemma sq_le_one_of_le : t ^ 2 ≤ 1 := by
  have hπ : π < 3.15 := Real.pi_lt_d2
  nlinarith

include ht0 ht in
omit hη0 hη in
lemma le_sqrt_pi_eta : t ≤ Real.sqrt (π * η) := by
  have h := Real.sqrt_le_sqrt ht
  rwa [Real.sqrt_sq ht0] at h

include hη0 hη ht in
omit ht0 in
lemma abs_Camp_le : |Camp η t| ≤ 2 := by
  have h1 : t ^ 2 ≤ 1 := sq_le_one_of_le hη0 hη ht
  have hs1 : |s (t ^ 2)| ≤ 1 :=
    abs_le.mpr ⟨by linarith [s_nonneg (t ^ 2)], s_le_one (t ^ 2)⟩
  have hw : |wJ η (t ^ 2)| ≤ 1 :=
    abs_le.mpr ⟨by linarith [(wJ_mem η (t ^ 2)).1], (wJ_mem η (t ^ 2)).2⟩
  calc |Camp η t| = |(2 : ℝ) * (s (t ^ 2) * wJ η (t ^ 2))| := rfl
    _ ≤ 2 * (1 * 1) := abs_mul2_le (by rw [abs_two]) (abs_mul2_le hs1 hw)
    _ = 2 := by norm_num

include hη0 hη ht0 ht in
lemma abs_Camp1_le : |Camp1 η t| ≤ 4 * Real.sqrt (π * η) * (1 + Mψ / η) := by
  have h1 : t ^ 2 ≤ 1 := sq_le_one_of_le hη0 hη ht
  have htR : t ≤ Real.sqrt (π * η) := le_sqrt_pi_eta ht0 ht
  have hs1 : |s (t ^ 2)| ≤ 1 :=
    abs_le.mpr ⟨by linarith [s_nonneg (t ^ 2)], s_le_one (t ^ 2)⟩
  have hw : |wJ η (t ^ 2)| ≤ 1 :=
    abs_le.mpr ⟨by linarith [(wJ_mem η (t ^ 2)).1], (wJ_mem η (t ^ 2)).2⟩
  have hds : |ds (t ^ 2)| ≤ 1 :=
    le_trans (abs_ds_le (sq_nonneg t) h1) (by linarith)
  have hw1 : |wJ1 η (t ^ 2)| ≤ Mψ / η := abs_wJ1_le hη0 _
  have h2t : |2 * t| ≤ 2 * Real.sqrt (π * η) := by
    rw [abs_mul, abs_two, abs_of_nonneg ht0]
    linarith
  have hMη : (0:ℝ) ≤ Mψ / η := div_nonneg Mψ_nonneg hη0.le
  have hsqnn := Real.sqrt_nonneg (π * η)
  calc |Camp1 η t|
      = |(2:ℝ) * (ds (t ^ 2) * (2 * t) * wJ η (t ^ 2)
        + s (t ^ 2) * (wJ1 η (t ^ 2) * (2 * t)))| := rfl
    _ ≤ 2 * (|ds (t ^ 2) * (2 * t) * wJ η (t ^ 2)|
        + |s (t ^ 2) * (wJ1 η (t ^ 2) * (2 * t))|) :=
        abs_mul2_le (by rw [abs_two]) (abs_add_le _ _)
    _ ≤ 2 * (1 * (2 * Real.sqrt (π * η)) * 1
        + 1 * (Mψ / η * (2 * Real.sqrt (π * η)))) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by norm_num)
        · exact abs_mul3_le hds h2t hw
        · exact abs_mul2_le hs1 (abs_mul2_le hw1 h2t)
    _ = 4 * Real.sqrt (π * η) * (1 + Mψ / η) := by ring

include hη0 hη ht0 ht in
lemma abs_Camp2_le : |Camp2 η t| ≤ 50 * (1 + Mψ + Mψ₂) / η := by
  have h1 : t ^ 2 ≤ 1 := sq_le_one_of_le hη0 hη ht
  have hπ1 : 3.14 < π := Real.pi_gt_d2
  have hπ2 : π < 3.15 := Real.pi_lt_d2
  have hRR : Real.sqrt (π * η) * Real.sqrt (π * η) = π * η :=
    Real.mul_self_sqrt (by positivity)
  have hs1 : |s (t ^ 2)| ≤ 1 :=
    abs_le.mpr ⟨by linarith [s_nonneg (t ^ 2)], s_le_one (t ^ 2)⟩
  have hw : |wJ η (t ^ 2)| ≤ 1 :=
    abs_le.mpr ⟨by linarith [(wJ_mem η (t ^ 2)).1], (wJ_mem η (t ^ 2)).2⟩
  have hds : |ds (t ^ 2)| ≤ 1 :=
    le_trans (abs_ds_le (sq_nonneg t) h1) (by linarith)
  have hd2s : |d2s (t ^ 2)| ≤ 1/2 := abs_d2s_le (sq_nonneg t) h1
  have hw1 : |wJ1 η (t ^ 2)| ≤ Mψ / η := abs_wJ1_le hη0 _
  have hw2 : |wJ2 η (t ^ 2)| ≤ (Mψ₂ + Mψ) / η ^ 2 := abs_wJ2_le hη0 (by linarith) _
  have h2t : |2 * t| ≤ 2 * Real.sqrt (π * η) := by
    rw [abs_mul, abs_two, abs_of_nonneg ht0]
    linarith [le_sqrt_pi_eta ht0 ht]
  have habs2 : |(2:ℝ)| ≤ 2 := by rw [abs_two]
  have hMη : (0:ℝ) ≤ Mψ / η := div_nonneg Mψ_nonneg hη0.le
  have hM2η : (0:ℝ) ≤ (Mψ₂ + Mψ) / η ^ 2 :=
    div_nonneg (by linarith [Mψ_nonneg, Mψ₂_nonneg]) (by positivity)
  have hsqnn := Real.sqrt_nonneg (π * η)
  set A : ℝ := Real.sqrt (π * η) with hA
  -- the four grouped pieces
  have hX : |(d2s (t ^ 2) * (2 * t) * (2 * t) + ds (t ^ 2) * 2) * wJ η (t ^ 2)|
      ≤ (1/2 * (2 * A) * (2 * A) + 1 * 2) * 1 := by
    refine abs_mul2_le ?_ hw
    calc |d2s (t ^ 2) * (2 * t) * (2 * t) + ds (t ^ 2) * 2|
        ≤ |d2s (t ^ 2) * (2 * t) * (2 * t)| + |ds (t ^ 2) * 2| := abs_add_le _ _
      _ ≤ 1/2 * (2 * A) * (2 * A) + 1 * 2 :=
          add_le_add (abs_mul3_le hd2s h2t h2t) (abs_mul2_le hds habs2)
  have hcross : |ds (t ^ 2) * (2 * t) * (wJ1 η (t ^ 2) * (2 * t))|
      ≤ 1 * (2 * A) * (Mψ / η * (2 * A)) :=
    abs_mul3_le hds h2t (abs_mul2_le hw1 h2t)
  have hY : |s (t ^ 2) * (wJ2 η (t ^ 2) * (2 * t) * (2 * t) + wJ1 η (t ^ 2) * 2)|
      ≤ 1 * ((Mψ₂ + Mψ) / η ^ 2 * (2 * A) * (2 * A) + Mψ / η * 2) := by
    refine abs_mul2_le hs1 ?_
    calc |wJ2 η (t ^ 2) * (2 * t) * (2 * t) + wJ1 η (t ^ 2) * 2|
        ≤ |wJ2 η (t ^ 2) * (2 * t) * (2 * t)| + |wJ1 η (t ^ 2) * 2| := abs_add_le _ _
      _ ≤ (Mψ₂ + Mψ) / η ^ 2 * (2 * A) * (2 * A) + Mψ / η * 2 :=
          add_le_add (abs_mul3_le hw2 h2t h2t) (abs_mul2_le hw1 habs2)
  -- triangle assembly
  have hsum : |Camp2 η t|
      ≤ 2 * (((1/2 * (2 * A) * (2 * A) + 1 * 2) * 1
        + 1 * (2 * A) * (Mψ / η * (2 * A)))
        + (1 * (2 * A) * (Mψ / η * (2 * A))
          + 1 * ((Mψ₂ + Mψ) / η ^ 2 * (2 * A) * (2 * A) + Mψ / η * 2))) := by
    refine abs_mul2_le (by rw [abs_two]) ?_
    calc |(d2s (t ^ 2) * (2 * t) * (2 * t) + ds (t ^ 2) * 2) * wJ η (t ^ 2)
        + ds (t ^ 2) * (2 * t) * (wJ1 η (t ^ 2) * (2 * t))
        + (ds (t ^ 2) * (2 * t) * (wJ1 η (t ^ 2) * (2 * t))
          + s (t ^ 2) * (wJ2 η (t ^ 2) * (2 * t) * (2 * t) + wJ1 η (t ^ 2) * 2))|
        ≤ |(d2s (t ^ 2) * (2 * t) * (2 * t) + ds (t ^ 2) * 2) * wJ η (t ^ 2)
            + ds (t ^ 2) * (2 * t) * (wJ1 η (t ^ 2) * (2 * t))|
          + |ds (t ^ 2) * (2 * t) * (wJ1 η (t ^ 2) * (2 * t))
            + s (t ^ 2) * (wJ2 η (t ^ 2) * (2 * t) * (2 * t) + wJ1 η (t ^ 2) * 2)| :=
          abs_add_le _ _
      _ ≤ (|(d2s (t ^ 2) * (2 * t) * (2 * t) + ds (t ^ 2) * 2) * wJ η (t ^ 2)|
            + |ds (t ^ 2) * (2 * t) * (wJ1 η (t ^ 2) * (2 * t))|)
          + (|ds (t ^ 2) * (2 * t) * (wJ1 η (t ^ 2) * (2 * t))|
            + |s (t ^ 2) * (wJ2 η (t ^ 2) * (2 * t) * (2 * t) + wJ1 η (t ^ 2) * 2)|) :=
          add_le_add (abs_add_le _ _) (abs_add_le _ _)
      _ ≤ _ := add_le_add (add_le_add hX hcross) (add_le_add hcross hY)
  -- the numeric collapse
  have hπη : π * η ≤ 0.7875 := by nlinarith
  have hAA4 : (2 * A) * (2 * A) = 4 * (π * η) := by
    calc (2 * A) * (2 * A) = 4 * (A * A) := by ring
      _ = 4 * (π * η) := by rw [hRR]
  have e1 : 1 * (2 * A) * (Mψ / η * (2 * A)) = 4 * π * Mψ := by
    calc 1 * (2 * A) * (Mψ / η * (2 * A)) = (2 * A) * (2 * A) * (Mψ / η) := by ring
      _ = 4 * (π * η) * (Mψ / η) := by rw [hAA4]
      _ = 4 * π * Mψ := by field_simp
  have e2 : 1 * ((Mψ₂ + Mψ) / η ^ 2 * (2 * A) * (2 * A) + Mψ / η * 2)
      = 4 * π * (Mψ₂ + Mψ) / η + 2 * Mψ / η := by
    have h1 : (Mψ₂ + Mψ) / η ^ 2 * (2 * A) * (2 * A)
        = (Mψ₂ + Mψ) / η ^ 2 * (4 * (π * η)) := by
      rw [mul_assoc, hAA4]
    rw [one_mul, h1]
    field_simp
  have e3 : (1/2 * (2 * A) * (2 * A) + 1 * 2) * 1 = 2 * (π * η) + 2 := by
    have h1 : 1/2 * (2 * A) * (2 * A) = 1/2 * ((2 * A) * (2 * A)) := by ring
    rw [one_mul, mul_one, h1, hAA4]
    ring
  rw [e1, e2, e3] at hsum
  refine le_trans hsum ?_
  have hnum : 2 * ((2 * (π * η) + 2 + 4 * π * Mψ)
      + (4 * π * Mψ + (4 * π * (Mψ₂ + Mψ) / η + 2 * Mψ / η)))
      = (4 * π * η ^ 2 + 4 * η + 16 * π * Mψ * η + 8 * π * (Mψ₂ + Mψ) + 4 * Mψ) / η := by
    field_simp
    ring
  rw [hnum, div_eq_mul_inv, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr hη0.le)
  nlinarith [mul_le_mul_of_nonneg_right hπη Mψ_nonneg, Mψ_nonneg, Mψ₂_nonneg,
    mul_le_mul_of_nonneg_right hπη hη0.le, hη0, hη, hπ2,
    mul_nonneg Mψ_nonneg hη0.le, mul_nonneg Mψ₂_nonneg hη0.le]

end Bounds

end KsIndex.JunctionAmp
