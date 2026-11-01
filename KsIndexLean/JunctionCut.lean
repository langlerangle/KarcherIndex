module

/-
KsIndexLean — Junction cutoff and its first two derivatives.

Under either junction substitution `θ = π/2-x` or `θ = x-π/2`, the
complement of the cosine collar factor becomes
`wJ η x = 1 - smoothTransition ((sin x - η)/η)`.
This identity, continuity, the range `[0,1]`, and the derivative identities
for `wJ1` and `wJ2` hold for every real `η`.

For `η > 0`, the cutoff equals `1` where `sin x ≤ η` and `0` where
`2η ≤ sin x`, and its first derivative satisfies `|wJ1 η x| ≤ Mψ/η`.
For `0 < η ≤ 1`, its second derivative satisfies
`|wJ2 η x| ≤ (Mψ₂ + Mψ)/η²`.
Here `PunctureCutoff.Mψ` and `CutLaplacian.Mψ₂` are chosen nonnegative
upper bounds for the first two derivatives of `smoothTransition`; they
are not defined as least upper bounds. These estimates supply the
junction amplitude used in the subsequent oscillatory-integral bounds.
-/
public import KsIndexLean.PunctureCutoff
public import KsIndexLean.CutLaplacian
public import KsIndexLean.SincKit
public import KsIndexLean.ArcField

@[expose] public section


noncomputable section

open Real Set KsIndex.PunctureCutoff KsIndex.CutLaplacian

namespace KsIndex.JunctionCut

/-- The junction cutoff: for `η > 0`, it is `1` where `sin x ≤ η` and `0` where `sin x ≥ 2η`. -/
def wJ (η x : ℝ) : ℝ := 1 - Real.smoothTransition ((Real.sin x - η) / η)

/-- First derivative of `wJ η`. -/
def wJ1 (η x : ℝ) : ℝ :=
  -(deriv Real.smoothTransition ((Real.sin x - η) / η) * (Real.cos x / η))

/-- Second derivative of `wJ η`. -/
def wJ2 (η x : ℝ) : ℝ :=
  -(deriv (deriv Real.smoothTransition) ((Real.sin x - η) / η) * (Real.cos x / η)
      * (Real.cos x / η)
    + deriv Real.smoothTransition ((Real.sin x - η) / η) * (-Real.sin x / η))

/-! ### Values and the link to the θ-side collar -/

lemma wJ_mem (η x : ℝ) : wJ η x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨by simp only [wJ]; linarith [Real.smoothTransition.le_one ((Real.sin x - η) / η)],
    by simp only [wJ]; linarith [Real.smoothTransition.nonneg ((Real.sin x - η) / η)]⟩

lemma wJ_eq_zero {η x : ℝ} (hη : 0 < η) (h : 2 * η ≤ Real.sin x) : wJ η x = 0 := by
  simp only [wJ]
  rw [Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hη]; linarith)]
  ring

lemma wJ_eq_one {η x : ℝ} (hη : 0 < η) (h : Real.sin x ≤ η) : wJ η x = 1 := by
  simp only [wJ]
  rw [Real.smoothTransition.zero_of_nonpos (by rw [div_le_iff₀ hη]; linarith)]
  ring

/-- Right junction: `θ = π/2 − x` turns the collar complement into `wJ`. -/
lemma wJ_eq_sub_right_junction (η x : ℝ) :
    1 - KsIndex.ArcField.wCol η (π / 2 - x) = wJ η x := by
  simp only [KsIndex.ArcField.wCol, wJ, Real.cos_pi_div_two_sub]

/-- Left junction: `θ = x − π/2` turns the collar complement into `wJ`. -/
lemma wJ_eq_sub_left_junction (η x : ℝ) :
    1 - KsIndex.ArcField.wCol η (x - π / 2) = wJ η x := by
  simp only [KsIndex.ArcField.wCol, wJ]
  rw [show x - π / 2 = -(π / 2 - x) by ring, Real.cos_neg, Real.cos_pi_div_two_sub]

lemma continuous_wJ (η : ℝ) : Continuous (wJ η) :=
  continuous_const.sub (Real.smoothTransition.continuous.comp
    ((Real.continuous_sin.sub continuous_const).div_const η))

/-! ### The derivative package -/

/-- The inner map `x ↦ (sin x − η)/η` has derivative `cos x/η`. -/
lemma hasDerivAt_inner (η : ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (Real.sin y - η) / η) (Real.cos x / η) x :=
  ((Real.hasDerivAt_sin x).sub_const η).div_const η

lemma hasDerivAt_wJ (η : ℝ) (x : ℝ) : HasDerivAt (wJ η) (wJ1 η x) x := by
  have hψ : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((Real.sin x - η) / η)) ((Real.sin x - η) / η) :=
    (((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)) _).hasDerivAt
  have hcomp := hψ.comp x (hasDerivAt_inner η x)
  exact hcomp.const_sub 1

lemma hasDerivAt_wJ1 (η : ℝ) (x : ℝ) : HasDerivAt (wJ1 η) (wJ2 η x) x := by
  have hd1 : ContDiff ℝ 1 (deriv Real.smoothTransition) :=
    (contDiff_succ_iff_deriv.mp (Real.smoothTransition.contDiff (n := 2))).2.2
  have hψ' : HasDerivAt (deriv Real.smoothTransition)
      (deriv (deriv Real.smoothTransition) ((Real.sin x - η) / η)) ((Real.sin x - η) / η) :=
    ((hd1.differentiable (by norm_num)) _).hasDerivAt
  have hc1 := hψ'.comp x (hasDerivAt_inner η x)
  have hc2 : HasDerivAt (fun y : ℝ => Real.cos y / η) (-Real.sin x / η) x :=
    (Real.hasDerivAt_cos x).div_const η
  exact (hc1.mul hc2).neg

/-! ### The budget bounds -/

lemma abs_wJ1_le {η : ℝ} (hη : 0 < η) (x : ℝ) : |wJ1 η x| ≤ Mψ / η := by
  simp only [wJ1, abs_neg, abs_mul]
  calc |deriv Real.smoothTransition ((Real.sin x - η) / η)| * |Real.cos x / η|
      ≤ Mψ * (1 / η) :=
        mul_le_mul (abs_deriv_smoothTransition_le _)
          (KsIndex.SincKit.abs_div_le (Real.abs_cos_le_one x) hη le_rfl)
          (abs_nonneg _) Mψ_nonneg
    _ = Mψ / η := by ring

lemma abs_wJ2_le {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (x : ℝ) :
    |wJ2 η x| ≤ (Mψ₂ + Mψ) / η ^ 2 := by
  have h1 : |Real.cos x / η| ≤ 1 / η :=
    KsIndex.SincKit.abs_div_le (Real.abs_cos_le_one x) hη le_rfl
  have h2 : |-Real.sin x / η| ≤ 1 / η :=
    KsIndex.SincKit.abs_div_le (by rw [abs_neg]; exact Real.abs_sin_le_one x) hη le_rfl
  have hinv : 1 / η ≤ 1 / η ^ 2 := by
    rw [one_div, one_div]
    exact inv_anti₀ (by positivity) (by nlinarith)
  have h1nn : (0 : ℝ) ≤ 1 / η := by positivity
  simp only [wJ2, abs_neg]
  calc |deriv (deriv Real.smoothTransition) ((Real.sin x - η) / η) * (Real.cos x / η)
        * (Real.cos x / η)
      + deriv Real.smoothTransition ((Real.sin x - η) / η) * (-Real.sin x / η)|
      ≤ |deriv (deriv Real.smoothTransition) ((Real.sin x - η) / η) * (Real.cos x / η)
          * (Real.cos x / η)|
        + |deriv Real.smoothTransition ((Real.sin x - η) / η) * (-Real.sin x / η)| :=
        abs_add_le _ _
    _ = |deriv (deriv Real.smoothTransition) ((Real.sin x - η) / η)| * |Real.cos x / η|
          * |Real.cos x / η|
        + |deriv Real.smoothTransition ((Real.sin x - η) / η)| * |-Real.sin x / η| := by
        rw [abs_mul, abs_mul, abs_mul]
    _ ≤ Mψ₂ * (1 / η) * (1 / η) + Mψ * (1 / η) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul
            (mul_le_mul (abs_deriv2_smoothTransition_le _) h1 (abs_nonneg _) Mψ₂_nonneg)
            h1 (abs_nonneg _) (mul_nonneg Mψ₂_nonneg h1nn)
        · exact mul_le_mul (abs_deriv_smoothTransition_le _) h2 (abs_nonneg _) Mψ_nonneg
    _ = Mψ₂ / η ^ 2 + Mψ * (1 / η) := by ring
    _ ≤ Mψ₂ / η ^ 2 + Mψ * (1 / η ^ 2) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hinv Mψ_nonneg)
    _ = (Mψ₂ + Mψ) / η ^ 2 := by ring

end KsIndex.JunctionCut
