module

public import KsIndexLean.ComplexRadialClassification
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section


noncomputable section
namespace KsIndex.Radial
open Set

lemma uD_one {k : ℕ} (hk : 2 ≤ k) (ℓ : ℕ) :
    uD k ℓ 1 = (ℓ : ℝ) ^ 2 - kap k ^ 2 := by
  rw [uD, uRad_one hk, gD_one hk]
  simp only [div_one, one_pow, one_mul]
  ring

lemma uD_one_ne_zero {k ℓ : ℕ} (hk : 2 ≤ k) (hℓ : ℓ ≠ k - 1) : uD k ℓ 1 ≠ 0 := by
  rw [uD_one hk]
  have hkcast : kap k = ((k - 1 : ℕ) : ℝ) := by
    unfold kap
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hkcast]
  have hn : (ℓ : ℝ) ≠ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hℓ
  intro he
  apply hn
  have hpos : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg _
  have hkpos : (0 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- A one-sided Neumann condition on a regular multiple forces its coefficient
or its explicit mode derivative to vanish. No extension beyond the disk is used. -/
lemma regular_mode_neumann_coefficient {k ℓ : ℕ} (hk : 2 ≤ k)
    {f : ℝ → ℂ} {c : ℂ}
    (hc : ∀ r ∈ Icc (0:ℝ) 1, f r = c * (uRad k ℓ r : ℂ))
    (hn : HasDerivWithinAt f 0 (Icc (0:ℝ) 1) 1) : c * (uD k ℓ 1 : ℂ) = 0 := by
  have hu := ((uRad_hasDerivAt hk ℓ (by norm_num : (1 : ℝ) ≠ 0)).ofReal_comp.const_mul c)
  have hf : HasDerivWithinAt f (c * (uD k ℓ 1 : ℂ)) (Icc (0:ℝ) 1) 1 :=
    hu.hasDerivWithinAt.congr_of_mem hc (by norm_num)
  exact UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Icc_zero_one 1 (by norm_num)) hf hn

/-- Only the resonant angular frequency k-1 can survive regular Neumann data. -/
lemma regular_neumann_nonresonant_mode_vanishes {k ℓ : ℕ} (hk : 2 ≤ k)
    (hℓ : ℓ ≠ k - 1) {f f' : ℝ → ℂ}
    (hfc : ContinuousOn f (Icc 0 1)) (hf'c : ContinuousOn f' (Ico 0 1))
    (hd : ∀ r ∈ Ioo (0:ℝ) 1, HasDerivAt f (f' r) r)
    (hode : ∀ r ∈ Ioo (0:ℝ) 1,
      HasDerivAt (fun r : ℝ => (r : ℂ) * f' r)
        (((ℓ : ℂ) ^ 2 * f r / (r : ℂ)) - (r : ℂ) * (Vrad k r : ℂ) * f r) r)
    (hn : HasDerivWithinAt f 0 (Icc (0:ℝ) 1) 1) :
    ∀ r ∈ Icc (0:ℝ) 1, f r = 0 := by
  obtain ⟨c, hc⟩ := eq_const_mul_uRad_complex_closed hk ℓ hfc hf'c hd hode
  have he := regular_mode_neumann_coefficient hk hc hn
  have hu : (uD k ℓ 1 : ℂ) ≠ 0 := by exact_mod_cast uD_one_ne_zero hk hℓ
  have hz : c = 0 := (mul_eq_zero.mp he).resolve_right hu
  intro r hr
  rw [hc r hr, hz, zero_mul]

end KsIndex.Radial
