module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section


/-! Exponential transport for certified nonvanishing C¹ pieces on compact real intervals.
The exponential of the integrated logarithmic derivative equals the endpoint ratio.
For a closed curve, the integral is a unique integer multiple of `2πi`. The hypotheses
require regularity only on the interval; no winding orientation is prescribed. -/

open Set MeasureTheory Filter
open scoped Topology

namespace KsIndex.LoopTransport

lemma logarithmicDerivative_intervalIntegrable {a b : ℝ} {γ v : ℝ → ℂ}
    (hab : a < b) (hγ : ContinuousOn γ (Icc a b))
    (hv : ContinuousOn v (Icc a b)) (hn : ∀ t ∈ Icc a b, γ t ≠ 0) :
    IntervalIntegrable (fun t => v t / γ t) volume a b := by
  have hq : ContinuousOn (fun t => v t / γ t) (Icc a b) := hv.div hγ hn
  rw [← uIcc_of_le hab.le] at hq
  exact hq.intervalIntegrable


lemma exp_integral_logarithmicDerivative {a b : ℝ} {γ v : ℝ → ℂ}
    (hab : a < b) (hγ : ContinuousOn γ (Icc a b))
    (hv : ContinuousOn v (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivWithinAt γ (v t) (Icc a b) t)
    (hn : ∀ t ∈ Icc a b, γ t ≠ 0) :
    Complex.exp (∫ t in a..b, v t / γ t) = γ b / γ a := by
  let q : ℝ → ℂ := fun t => v t / γ t
  let H : ℝ → ℂ := fun t => ∫ s in a..t, q s
  have hq : ContinuousOn q (Icc a b) := hv.div hγ hn
  have hi := logarithmicDerivative_intervalIntegrable hab hγ hv hn
  have hH : ContinuousOn H (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using
      (intervalIntegral.continuousOn_primitive_interval' hi (left_mem_uIcc (a := a) (b := b)))
  have hD : ∀ t ∈ Ioo a b, HasDerivAt H (q t) t := by
    intro t ht
    have htN : Icc a b ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    have hit : IntervalIntegrable q volume a t := hi.mono_set (by
      rw [uIcc_of_le hab.le, uIcc_of_le ht.1.le]
      exact Icc_subset_Icc le_rfl ht.2.le)
    exact intervalIntegral.integral_hasDerivAt_right hit
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
        (hq.mono Ioo_subset_Icc_self) t ht)
      (hq.continuousAt htN)
  have hF : ContinuousOn (fun t => Complex.exp (-H t) * γ t) (Icc a b) :=
    (Complex.continuous_exp.comp_continuousOn hH.neg).mul hγ
  have hFD : ∀ t ∈ Ioo a b,
      HasDerivAt (fun t => Complex.exp (-H t) * γ t) 0 t := by
    intro t ht
    have hg := (hd t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have hh := (hD t ht).neg.cexp.mul hg
    have hz : Complex.exp (-H t) * -q t * γ t + Complex.exp (-H t) * v t = 0 := by
      dsimp [q]
      field_simp [hn t ⟨ht.1.le, ht.2.le⟩]
      ring
    convert hh using 1 <;> first | rfl | exact hz.symm
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le hF hFD
    (intervalIntegrable_const (a := a) (b := b) (c := (0 : ℂ)))
  have he' : Complex.exp (-H b) * γ b = γ a := by
    have hz := he.symm
    simp only [intervalIntegral.integral_zero] at hz
    simpa [H] using (sub_eq_zero.mp hz)
  have hm := congrArg (fun z => Complex.exp (H b) * z) he'
  rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul] at hm
  exact (eq_div_iff (hn a ⟨le_rfl, hab.le⟩)).mpr hm.symm

lemma closed_integral_unique_integer {a b : ℝ} {γ v : ℝ → ℂ}
    (hab : a < b) (hγ : ContinuousOn γ (Icc a b))
    (hv : ContinuousOn v (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivWithinAt γ (v t) (Icc a b) t)
    (hn : ∀ t ∈ Icc a b, γ t ≠ 0) (hc : γ b = γ a) :
    ∃! n : ℤ, (∫ t in a..b, v t / γ t) = (n : ℂ) * (2 * Real.pi * Complex.I) := by
  have he := exp_integral_logarithmicDerivative hab hγ hv hd hn
  rw [hc, div_self (hn a ⟨le_rfl, hab.le⟩)] at he
  obtain ⟨n, hn'⟩ := Complex.exp_eq_one_iff.mp he
  refine ⟨n, hn', ?_⟩
  intro m hm
  exact_mod_cast (mul_right_cancel₀ Complex.two_pi_I_ne_zero (hm.symm.trans hn'))

end KsIndex.LoopTransport
