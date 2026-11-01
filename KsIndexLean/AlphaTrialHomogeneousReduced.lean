module

public import KsIndexLean.AlphaGroupMultiplierBridge

@[expose] public section


/-! The actual trial's homogeneous coefficient in the same groups as its transforms. -/
noncomputable section
namespace KsIndex.OppositeHalf
open CircleQ PowerArc KsIndex.AlphaRemarkTrial

theorem group_homogeneous_reduced (s : Finset (Fin 25)) (β r n : ℝ)
    (hβ : 0 < β) (hr : 0 ≤ 2*n+9-r)
    (hfacts : ∀ i ∈ s, exponent i = β ∧ baseR i = r) :
    (∑ i ∈ s, (coefficient i).re *
      (g (exponent i) (2*n+shift i) / g (exponent i) 0)) =
      (g β (2*n+9-r)/g β 0) * trialGroupMult s β r (n+9/2) := by
  rw [trialGroupMult_eq_normalized, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hrel := chainLen_rel i
  rw [(hfacts i hi).2] at hrel
  have harg : (2*n+9-r)+2*chainLen i = 2*n+shift i := by linarith
  have hg := g_eq_normalizedCoefficient hβ hr (chainLen i)
  rw [harg] at hg
  rw [(hfacts i hi).1, hg,
    show 2*(n+9/2)-r = 2*n+9-r by ring]
  ring

end KsIndex.OppositeHalf

namespace KsIndex.AlphaRemarkTrial
open CircleQ PowerArc OppositeHalf

lemma trial_re_eq_sum (n : ℤ) : (trial n).re =
    ∑ i : Fin 25, (coefficient i).re *
      (g (exponent i) (2*(n : ℝ)+shift i)/g (exponent i) 0) := by
  simp [trial, powerTrial, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    normalizedPowerField_apply, Complex.mul_re]

def reducedTrial (n : ℝ) : ℝ :=
  (g (4323618/10000000) (2*n-6)/g (4323618/10000000) 0) *
    trialGroupMult grpAe (4323618/10000000) 15 (n+9/2) +
  (g (4323618/10000000) (2*n-5)/g (4323618/10000000) 0) *
    trialGroupMult grpAo (4323618/10000000) 14 (n+9/2) +
  ((g (5676382/10000000) (2*n-6)/g (5676382/10000000) 0) *
    trialGroupMult grpBe (5676382/10000000) 15 (n+9/2) +
  (g (5676382/10000000) (2*n-5)/g (5676382/10000000) 0) *
    trialGroupMult grpBo (5676382/10000000) 14 (n+9/2))

theorem trial_re_eq_reduced (n : ℤ) (hn : 3 ≤ n) :
    (trial n).re = reducedTrial n := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [trial_re_eq_sum, sum_four_groups]
  rw [group_homogeneous_reduced grpAe _ 15 n (by norm_num) (by linarith)
      (fun i hi => grpAe_facts hi),
    group_homogeneous_reduced grpAo _ 14 n (by norm_num) (by linarith)
      (fun i hi => grpAo_facts hi),
    group_homogeneous_reduced grpBe _ 15 n (by norm_num) (by linarith)
      (fun i hi => grpBe_facts hi),
    group_homogeneous_reduced grpBo _ 14 n (by norm_num) (by linarith)
      (fun i hi => grpBo_facts hi)]
  unfold reducedTrial
  congr 3 <;> congr 2 <;> ring

end KsIndex.AlphaRemarkTrial
