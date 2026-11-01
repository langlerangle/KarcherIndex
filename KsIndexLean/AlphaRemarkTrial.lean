module

public import KsIndexLean.PowerArcTrial

@[expose] public section


/-! A rationally specified endpoint-adapted trial for the numerical threshold.
The coefficient choices do not themselves assert a spectral sign. -/

namespace KsIndex.AlphaRemarkTrial
open PowerArc CircleQ

noncomputable def exponent : Fin 25 → ℝ :=
  ![4323618/10000000,
    4323618/10000000,
    4323618/10000000,
    4323618/10000000,
    4323618/10000000,
    4323618/10000000,
    4323618/10000000,
    4323618/10000000,
    4323618/10000000,
    4323618/10000000,
    4323618/10000000,
    4323618/10000000,
    5676382/10000000,
    5676382/10000000,
    5676382/10000000,
    5676382/10000000,
    5676382/10000000,
    5676382/10000000,
    5676382/10000000,
    5676382/10000000,
    5676382/10000000,
    5676382/10000000,
    5676382/10000000,
    5676382/10000000,
    5676382/10000000]

def shift : Fin 25 → ℤ :=
  ![6,
    5,
    4,
    3,
    2,
    1,
    -1,
    -2,
    -3,
    -4,
    -5,
    -6,
    6,
    5,
    4,
    3,
    2,
    1,
    0,
    -1,
    -2,
    -3,
    -4,
    -5,
    -6]

noncomputable def coefficient : Fin 25 → ℂ :=
  ![678297074/1000000000000,
    -3847817393/1000000000000,
    10105953973/1000000000000,
    -12255602695/1000000000000,
    -15903023220/1000000000000,
    237044154676/1000000000000,
    -237044154676/1000000000000,
    15903023220/1000000000000,
    12255602695/1000000000000,
    -10105953973/1000000000000,
    3847817393/1000000000000,
    -678297074/1000000000000,
    -2064148267/1000000000000,
    15584704300/1000000000000,
    -60384017740/1000000000000,
    157391608797/1000000000000,
    -309175124422/1000000000000,
    546623219487/1000000000000,
    347930602765/1000000000000,
    546623219487/1000000000000,
    -309175124422/1000000000000,
    157391608797/1000000000000,
    -60384017740/1000000000000,
    15584704300/1000000000000,
    -2064148267/1000000000000]

lemma exponent_pos (i : Fin 25) : 0 < exponent i := by
  fin_cases i <;> norm_num [exponent]

noncomputable def trial : ℤ → ℂ := powerTrial Finset.univ exponent shift coefficient

theorem trial_memDom : MemDom trial :=
  powerTrial_memDom _ _ _ _ (fun i _ => exponent_pos i)

theorem convS_trial (m : ℤ) :
    convS trial m = ∑ i : Fin 25, coefficient i *
      (g (exponent i) (2 * (m : ℝ) + (shift i + 1)) / g (exponent i) 0 : ℝ) :=
  convS_powerTrial _ _ _ _ (fun i _ => exponent_pos i) m

end KsIndex.AlphaRemarkTrial
