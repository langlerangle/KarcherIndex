module

public import KsIndexLean.AlphaRemainderGroupBounds
public import KsIndexLean.AlphaMiddleKappa
public import KsIndexLean.AlphaSeedApproximation

@[expose] public section


/-! Rational remainder evaluation, keeping the moment interval as an input.
The connection to rawRemainder is a separate group-identity obligation. -/
namespace KsIndex.AlphaRemarkTrial.MiddleInterval
open PowerArc GroupBounds

def ratioQ {k : ℕ} (num den : Fin k → ℤ) (n : ℚ) : ℚ :=
  (∑ i, (num i : ℚ)*(n-1024)^i.val) / (∑ i, (den i : ℚ)*(n-1024)^i.val)

theorem ratioQ_cast {k : ℕ} (num den : Fin k → ℤ) (n : ℚ) :
    (ratioQ num den n : ℝ) =
      (∑ i, (num i : ℝ)*((n : ℝ)-1024)^i.val) /
        (∑ i, (den i : ℝ)*((n : ℝ)-1024)^i.val) := by
  simp [ratioQ]

def remainderCoefficientQ (negative : Bool) (n : ℕ) : Fin 4 → ℚ :=
  if negative then
    ![ratioQ grpNum_0_0_m grpDen_0_0_m n / n, ratioQ grpNum_0_1_m grpDen_0_1_m n / n, ratioQ grpNum_1_0_m grpDen_1_0_m n / n, ratioQ grpNum_1_1_m grpDen_1_1_m n / n]
  else
    ![ratioQ grpNum_0_0_p grpDen_0_0_p n / n, ratioQ grpNum_0_1_p grpDen_0_1_p n / n, ratioQ grpNum_1_0_p grpDen_1_0_p n / n, ratioQ grpNum_1_1_p grpDen_1_1_p n / n]

noncomputable def remainderCoefficient (negative : Bool) (n : ℕ) : Fin 4 → ℝ :=
  if negative then
    ![grpValue_0_0_m n / n, grpValue_0_1_m n / n, grpValue_1_0_m n / n, grpValue_1_1_m n / n]
  else
    ![grpValue_0_0_p n / n, grpValue_0_1_p n / n, grpValue_1_0_p n / n, grpValue_1_1_p n / n]

theorem remainderCoefficientQ_cast (negative : Bool) (n : ℕ) (j : Fin 4) :
    (remainderCoefficientQ negative n j : ℝ) = remainderCoefficient negative n j := by
  cases negative <;> fin_cases j <;>
    simp [remainderCoefficientQ, remainderCoefficient, ratioQ_cast,
      grpValue_0_0_p, grpValue_0_1_p, grpValue_1_0_p, grpValue_1_1_p, grpValue_0_0_m, grpValue_0_1_m, grpValue_1_0_m, grpValue_1_1_m]

noncomputable def remainderSeed : Fin 4 → ℝ :=
  ![g (2161809/5000000) 1 / g (2161809/5000000) 0, 1,
    g (2838191/5000000) 1 / g (2838191/5000000) 0, 1]
def remainderSeedLo : Fin 4 → ℚ := ![719689654/1000000000, 1, 738631769/1000000000, 1]
def remainderSeedHi : Fin 4 → ℚ := ![719689660/1000000000, 1, 738631773/1000000000, 1]

theorem remainderSeed_enclosed (j : Fin 4) :
    (remainderSeedLo j : ℝ) ≤ remainderSeed j ∧ remainderSeed j ≤ (remainderSeedHi j : ℝ) := by
  have ha := abs_le.mp gamma_seed_approximation
  have hb := abs_le.mp beta_seed_approximation
  fin_cases j <;> norm_num [remainderSeedLo, remainderSeedHi, remainderSeed] <;> constructor <;> linarith

def momentMultiplierQ (negative : Bool) (n : ℕ) : ℚ :=
  1 / (6*n + if negative then -1 else 1)

noncomputable def remainderValue (negative : Bool) (n : ℕ) (U : ℝ) : ℝ :=
  (∑ j, remainderCoefficient negative n j * remainderSeed j) +
    (momentMultiplierQ negative n : ℝ)*U

def remainderLo (negative : Bool) (n : ℕ) (ul uh : ℚ) : ℚ :=
  groupSumLo (remainderCoefficientQ negative n) remainderSeedLo remainderSeedHi +
    scaleLo (momentMultiplierQ negative n) ul uh

def remainderHi (negative : Bool) (n : ℕ) (ul uh : ℚ) : ℚ :=
  groupSumHi (remainderCoefficientQ negative n) remainderSeedLo remainderSeedHi +
    scaleHi (momentMultiplierQ negative n) ul uh

theorem remainderValue_enclosed (negative : Bool) (n : ℕ) (ul uh : ℚ) (U : ℝ)
    (hU : (ul : ℝ) ≤ U ∧ U ≤ (uh : ℝ)) :
    (remainderLo negative n ul uh : ℝ) ≤ remainderValue negative n U ∧
      remainderValue negative n U ≤ (remainderHi negative n ul uh : ℝ) := by
  have hg := sum_sound Finset.univ
    (fun j => scaleLo (remainderCoefficientQ negative n j) (remainderSeedLo j) (remainderSeedHi j))
    (fun j => scaleHi (remainderCoefficientQ negative n j) (remainderSeedLo j) (remainderSeedHi j))
    (fun j => (remainderCoefficientQ negative n j : ℝ)*remainderSeed j)
    (fun j _ => scale_sound _ _ _ _ (remainderSeed_enclosed j))
  simp_rw [remainderCoefficientQ_cast] at hg
  have hu := scale_sound (momentMultiplierQ negative n) ul uh U hU
  constructor
  · simpa [remainderLo, remainderValue, groupSumLo] using add_le_add hg.1 hu.1
  · simpa [remainderHi, remainderValue, groupSumHi] using add_le_add hg.2 hu.2

end KsIndex.AlphaRemarkTrial.MiddleInterval
#print axioms KsIndex.AlphaRemarkTrial.MiddleInterval.remainderCoefficientQ_cast
#print axioms KsIndex.AlphaRemarkTrial.MiddleInterval.remainderValue_enclosed
