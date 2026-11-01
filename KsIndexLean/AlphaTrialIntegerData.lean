module

public import KsIndexLean.AlphaTrialSampleCertificate
public import KsIndexLean.IntegerQuadraticCertificate

@[expose] public section


/-! Integer numerators for the concrete trial's certified sample intervals. -/

namespace KsIndex.AlphaRemarkTrial
open PowerArc

def coefficientNumerator : Fin 25 → ℤ :=
  ![678297074,
    -3847817393,
    10105953973,
    -12255602695,
    -15903023220,
    237044154676,
    -237044154676,
    15903023220,
    12255602695,
    -10105953973,
    3847817393,
    -678297074,
    -2064148267,
    15584704300,
    -60384017740,
    157391608797,
    -309175124422,
    546623219487,
    347930602765,
    546623219487,
    -309175124422,
    157391608797,
    -60384017740,
    15584704300,
    -2064148267]

def seedNumerator (i : Fin 25) : ℤ := if i.val < 12 then 719689657 else 738631771
def seedRadius (i : Fin 25) : ℤ := if i.val < 12 then 3 else 2

def cellA (i : Fin 25) (k : ℤ) : ℤ :=
  roundedCoefficient (numerator i) 5000000 (k.natAbs % 2 : ℕ) (10^30) (k.natAbs / 2)
def cellZ (i : Fin 25) (k : ℤ) : ℤ :=
  if k.natAbs % 2 = 0 then 10^9 else seedNumerator i
def cellDelta (i : Fin 25) (k : ℤ) : ℤ :=
  if k.natAbs % 2 = 0 then 0 else seedRadius i
def cellE (i : Fin 25) (k : ℤ) : ℤ :=
  |cellA i k| * cellDelta i k + (k.natAbs / 2 : ℕ) * (|cellZ i k| + cellDelta i k)

def sampleNumerator (k : ℤ) : ℤ :=
  ∑ i : Fin 25, coefficientNumerator i * cellA i (k + shift i) * cellZ i (k + shift i)
def sampleRadius (k : ℤ) : ℤ :=
  ∑ i : Fin 25, |coefficientNumerator i| * cellE i (k + shift i)

lemma coefficient_re_eq (i : Fin 25) :
    (coefficient i).re = (coefficientNumerator i : ℝ) / 10^12 := by
  fin_cases i <;> norm_num [coefficient, coefficientNumerator]

lemma integer_cell_center (i : Fin 25) (k : ℤ) :
    integerSampleCenter (numerator i) 5000000 (10^30) (seedCenter i) k =
      ((cellA i k * cellZ i k : ℤ) : ℝ) / 10^39 := by
  unfold integerSampleCenter cellA cellZ seedCenter seedNumerator
  split_ifs <;> push_cast <;> ring

lemma integer_cell_error (i : Fin 25) (k : ℤ) :
    integerSampleError (numerator i) 5000000 (10^30) (seedCenter i) (seedError i) k =
      (cellE i k : ℝ) / 10^39 := by
  unfold integerSampleError cellE cellA cellZ cellDelta seedCenter seedError
    seedNumerator seedRadius
  split_ifs <;> simp only [Int.cast_mul, Int.cast_add, Int.cast_abs, Int.cast_natCast, abs_div]
    <;> norm_num <;> ring

lemma sampleCenter_eq_integer (k : ℤ) : sampleCenter k = (sampleNumerator k : ℝ) / 10^51 := by
  unfold sampleCenter sampleNumerator
  rw [Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [coefficient_re_eq, integer_cell_center]
  push_cast
  ring

lemma sampleError_eq_integer (k : ℤ) : sampleError k = (sampleRadius k : ℝ) / 10^51 := by
  unfold sampleError sampleRadius
  rw [Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [coefficient_re_eq, integer_cell_error, abs_div]
  push_cast
  norm_num
  ring

theorem integer_sample_certificate (k : ℤ) :
    |sample k - (sampleNumerator k : ℝ) / 10^51| ≤ (sampleRadius k : ℝ) / 10^51 := by
  simpa only [sampleCenter_eq_integer, sampleError_eq_integer] using sample_bound k

lemma sampleRadius_nonneg (k : ℤ) : 0 ≤ sampleRadius k := by
  have hh := sampleError_nonneg k
  rw [sampleError_eq_integer] at hh
  have hp : (0 : ℝ) ≤ (sampleRadius k : ℝ) := by
    have h := (le_div_iff₀ (by norm_num : (0 : ℝ) < 10^51)).mp hh
    simpa using h
  exact_mod_cast hp

def energyNumerator (s : Finset ℤ) (a b : ℤ) : ℤ :=
  ∑ n ∈ s, ((6 * n + a) ^ 2 - 4) * sampleNumerator (2 * n + b) ^ 2 / |6 * n + a|

def energyRadius (s : Finset ℤ) (a b : ℤ) : ℤ :=
  ∑ n ∈ s, (|((6 * n + a) ^ 2 - 4)| * sampleRadius (2 * n + b) *
    (2 * |sampleNumerator (2 * n + b)| + sampleRadius (2 * n + b)) / |6 * n + a| + 2)

theorem integer_energy_component (s : Finset ℤ) (a b : ℤ)
    (ha : ∀ n ∈ s, 6 * n + a ≠ 0) :
    |(∑ n ∈ s, (((6 * (n : ℝ) + a) ^ 2 - 4) / |6 * (n : ℝ) + a|) *
      sample (2 * n + b) ^ 2) - (energyNumerator s a b : ℝ) / (10^51 : ℝ) ^ 2| ≤
      (energyRadius s a b : ℝ) / (10^51 : ℝ) ^ 2 := by
  have hh := CertifiedApproximation.finite_integer_energy_error s
    (fun n => sample (2 * n + b)) (fun n => (6 * n + a) ^ 2 - 4)
    (fun n => |6 * n + a|) (fun n => sampleNumerator (2 * n + b))
    (fun n => sampleRadius (2 * n + b)) (T := 10^51) (by norm_num)
    (fun n hn => abs_pos.mpr (ha n hn)) (fun n _ => sampleRadius_nonneg _)
    (fun n _ => by
      simpa only [Int.cast_pow, Int.cast_ofNat] using integer_sample_certificate (2*n+b))
  simpa only [energyNumerator, energyRadius, Int.cast_mul, Int.cast_add, Int.cast_sub,
    Int.cast_pow, Int.cast_abs, Int.cast_ofNat] using hh

end KsIndex.AlphaRemarkTrial
