module

public import KsIndexLean.AlphaTrialIntegerData
public import KsIndexLean.PowerArcTableCertificate

@[expose] public section


/-! Finite recurrence tables supply the exact integer sample and energy
certificates once every accessed index lies in the verified prefix. -/

namespace KsIndex.AlphaRemarkTrial
open PowerArc

abbrev CoefficientTable := ℤ → ℕ → ℕ → ℤ

/-- Only the two numerators occurring in the trial and the two parities
are required. A concrete implementation may store four shared arrays. -/
def ValidCoefficientTable (N : ℕ) (t : CoefficientTable) : Prop :=
  ∀ i : Fin 25, ∀ r < 2,
    t (numerator i) r 0 = 10^30 ∧
    ∀ n < N, t (numerator i) r (n + 1) =
      (numerator i - 5000000 * ((r : ℤ) + 2 * n)) * t (numerator i) r n /
        (numerator i + 5000000 * ((r : ℤ) + 2 * n + 2))

def tableCellA (t : CoefficientTable) (i : Fin 25) (k : ℤ) : ℤ :=
  t (numerator i) (k.natAbs % 2) (k.natAbs / 2)

def tableCellE (t : CoefficientTable) (i : Fin 25) (k : ℤ) : ℤ :=
  |tableCellA t i k| * cellDelta i k +
    (k.natAbs / 2 : ℕ) * (|cellZ i k| + cellDelta i k)

def tableSampleNumerator (t : CoefficientTable) (k : ℤ) : ℤ :=
  ∑ i : Fin 25, coefficientNumerator i * tableCellA t i (k + shift i) *
    cellZ i (k + shift i)

def tableSampleRadius (t : CoefficientTable) (k : ℤ) : ℤ :=
  ∑ i : Fin 25, |coefficientNumerator i| * tableCellE t i (k + shift i)

def SampleCovered (N : ℕ) (k : ℤ) : Prop :=
  ∀ i : Fin 25, (k + shift i).natAbs / 2 ≤ N

lemma shift_natAbs_le_six (i : Fin 25) : (shift i).natAbs ≤ 6 := by
  fin_cases i <;> norm_num [shift]

/-- A single frequency bound covers every shift in the concrete trial. -/
lemma sampleCovered_of_bound {N : ℕ} {k : ℤ}
    (hk : k.natAbs + 6 ≤ 2 * N + 1) : SampleCovered N k := by
  intro i
  have ha := Int.natAbs_add_le k (shift i)
  have hs := shift_natAbs_le_six i
  omega

lemma tableCellA_eq {N : ℕ} {t : CoefficientTable}
    (ht : ValidCoefficientTable N t) (i : Fin 25) (k : ℤ)
    (hk : k.natAbs / 2 ≤ N) : tableCellA t i k = cellA i k := by
  obtain ⟨hzero, hstep⟩ := ht i (k.natAbs % 2) (Nat.mod_lt _ (by decide))
  exact roundedCoefficient_eq_of_table _ hzero hstep _ hk

lemma tableCellE_eq {N : ℕ} {t : CoefficientTable}
    (ht : ValidCoefficientTable N t) (i : Fin 25) (k : ℤ)
    (hk : k.natAbs / 2 ≤ N) : tableCellE t i k = cellE i k := by
  simp only [tableCellE, cellE, tableCellA_eq ht i k hk]

lemma tableSampleNumerator_eq {N : ℕ} {t : CoefficientTable}
    (ht : ValidCoefficientTable N t) {k : ℤ} (hk : SampleCovered N k) :
    tableSampleNumerator t k = sampleNumerator k := by
  apply Finset.sum_congr rfl
  intro i _
  rw [tableCellA_eq ht i _ (hk i)]

lemma tableSampleRadius_eq {N : ℕ} {t : CoefficientTable}
    (ht : ValidCoefficientTable N t) {k : ℤ} (hk : SampleCovered N k) :
    tableSampleRadius t k = sampleRadius k := by
  apply Finset.sum_congr rfl
  intro i _
  rw [tableCellE_eq ht i _ (hk i)]

def tableEnergyNumerator (t : CoefficientTable) (s : Finset ℤ) (a b : ℤ) : ℤ :=
  ∑ n ∈ s, ((6 * n + a) ^ 2 - 4) * tableSampleNumerator t (2 * n + b) ^ 2 /
    |6 * n + a|

def tableEnergyRadius (t : CoefficientTable) (s : Finset ℤ) (a b : ℤ) : ℤ :=
  ∑ n ∈ s, (|((6 * n + a) ^ 2 - 4)| * tableSampleRadius t (2 * n + b) *
    (2 * |tableSampleNumerator t (2 * n + b)| + tableSampleRadius t (2 * n + b)) /
      |6 * n + a| + 2)

lemma tableEnergyNumerator_eq {N : ℕ} {t : CoefficientTable}
    (ht : ValidCoefficientTable N t) (s : Finset ℤ) (a b : ℤ)
    (hc : ∀ n ∈ s, SampleCovered N (2 * n + b)) :
    tableEnergyNumerator t s a b = energyNumerator s a b := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [tableSampleNumerator_eq ht (hc n hn)]

lemma tableEnergyRadius_eq {N : ℕ} {t : CoefficientTable}
    (ht : ValidCoefficientTable N t) (s : Finset ℤ) (a b : ℤ)
    (hc : ∀ n ∈ s, SampleCovered N (2 * n + b)) :
    tableEnergyRadius t s a b = energyRadius s a b := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [tableSampleNumerator_eq ht (hc n hn), tableSampleRadius_eq ht (hc n hn)]

/-- A verified table gives the same outward finite-energy interval as the
recursive certificate. Coverage is required at every shifted sample. -/
theorem table_integer_energy_component {N : ℕ} {t : CoefficientTable}
    (ht : ValidCoefficientTable N t) (s : Finset ℤ) (a b : ℤ)
    (hc : ∀ n ∈ s, SampleCovered N (2 * n + b))
    (ha : ∀ n ∈ s, 6 * n + a ≠ 0) :
    |(∑ n ∈ s, (((6 * (n : ℝ) + a) ^ 2 - 4) / |6 * (n : ℝ) + a|) *
      sample (2 * n + b) ^ 2) - (tableEnergyNumerator t s a b : ℝ) /
        (10^51 : ℝ) ^ 2| ≤ (tableEnergyRadius t s a b : ℝ) / (10^51 : ℝ) ^ 2 := by
  rw [tableEnergyNumerator_eq ht s a b hc, tableEnergyRadius_eq ht s a b hc]
  exact integer_energy_component s a b ha

/-- Upper bound on the actual finite trial energy from the two integer
component intervals. Infinite tails remain a separate obligation. -/
theorem finite_trial_energy_le_table {N : ℕ} {t : CoefficientTable}
    (ht : ValidCoefficientTable N t) (p q : Finset ℤ) (s : ℝ)
    (hp : ∀ n ∈ p, SampleCovered N (2 * n))
    (hq : ∀ n ∈ q, SampleCovered N (2 * n + 1)) :
    (∑ n ∈ p, CircleQ.sigP n * ‖trial n‖ ^ 2) +
      s ^ 2 * ∑ n ∈ q, CircleQ.sigM n * ‖CircleQ.convS trial n‖ ^ 2 ≤
      ((tableEnergyNumerator t p 1 0 : ℝ) + tableEnergyRadius t p 1 0 +
        s ^ 2 * ((tableEnergyNumerator t q 4 1 : ℝ) + tableEnergyRadius t q 4 1)) /
        (10^51 : ℝ) ^ 2 := by
  have hP := table_integer_energy_component ht p 1 0
    (by simpa only [add_zero] using hp) (by intro n _; omega)
  have hM := table_integer_energy_component ht q 4 1 hq (by intro n _; omega)
  have hP' : (∑ n ∈ p, CircleQ.sigP n * sample (2 * n) ^ 2) ≤
      ((tableEnergyNumerator t p 1 0 : ℝ) + tableEnergyRadius t p 1 0) /
        (10^51 : ℝ) ^ 2 := by
    have hh := (abs_le.mp hP).2
    simp only [Int.cast_one, add_zero] at hh
    dsimp only [CircleQ.sigP]
    rw [add_div]
    linarith
  have hM' : (∑ n ∈ q, CircleQ.sigM n * sample (2 * n + 1) ^ 2) ≤
      ((tableEnergyNumerator t q 4 1 : ℝ) + tableEnergyRadius t q 4 1) /
        (10^51 : ℝ) ^ 2 := by
    have hh := (abs_le.mp hM).2
    norm_num only [Int.cast_ofNat, Int.cast_one] at hh
    dsimp only [CircleQ.sigM]
    rw [add_div]
    linarith
  simp only [trial_eq_sample, convS_eq_sample, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc
    _ ≤ ((tableEnergyNumerator t p 1 0 : ℝ) + tableEnergyRadius t p 1 0) /
          (10^51 : ℝ) ^ 2 +
        s ^ 2 * (((tableEnergyNumerator t q 4 1 : ℝ) + tableEnergyRadius t q 4 1) /
          (10^51 : ℝ) ^ 2) :=
      add_le_add hP' (mul_le_mul_of_nonneg_left hM' (sq_nonneg s))
    _ = _ := by ring

end KsIndex.AlphaRemarkTrial
