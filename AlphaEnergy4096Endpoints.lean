module
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaTrialTableData
@[expose] public section
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
namespace KsIndex.AlphaRemarkTrial.Energy4096Endpoints
open PowerArc

theorem ratio_table {N : ℕ} {t : CoefficientTable}
    (ht : ValidCoefficientTable N t) (i : Fin 25) (k : ℤ)
    (hcov : k.natAbs / 2 ≤ N) {A Z E : ℤ}
    (hA : tableCellA t i k = A) (hZ : cellZ i k = Z)
    (hE : tableCellE t i k = E) :
    |g (exponent i) k / g (exponent i) 0 - ((A * Z : ℤ) : ℝ) / 10^39| ≤
      (E : ℝ) / 10^39 := by
  have h := integerSample_bound (numerator_pos i) (by norm_num : (0 : ℤ) < 5000000)
    (by norm_num : (0 : ℤ) < 10^30) (seed_error i) k
  rw [integer_cell_center, integer_cell_error] at h
  have ha : cellA i k = A := by rw [← tableCellA_eq ht i k hcov, hA]
  have he : cellE i k = E := by rw [← tableCellE_eq ht i k hcov, hE]
  rw [ha, hZ, he] at h
  simpa only [exponent_eq, Int.cast_ofNat] using h

theorem Pplus_0 :
    |g (exponent 0) 8200 / g (exponent 0) 0 -
      (((-1116900560304796976861606 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4100000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 0 8200 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pplus_1 :
    |g (exponent 1) 8199 / g (exponent 1) 0 -
      (((-1922788413836854343628324 : ℤ) * 719689657 : ℤ) : ℝ) / 10^39| ≤
      (5768365241513513038801312 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 1 8199 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pplus_2 :
    |g (exponent 2) 8198 / g (exponent 2) 0 -
      (((1117290872594389861174066 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4099000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 2 8198 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pplus_3 :
    |g (exponent 3) 8197 / g (exponent 3) 0 -
      (((1923460433832303882696577 : ℤ) * 719689657 : ℤ) : ℝ) / 10^39| ≤
      (5770381301499860936316411 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 3 8197 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pplus_4 :
    |g (exponent 4) 8196 / g (exponent 4) 0 -
      (((-1117681416565483085048780 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4098000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 4 8196 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pplus_5 :
    |g (exponent 5) 8195 / g (exponent 5) 0 -
      (((-1924132852773942638084297 : ℤ) * 719689657 : ℤ) : ℝ) / 10^39| ≤
      (5772398558324776482789911 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 5 8195 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pplus_6 :
    |g (exponent 6) 8193 / g (exponent 6) 0 -
      (((1924805670996055957339134 : ℤ) * 719689657 : ℤ) : ℝ) / 10^39| ≤
      (5774417012991115720864762 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 6 8193 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pplus_7 :
    |g (exponent 7) 8192 / g (exponent 7) 0 -
      (((-1118463200328808916962199 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4096000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 7 8192 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pplus_8 :
    |g (exponent 8) 8191 / g (exponent 8) 0 -
      (((-1925478888833290987988968 : ℤ) * 719689657 : ℤ) : ℝ) / 10^39| ≤
      (5776436666502820093124604 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 8 8191 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pplus_9 :
    |g (exponent 9) 8190 / g (exponent 9) 0 -
      (((1118854440509886131801620 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4095000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 9 8190 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pplus_10 :
    |g (exponent 10) 8189 / g (exponent 10) 0 -
      (((1926152506620657157583949 : ℤ) * 719689657 : ℤ) : ℝ) / 10^39| ≤
      (5778457519864917882219887 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 10 8189 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pplus_11 :
    |g (exponent 11) 8188 / g (exponent 11) 0 -
      (((-1119245913150153457591624 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4094000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 11 8188 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pplus_12 :
    |g (exponent 12) 8200 / g (exponent 12) 0 -
      (((-435410377226636193888421 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4100000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 12 8200 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pplus_13 :
    |g (exponent 13) 8199 / g (exponent 13) 0 -
      (((-475956694614488240811932 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (951913389232004133261391 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 13 8199 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pplus_14 :
    |g (exponent 14) 8198 / g (exponent 14) 0 -
      (((435576908869690094360322 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4099000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 14 8198 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pplus_15 :
    |g (exponent 15) 8197 / g (exponent 15) 0 -
      (((476138756239128927916332 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (952277512481284768838418 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 15 8197 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pplus_16 :
    |g (exponent 16) 8196 / g (exponent 16) 0 -
      (((-435743544861847089631073 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4098000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 16 8196 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pplus_17 :
    |g (exponent 17) 8195 / g (exponent 17) 0 -
      (((-476320931957915869906593 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (952641863918857914187167 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 17 8195 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pplus_18 :
    |g (exponent 18) 8194 / g (exponent 18) 0 -
      (((435910285293979925064975 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4097000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 18 8194 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pplus_19 :
    |g (exponent 19) 8193 / g (exponent 19) 0 -
      (((476503221870220441875980 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (953006443743466319494168 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 19 8193 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pplus_20 :
    |g (exponent 20) 8192 / g (exponent 20) 0 -
      (((-436077130257062689431180 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4096000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 20 8192 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pplus_21 :
    |g (exponent 21) 8191 / g (exponent 21) 0 -
      (((-476685626075524853723252 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (953371252154074404556939 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 21 8191 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pplus_22 :
    |g (exponent 22) 8190 / g (exponent 22) 0 -
      (((436244079842170952701614 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4095000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 22 8190 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pplus_23 :
    |g (exponent 23) 8189 / g (exponent 23) 0 -
      (((476868144673422300874574 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (953736289349868560227810 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 23 8189 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pplus_24 :
    |g (exponent 24) 8188 / g (exponent 24) 0 -
      (((-436411134140481904069988 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4094000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 24 8188 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pminus_0 :
    |g (exponent 0) 8188 / g (exponent 0) 0 -
      (((-1119245913150153457591624 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4094000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 0 8188 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pminus_1 :
    |g (exponent 1) 8189 / g (exponent 1) 0 -
      (((1926152506620657157583949 : ℤ) * 719689657 : ℤ) : ℝ) / 10^39| ≤
      (5778457519864917882219887 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 1 8189 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pminus_2 :
    |g (exponent 2) 8190 / g (exponent 2) 0 -
      (((1118854440509886131801620 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4095000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 2 8190 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pminus_3 :
    |g (exponent 3) 8191 / g (exponent 3) 0 -
      (((-1925478888833290987988968 : ℤ) * 719689657 : ℤ) : ℝ) / 10^39| ≤
      (5776436666502820093124604 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 3 8191 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pminus_4 :
    |g (exponent 4) 8192 / g (exponent 4) 0 -
      (((-1118463200328808916962199 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4096000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 4 8192 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pminus_5 :
    |g (exponent 5) 8193 / g (exponent 5) 0 -
      (((1924805670996055957339134 : ℤ) * 719689657 : ℤ) : ℝ) / 10^39| ≤
      (5774417012991115720864762 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 5 8193 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pminus_6 :
    |g (exponent 6) 8195 / g (exponent 6) 0 -
      (((-1924132852773942638084297 : ℤ) * 719689657 : ℤ) : ℝ) / 10^39| ≤
      (5772398558324776482789911 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 6 8195 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pminus_7 :
    |g (exponent 7) 8196 / g (exponent 7) 0 -
      (((-1117681416565483085048780 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4098000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 7 8196 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pminus_8 :
    |g (exponent 8) 8197 / g (exponent 8) 0 -
      (((1923460433832303882696577 : ℤ) * 719689657 : ℤ) : ℝ) / 10^39| ≤
      (5770381301499860936316411 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 8 8197 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pminus_9 :
    |g (exponent 9) 8198 / g (exponent 9) 0 -
      (((1117290872594389861174066 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4099000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 9 8198 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pminus_10 :
    |g (exponent 10) 8199 / g (exponent 10) 0 -
      (((-1922788413836854343628324 : ℤ) * 719689657 : ℤ) : ℝ) / 10^39| ≤
      (5768365241513513038801312 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 10 8199 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pminus_11 :
    |g (exponent 11) 8200 / g (exponent 11) 0 -
      (((-1116900560304796976861606 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4100000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 11 8200 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pminus_12 :
    |g (exponent 12) 8188 / g (exponent 12) 0 -
      (((-436411134140481904069988 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4094000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 12 8188 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pminus_13 :
    |g (exponent 13) 8189 / g (exponent 13) 0 -
      (((476868144673422300874574 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (953736289349868560227810 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 13 8189 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pminus_14 :
    |g (exponent 14) 8190 / g (exponent 14) 0 -
      (((436244079842170952701614 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4095000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 14 8190 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pminus_15 :
    |g (exponent 15) 8191 / g (exponent 15) 0 -
      (((-476685626075524853723252 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (953371252154074404556939 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 15 8191 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pminus_16 :
    |g (exponent 16) 8192 / g (exponent 16) 0 -
      (((-436077130257062689431180 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4096000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 16 8192 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pminus_17 :
    |g (exponent 17) 8193 / g (exponent 17) 0 -
      (((476503221870220441875980 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (953006443743466319494168 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 17 8193 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pminus_18 :
    |g (exponent 18) 8194 / g (exponent 18) 0 -
      (((435910285293979925064975 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4097000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 18 8194 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pminus_19 :
    |g (exponent 19) 8195 / g (exponent 19) 0 -
      (((-476320931957915869906593 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (952641863918857914187167 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 19 8195 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pminus_20 :
    |g (exponent 20) 8196 / g (exponent 20) 0 -
      (((-435743544861847089631073 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4098000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 20 8196 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pminus_21 :
    |g (exponent 21) 8197 / g (exponent 21) 0 -
      (((476138756239128927916332 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (952277512481284768838418 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 21 8197 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pminus_22 :
    |g (exponent 22) 8198 / g (exponent 22) 0 -
      (((435576908869690094360322 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4099000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 22 8198 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pminus_23 :
    |g (exponent 23) 8199 / g (exponent 23) 0 -
      (((-475956694614488240811932 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (951913389232004133261391 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 23 8199 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Pminus_24 :
    |g (exponent 24) 8200 / g (exponent 24) 0 -
      (((-435410377226636193888421 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4100000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 24 8200 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mplus_0 :
    |g (exponent 0) 8201 / g (exponent 0) 0 -
      (((1922116792453669994023053 : ℤ) * 719689657 : ℤ) : ℝ) / 10^39| ≤
      (5766350377363960709675159 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 0 8201 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mplus_1 :
    |g (exponent 1) 8200 / g (exponent 1) 0 -
      (((-1116900560304796976861606 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4100000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 1 8200 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mplus_2 :
    |g (exponent 2) 8199 / g (exponent 2) 0 -
      (((-1922788413836854343628324 : ℤ) * 719689657 : ℤ) : ℝ) / 10^39| ≤
      (5768365241513513038801312 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 2 8199 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mplus_3 :
    |g (exponent 3) 8198 / g (exponent 3) 0 -
      (((1117290872594389861174066 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4099000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 3 8198 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mplus_4 :
    |g (exponent 4) 8197 / g (exponent 4) 0 -
      (((1923460433832303882696577 : ℤ) * 719689657 : ℤ) : ℝ) / 10^39| ≤
      (5770381301499860936316411 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 4 8197 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mplus_5 :
    |g (exponent 5) 8196 / g (exponent 5) 0 -
      (((-1117681416565483085048780 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4098000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 5 8196 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mplus_6 :
    |g (exponent 6) 8194 / g (exponent 6) 0 -
      (((1118072192412183725316296 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4097000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 6 8194 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mplus_7 :
    |g (exponent 7) 8193 / g (exponent 7) 0 -
      (((1924805670996055957339134 : ℤ) * 719689657 : ℤ) : ℝ) / 10^39| ≤
      (5774417012991115720864762 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 7 8193 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mplus_8 :
    |g (exponent 8) 8192 / g (exponent 8) 0 -
      (((-1118463200328808916962199 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4096000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 8 8192 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mplus_9 :
    |g (exponent 9) 8191 / g (exponent 9) 0 -
      (((-1925478888833290987988968 : ℤ) * 719689657 : ℤ) : ℝ) / 10^39| ≤
      (5776436666502820093124604 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 9 8191 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mplus_10 :
    |g (exponent 10) 8190 / g (exponent 10) 0 -
      (((1118854440509886131801620 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4095000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 10 8190 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mplus_11 :
    |g (exponent 11) 8189 / g (exponent 11) 0 -
      (((1926152506620657157583949 : ℤ) * 719689657 : ℤ) : ℝ) / 10^39| ≤
      (5778457519864917882219887 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 11 8189 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mplus_12 :
    |g (exponent 12) 8201 / g (exponent 12) 0 -
      (((475774746984733117825095 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (951549493972494625919490 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 12 8201 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mplus_13 :
    |g (exponent 13) 8200 / g (exponent 13) 0 -
      (((-435410377226636193888421 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4100000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 13 8200 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mplus_14 :
    |g (exponent 14) 8199 / g (exponent 14) 0 -
      (((-475956694614488240811932 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (951913389232004133261391 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 14 8199 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mplus_15 :
    |g (exponent 15) 8198 / g (exponent 15) 0 -
      (((435576908869690094360322 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4099000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 15 8198 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mplus_16 :
    |g (exponent 16) 8197 / g (exponent 16) 0 -
      (((476138756239128927916332 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (952277512481284768838418 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 16 8197 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mplus_17 :
    |g (exponent 17) 8196 / g (exponent 17) 0 -
      (((-435743544861847089631073 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4098000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 17 8196 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mplus_18 :
    |g (exponent 18) 8195 / g (exponent 18) 0 -
      (((-476320931957915869906593 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (952641863918857914187167 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 18 8195 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mplus_19 :
    |g (exponent 19) 8194 / g (exponent 19) 0 -
      (((435910285293979925064975 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4097000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 19 8194 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mplus_20 :
    |g (exponent 20) 8193 / g (exponent 20) 0 -
      (((476503221870220441875980 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (953006443743466319494168 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 20 8193 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mplus_21 :
    |g (exponent 21) 8192 / g (exponent 21) 0 -
      (((-436077130257062689431180 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4096000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 21 8192 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mplus_22 :
    |g (exponent 22) 8191 / g (exponent 22) 0 -
      (((-476685626075524853723252 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (953371252154074404556939 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 22 8191 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mplus_23 :
    |g (exponent 23) 8190 / g (exponent 23) 0 -
      (((436244079842170952701614 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4095000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 23 8190 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mplus_24 :
    |g (exponent 24) 8189 / g (exponent 24) 0 -
      (((476868144673422300874574 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (953736289349868560227810 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 24 8189 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mminus_0 :
    |g (exponent 0) 8187 / g (exponent 0) 0 -
      (((-1926826524693526654492914 : ℤ) * 719689657 : ℤ) : ℝ) / 10^39| ≤
      (5780479574083525653257122 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 0 8187 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mminus_1 :
    |g (exponent 1) 8188 / g (exponent 1) 0 -
      (((-1119245913150153457591624 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4094000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 1 8188 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mminus_2 :
    |g (exponent 2) 8189 / g (exponent 2) 0 -
      (((1926152506620657157583949 : ℤ) * 719689657 : ℤ) : ℝ) / 10^39| ≤
      (5778457519864917882219887 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 2 8189 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mminus_3 :
    |g (exponent 3) 8190 / g (exponent 3) 0 -
      (((1118854440509886131801620 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4095000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 3 8190 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mminus_4 :
    |g (exponent 4) 8191 / g (exponent 4) 0 -
      (((-1925478888833290987988968 : ℤ) * 719689657 : ℤ) : ℝ) / 10^39| ≤
      (5776436666502820093124604 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 4 8191 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mminus_5 :
    |g (exponent 5) 8192 / g (exponent 5) 0 -
      (((-1118463200328808916962199 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4096000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 5 8192 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mminus_6 :
    |g (exponent 6) 8194 / g (exponent 6) 0 -
      (((1118072192412183725316296 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4097000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 6 8194 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mminus_7 :
    |g (exponent 7) 8195 / g (exponent 7) 0 -
      (((-1924132852773942638084297 : ℤ) * 719689657 : ℤ) : ℝ) / 10^39| ≤
      (5772398558324776482789911 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 7 8195 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mminus_8 :
    |g (exponent 8) 8196 / g (exponent 8) 0 -
      (((-1117681416565483085048780 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4098000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 8 8196 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mminus_9 :
    |g (exponent 9) 8197 / g (exponent 9) 0 -
      (((1923460433832303882696577 : ℤ) * 719689657 : ℤ) : ℝ) / 10^39| ≤
      (5770381301499860936316411 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 9 8197 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mminus_10 :
    |g (exponent 10) 8198 / g (exponent 10) 0 -
      (((1117290872594389861174066 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4099000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 10 8198 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mminus_11 :
    |g (exponent 11) 8199 / g (exponent 11) 0 -
      (((-1922788413836854343628324 : ℤ) * 719689657 : ℤ) : ℝ) / 10^39| ≤
      (5768365241513513038801312 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 11 8199 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mminus_12 :
    |g (exponent 12) 8187 / g (exponent 12) 0 -
      (((-477050777763617115247268 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (954101555530257450341425 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 12 8187 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mminus_13 :
    |g (exponent 13) 8188 / g (exponent 13) 0 -
      (((-436411134140481904069988 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4094000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 13 8188 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mminus_14 :
    |g (exponent 14) 8189 / g (exponent 14) 0 -
      (((476868144673422300874574 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (953736289349868560227810 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 14 8189 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mminus_15 :
    |g (exponent 15) 8190 / g (exponent 15) 0 -
      (((436244079842170952701614 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4095000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 15 8190 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mminus_16 :
    |g (exponent 16) 8191 / g (exponent 16) 0 -
      (((-476685626075524853723252 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (953371252154074404556939 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 16 8191 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mminus_17 :
    |g (exponent 17) 8192 / g (exponent 17) 0 -
      (((-436077130257062689431180 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4096000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 17 8192 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mminus_18 :
    |g (exponent 18) 8193 / g (exponent 18) 0 -
      (((476503221870220441875980 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (953006443743466319494168 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 18 8193 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mminus_19 :
    |g (exponent 19) 8194 / g (exponent 19) 0 -
      (((435910285293979925064975 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4097000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 19 8194 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mminus_20 :
    |g (exponent 20) 8195 / g (exponent 20) 0 -
      (((-476320931957915869906593 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (952641863918857914187167 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 20 8195 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mminus_21 :
    |g (exponent 21) 8196 / g (exponent 21) 0 -
      (((-435743544861847089631073 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4098000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 21 8196 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mminus_22 :
    |g (exponent 22) 8197 / g (exponent 22) 0 -
      (((476138756239128927916332 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (952277512481284768838418 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 22 8197 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mminus_23 :
    |g (exponent 23) 8198 / g (exponent 23) 0 -
      (((435576908869690094360322 : ℤ) * 1000000000 : ℤ) : ℝ) / 10^39| ≤
      (4099000000000 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 23 8198 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem Mminus_24 :
    |g (exponent 24) 8199 / g (exponent 24) 0 -
      (((-475956694614488240811932 : ℤ) * 738631771 : ℤ) : ℝ) / 10^39| ≤
      (951913389232004133261391 : ℝ) / 10^39 := by
  exact ratio_table KsIndex.NegSignProd.valid 24 8199 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end KsIndex.AlphaRemarkTrial.Energy4096Endpoints
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pplus_0
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pplus_1
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pplus_2
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pplus_3
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pplus_4
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pplus_5
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pplus_6
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pplus_7
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pplus_8
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pplus_9
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pplus_10
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pplus_11
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pplus_12
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pplus_13
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pplus_14
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pplus_15
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pplus_16
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pplus_17
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pplus_18
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pplus_19
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pplus_20
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pplus_21
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pplus_22
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pplus_23
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pplus_24
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pminus_0
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pminus_1
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pminus_2
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pminus_3
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pminus_4
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pminus_5
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pminus_6
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pminus_7
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pminus_8
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pminus_9
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pminus_10
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pminus_11
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pminus_12
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pminus_13
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pminus_14
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pminus_15
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pminus_16
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pminus_17
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pminus_18
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pminus_19
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pminus_20
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pminus_21
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pminus_22
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pminus_23
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Pminus_24
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mplus_0
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mplus_1
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mplus_2
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mplus_3
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mplus_4
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mplus_5
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mplus_6
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mplus_7
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mplus_8
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mplus_9
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mplus_10
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mplus_11
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mplus_12
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mplus_13
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mplus_14
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mplus_15
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mplus_16
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mplus_17
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mplus_18
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mplus_19
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mplus_20
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mplus_21
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mplus_22
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mplus_23
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mplus_24
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mminus_0
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mminus_1
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mminus_2
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mminus_3
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mminus_4
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mminus_5
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mminus_6
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mminus_7
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mminus_8
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mminus_9
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mminus_10
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mminus_11
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mminus_12
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mminus_13
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mminus_14
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mminus_15
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mminus_16
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mminus_17
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mminus_18
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mminus_19
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mminus_20
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mminus_21
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mminus_22
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mminus_23
#print axioms KsIndex.AlphaRemarkTrial.Energy4096Endpoints.Mminus_24
