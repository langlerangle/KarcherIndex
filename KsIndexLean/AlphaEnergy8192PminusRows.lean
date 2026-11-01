module

public import KsIndexLean.AlphaEnergy8192Data

@[expose] public section


/-! Rowwise rational enclosures of the Pminus energy tail. -/
namespace KsIndex.AlphaRemarkTrial.Energy8192Tail.Pminus
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
theorem leading_row_0 :
    |(∑ j : Fin 25, tailMatrix point (0 : Fin 25) j*(center (0 : Fin 25)*center j))-(-11784739663/250000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_1 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (0 : Fin 24)) j*(center (Fin.succ (0 : Fin 24))*center j))-(-165622531003/500000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_2 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (0 : Fin 23))) j*(center (Fin.succ (Fin.succ (0 : Fin 23)))*center j))-(175571669197/250000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_3 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (0 : Fin 22)))) j*(center (Fin.succ (Fin.succ (Fin.succ (0 : Fin 22))))*center j))-(527493013101/500000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_4 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 21))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 21)))))*center j))-(110508041561/100000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_5 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 20)))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 20))))))*center j))-(10202071564997/500000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_6 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 19))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 19)))))))*center j))-(4080613265553/200000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_7 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 18)))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 18))))))))*center j))-(-1104963779947/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_8 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 17))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 17)))))))))*center j))-(1054819007651/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_9 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 16)))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 16))))))))))*center j))-(-351069219419/500000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_10 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 15))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 15)))))))))))*center j))-(-331157665731/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_11 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 14)))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 14))))))))))))*center j))-(23562017181/500000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_12 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 13))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 13)))))))))))))*center j))-(22141585373/500000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_13 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 12)))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 12))))))))))))))*center j))-(269895071033/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_14 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 11))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 11)))))))))))))))*center j))-(-647678871703/500000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_15 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 10)))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 10))))))))))))))))*center j))-(-2725510523881/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_16 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 9))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 9)))))))))))))))))*center j))-(1657991028339/250000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_17 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 8)))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 8))))))))))))))))))*center j))-(1893015913441/200000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_18 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 7))))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 7)))))))))))))))))))*center j))-(3731385878071/500000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_19 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 6)))))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 6))))))))))))))))))))*center j))-(-236610594589/25000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_20 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 5))))))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 5)))))))))))))))))))))*center j))-(1657761287487/250000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_21 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 4)))))))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 4))))))))))))))))))))))*center j))-(1362472024557/500000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_22 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 3))))))))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 3)))))))))))))))))))))))*center j))-(-1294998784657/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_23 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 2)))))))))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 2))))))))))))))))))))))))*center j))-(-134900792783/500000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_24 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1))))))))))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1)))))))))))))))))))))))))*center j))-(44264764937/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

noncomputable def rowCenter : Fin 25 → ℝ := ![(-11784739663/250000000000000000 : ℝ),
  (-165622531003/500000000000000000 : ℝ),
  (175571669197/250000000000000000 : ℝ),
  (527493013101/500000000000000000 : ℝ),
  (110508041561/100000000000000000 : ℝ),
  (10202071564997/500000000000000000 : ℝ),
  (4080613265553/200000000000000000 : ℝ),
  (-1104963779947/1000000000000000000 : ℝ),
  (1054819007651/1000000000000000000 : ℝ),
  (-351069219419/500000000000000000 : ℝ),
  (-331157665731/1000000000000000000 : ℝ),
  (23562017181/500000000000000000 : ℝ),
  (22141585373/500000000000000000 : ℝ),
  (269895071033/1000000000000000000 : ℝ),
  (-647678871703/500000000000000000 : ℝ),
  (-2725510523881/1000000000000000000 : ℝ),
  (1657991028339/250000000000000000 : ℝ),
  (1893015913441/200000000000000000 : ℝ),
  (3731385878071/500000000000000000 : ℝ),
  (-236610594589/25000000000000000 : ℝ),
  (1657761287487/250000000000000000 : ℝ),
  (1362472024557/500000000000000000 : ℝ),
  (-1294998784657/1000000000000000000 : ℝ),
  (-134900792783/500000000000000000 : ℝ),
  (44264764937/1000000000000000000 : ℝ)]
theorem leading_rows (i : Fin 25) :
    |(∑ j : Fin 25, tailMatrix point i j*(center i*center j))-rowCenter i| ≤ (1/1000000000000000000 : ℝ) := by
  fin_cases i
  · exact leading_row_0
  · exact leading_row_1
  · exact leading_row_2
  · exact leading_row_3
  · exact leading_row_4
  · exact leading_row_5
  · exact leading_row_6
  · exact leading_row_7
  · exact leading_row_8
  · exact leading_row_9
  · exact leading_row_10
  · exact leading_row_11
  · exact leading_row_12
  · exact leading_row_13
  · exact leading_row_14
  · exact leading_row_15
  · exact leading_row_16
  · exact leading_row_17
  · exact leading_row_18
  · exact leading_row_19
  · exact leading_row_20
  · exact leading_row_21
  · exact leading_row_22
  · exact leading_row_23
  · exact leading_row_24
theorem leading_interval :
    |tailCenter point center-(60479016934609/1000000000000000000 : ℝ)| ≤ (25/1000000000000000000 : ℝ) := by
  have h := CertifiedApproximation.finite_linear_error Finset.univ (fun _ : Fin 25 => (1:ℝ))
    (fun i => ∑ j : Fin 25, tailMatrix point i j*(center i*center j)) rowCenter
    (fun _ => (1/1000000000000000000 : ℝ)) (fun i _ => leading_rows i)
  simp only [one_mul, abs_one] at h
  change |tailCenter point center-(∑ i, rowCenter i)| ≤ ∑ _ : Fin 25, (1/1000000000000000000 : ℝ) at h
  norm_num [rowCenter, Fin.sum_univ_succ] at h
  convert! h using 1; norm_num

end KsIndex.AlphaRemarkTrial.Energy8192Tail.Pminus
