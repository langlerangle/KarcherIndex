module

public import KsIndexLean.AlphaEnergy8192PminusRows

@[expose] public section


/-! Outward rational bounds for the Pminus energy tail error sums. -/
namespace KsIndex.AlphaRemarkTrial.Energy8192Tail.Pminus
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable def radiusRow (i : Fin 25) : ℝ :=
  ∑ j, |tailMatrix point i j| * (|center i| * radius j+|center j| * radius i+radius i*radius j)
noncomputable def productRow (i : Fin 25) : ℝ :=
  ∑ j, |(coefficient i).re*(coefficient j).re| *
    (|49157-3*(exponent j*point i+exponent i*point j)/(exponent i+exponent j)| *
      (((point i+exponent i)^2*(|center i|+radius i)^2/(4*exponent i*point i)+
        (point j+exponent j)^2*(|center j|+radius j)^2/(4*exponent j*point j))/2))

theorem radius_row_0 : radiusRow (0 : Fin 25) ≤ (5933/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_0 : productRow (0 : Fin 25) ≤ (4001009/200000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_1 : radiusRow (Fin.succ (0 : Fin 24)) ≤ (19507/500000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_1 : productRow (Fin.succ (0 : Fin 24)) ≤ (130430111/1000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_2 : radiusRow (Fin.succ (Fin.succ (0 : Fin 23))) ≤ (88389/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_2 : productRow (Fin.succ (Fin.succ (0 : Fin 23))) ≤ (188455301/1000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_3 : radiusRow (Fin.succ (Fin.succ (Fin.succ (0 : Fin 22)))) ≤ (124261/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_3 : productRow (Fin.succ (Fin.succ (Fin.succ (0 : Fin 22)))) ≤ (232711401/1000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_4 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 21))))) ≤ (139093/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_4 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 21))))) ≤ (71125347/500000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_5 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 20)))))) ≤ (240341/100000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_5 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 20)))))) ≤ (45931713/20000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_6 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 19))))))) ≤ (600851/250000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_6 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 19))))))) ≤ (3289645537/1000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_7 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 18)))))))) ≤ (69547/500000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_7 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 18)))))))) ≤ (232107591/1000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_8 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 17))))))))) ≤ (6213/50000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_8 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 17))))))))) ≤ (170976609/500000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_9 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 16)))))))))) ≤ (88391/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_9 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 16)))))))))) ≤ (199211/781250000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_10 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 15))))))))))) ≤ (19507/500000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_10 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 15))))))))))) ≤ (166281767/1000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_11 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 14)))))))))))) ≤ (5933/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_11 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 14)))))))))))) ≤ (4904077/200000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_12 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 13))))))))))))) ≤ (8999/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_12 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 13))))))))))))) ≤ (15995747/1000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_13 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 12)))))))))))))) ≤ (62481/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_13 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 12)))))))))))))) ≤ (22565243/250000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_14 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 11))))))))))))))) ≤ (263243/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_14 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 11))))))))))))))) ≤ (299045069/1000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_15 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 10)))))))))))))))) ≤ (315513/500000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_15 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 10)))))))))))))))) ≤ (52647783/100000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_16 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 9))))))))))))))))) ≤ (1347897/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_16 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 9))))))))))))))))) ≤ (396929603/500000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_17 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 8)))))))))))))))))) ≤ (547919/250000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_17 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 8)))))))))))))))))) ≤ (121121967/100000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_18 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 7))))))))))))))))))) ≤ (758461/500000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_18 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 7))))))))))))))))))) ≤ (424882279/500000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_19 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 6)))))))))))))))))))) ≤ (219179/100000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_19 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 6)))))))))))))))))))) ≤ (380216319/250000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_20 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 5))))))))))))))))))))) ≤ (1348011/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_20 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 5))))))))))))))))))))) ≤ (65673069/50000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_21 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 4)))))))))))))))))))))) ≤ (5049/8000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_21 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 4)))))))))))))))))))))) ≤ (50365463/62500000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_22 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 3))))))))))))))))))))))) ≤ (263287/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_22 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 3))))))))))))))))))))))) ≤ (2108357/5000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_23 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 2)))))))))))))))))))))))) ≤ (62497/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_23 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 2)))))))))))))))))))))))) ≤ (30084379/250000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_24 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1))))))))))))))))))))))))) ≤ (9001/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_24 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1))))))))))))))))))))))))) ≤ (2547649/125000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

noncomputable def radiusRowUpper : Fin 25 → ℝ := ![(5933/1000000000000000000 : ℝ),
  (19507/500000000000000000 : ℝ),
  (88389/1000000000000000000 : ℝ),
  (124261/1000000000000000000 : ℝ),
  (139093/1000000000000000000 : ℝ),
  (240341/100000000000000000 : ℝ),
  (600851/250000000000000000 : ℝ),
  (69547/500000000000000000 : ℝ),
  (6213/50000000000000000 : ℝ),
  (88391/1000000000000000000 : ℝ),
  (19507/500000000000000000 : ℝ),
  (5933/1000000000000000000 : ℝ),
  (8999/1000000000000000000 : ℝ),
  (62481/1000000000000000000 : ℝ),
  (263243/1000000000000000000 : ℝ),
  (315513/500000000000000000 : ℝ),
  (1347897/1000000000000000000 : ℝ),
  (547919/250000000000000000 : ℝ),
  (758461/500000000000000000 : ℝ),
  (219179/100000000000000000 : ℝ),
  (1348011/1000000000000000000 : ℝ),
  (5049/8000000000000000 : ℝ),
  (263287/1000000000000000000 : ℝ),
  (62497/1000000000000000000 : ℝ),
  (9001/1000000000000000000 : ℝ)]
theorem radius_rows (i : Fin 25) : radiusRow i ≤ radiusRowUpper i := by
  fin_cases i
  · exact radius_row_0
  · exact radius_row_1
  · exact radius_row_2
  · exact radius_row_3
  · exact radius_row_4
  · exact radius_row_5
  · exact radius_row_6
  · exact radius_row_7
  · exact radius_row_8
  · exact radius_row_9
  · exact radius_row_10
  · exact radius_row_11
  · exact radius_row_12
  · exact radius_row_13
  · exact radius_row_14
  · exact radius_row_15
  · exact radius_row_16
  · exact radius_row_17
  · exact radius_row_18
  · exact radius_row_19
  · exact radius_row_20
  · exact radius_row_21
  · exact radius_row_22
  · exact radius_row_23
  · exact radius_row_24
theorem radius_bound : tailRadius point center radius ≤ (16128151/1000000000000000000 : ℝ) := by
  have h := Finset.sum_le_sum (fun (i : Fin 25) (_ : i ∈ Finset.univ) => radius_rows i)
  change tailRadius point center radius ≤ ∑ i, radiusRowUpper i at h
  norm_num [radiusRowUpper, Fin.sum_univ_succ] at h
  exact h

noncomputable def productRowUpper : Fin 25 → ℝ := ![(4001009/200000000000000000 : ℝ),
  (130430111/1000000000000000000 : ℝ),
  (188455301/1000000000000000000 : ℝ),
  (232711401/1000000000000000000 : ℝ),
  (71125347/500000000000000000 : ℝ),
  (45931713/20000000000000000 : ℝ),
  (3289645537/1000000000000000000 : ℝ),
  (232107591/1000000000000000000 : ℝ),
  (170976609/500000000000000000 : ℝ),
  (199211/781250000000000 : ℝ),
  (166281767/1000000000000000000 : ℝ),
  (4904077/200000000000000000 : ℝ),
  (15995747/1000000000000000000 : ℝ),
  (22565243/250000000000000000 : ℝ),
  (299045069/1000000000000000000 : ℝ),
  (52647783/100000000000000000 : ℝ),
  (396929603/500000000000000000 : ℝ),
  (121121967/100000000000000000 : ℝ),
  (424882279/500000000000000000 : ℝ),
  (380216319/250000000000000000 : ℝ),
  (65673069/50000000000000000 : ℝ),
  (50365463/62500000000000000 : ℝ),
  (2108357/5000000000000000 : ℝ),
  (30084379/250000000000000000 : ℝ),
  (2547649/125000000000000000 : ℝ)]
theorem product_rows (i : Fin 25) : productRow i ≤ productRowUpper i := by
  fin_cases i
  · exact product_row_0
  · exact product_row_1
  · exact product_row_2
  · exact product_row_3
  · exact product_row_4
  · exact product_row_5
  · exact product_row_6
  · exact product_row_7
  · exact product_row_8
  · exact product_row_9
  · exact product_row_10
  · exact product_row_11
  · exact product_row_12
  · exact product_row_13
  · exact product_row_14
  · exact product_row_15
  · exact product_row_16
  · exact product_row_17
  · exact product_row_18
  · exact product_row_19
  · exact product_row_20
  · exact product_row_21
  · exact product_row_22
  · exact product_row_23
  · exact product_row_24
theorem product_bound : tailProductUpper point center radius 49157 ≤ (3827281001/250000000000000000 : ℝ) := by
  have h := Finset.sum_le_sum (fun (i : Fin 25) (_ : i ∈ Finset.univ) => product_rows i)
  change tailProductUpper point center radius 49157 ≤ ∑ i, productRowUpper i at h
  norm_num [productRowUpper, Fin.sum_univ_succ] at h
  exact h

end KsIndex.AlphaRemarkTrial.Energy8192Tail.Pminus
