module

public import KsIndexLean.AlphaEnergy8192MplusRows

@[expose] public section


/-! Outward rational bounds for the Mplus energy tail error sums. -/
namespace KsIndex.AlphaRemarkTrial.Energy8192Tail.Mplus
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable def radiusRow (i : Fin 25) : ℝ :=
  ∑ j, |tailMatrix point i j| * (|center i| * radius j+|center j| * radius i+radius i*radius j)
noncomputable def productRow (i : Fin 25) : ℝ :=
  ∑ j, |(coefficient i).re*(coefficient j).re| *
    (|49162-3*(exponent j*point i+exponent i*point j)/(exponent i+exponent j)| *
      (((point i+exponent i)^2*(|center i|+radius i)^2/(4*exponent i*point i)+
        (point j+exponent j)^2*(|center j|+radius j)^2/(4*exponent j*point j))/2))

theorem radius_row_0 : radiusRow (0 : Fin 25) ≤ (211/31250000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_0 : productRow (0 : Fin 25) ≤ (3395597/125000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_1 : radiusRow (Fin.succ (0 : Fin 24)) ≤ (32941/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_1 : productRow (Fin.succ (0 : Fin 24)) ≤ (5483843/62500000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_2 : radiusRow (Fin.succ (Fin.succ (0 : Fin 23))) ≤ (10059/100000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_2 : productRow (Fin.succ (Fin.succ (0 : Fin 23))) ≤ (64030523/250000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_3 : radiusRow (Fin.succ (Fin.succ (Fin.succ (0 : Fin 22)))) ≤ (52459/500000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_3 : productRow (Fin.succ (Fin.succ (Fin.succ (0 : Fin 22)))) ≤ (78495577/500000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_4 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 21))))) ≤ (158291/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_4 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 21))))) ≤ (97610571/500000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_5 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 20)))))) ≤ (2029277/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_5 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 20)))))) ≤ (97836239/62500000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_6 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 19))))))) ≤ (2029271/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_6 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 19))))))) ≤ (1114809851/500000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_7 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 18)))))))) ≤ (158293/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_7 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 18)))))))) ≤ (157354777/500000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_8 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 17))))))))) ≤ (104917/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_8 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 17))))))))) ≤ (57626821/250000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_9 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 16)))))))))) ≤ (6287/62500000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_9 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 16)))))))))) ≤ (346082709/1000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_10 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 15))))))))))) ≤ (1647/50000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_10 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 15))))))))))) ≤ (56037379/500000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_11 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 14)))))))))))) ≤ (211/31250000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_11 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 14)))))))))))) ≤ (8326681/250000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_12 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 13))))))))))))) ≤ (1987/250000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_12 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 13))))))))))))) ≤ (1202907/100000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_13 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 12)))))))))))))) ≤ (32731/500000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_13 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 12)))))))))))))) ≤ (82728467/1000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_14 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 11))))))))))))))) ≤ (232483/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_14 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 11))))))))))))))) ≤ (56711279/250000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_15 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 10)))))))))))))))) ≤ (26443/40000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_15 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 10)))))))))))))))) ≤ (61481689/125000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_16 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 9))))))))))))))))) ≤ (238057/200000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_16 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 9))))))))))))))))) ≤ (125612521/200000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_17 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 8)))))))))))))))))) ≤ (2295833/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_17 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 8)))))))))))))))))) ≤ (230409533/200000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_18 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 7))))))))))))))))))) ≤ (1339423/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_18 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 7))))))))))))))))))) ≤ (335047319/500000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_19 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 6)))))))))))))))))))) ≤ (2295743/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_19 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 6)))))))))))))))))))) ≤ (715933827/500000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_20 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 5))))))))))))))))))))) ≤ (148771/125000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_20 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 5))))))))))))))))))))) ≤ (499374117/500000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_21 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 4)))))))))))))))))))))) ≤ (330499/500000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_21 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 4)))))))))))))))))))))) ≤ (735638673/1000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_22 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 3))))))))))))))))))))))) ≤ (232437/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_22 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 3))))))))))))))))))))))) ≤ (317328259/1000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_23 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 2)))))))))))))))))))))))) ≤ (65449/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_23 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 2)))))))))))))))))))))))) ≤ (109519869/1000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_24 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1))))))))))))))))))))))))) ≤ (3973/500000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_24 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1))))))))))))))))))))))))) ≤ (1914783/125000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

noncomputable def radiusRowUpper : Fin 25 → ℝ := ![(211/31250000000000000 : ℝ),
  (32941/1000000000000000000 : ℝ),
  (10059/100000000000000000 : ℝ),
  (52459/500000000000000000 : ℝ),
  (158291/1000000000000000000 : ℝ),
  (2029277/1000000000000000000 : ℝ),
  (2029271/1000000000000000000 : ℝ),
  (158293/1000000000000000000 : ℝ),
  (104917/1000000000000000000 : ℝ),
  (6287/62500000000000000 : ℝ),
  (1647/50000000000000000 : ℝ),
  (211/31250000000000000 : ℝ),
  (1987/250000000000000000 : ℝ),
  (32731/500000000000000000 : ℝ),
  (232483/1000000000000000000 : ℝ),
  (26443/40000000000000000 : ℝ),
  (238057/200000000000000000 : ℝ),
  (2295833/1000000000000000000 : ℝ),
  (1339423/1000000000000000000 : ℝ),
  (2295743/1000000000000000000 : ℝ),
  (148771/125000000000000000 : ℝ),
  (330499/500000000000000000 : ℝ),
  (232437/1000000000000000000 : ℝ),
  (65449/1000000000000000000 : ℝ),
  (3973/500000000000000000 : ℝ)]
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
theorem radius_bound : tailRadius point center radius ≤ (118053/7812500000000000 : ℝ) := by
  have h := Finset.sum_le_sum (fun (i : Fin 25) (_ : i ∈ Finset.univ) => radius_rows i)
  change tailRadius point center radius ≤ ∑ i, radiusRowUpper i at h
  norm_num [radiusRowUpper, Fin.sum_univ_succ] at h
  exact h

noncomputable def productRowUpper : Fin 25 → ℝ := ![(3395597/125000000000000000 : ℝ),
  (5483843/62500000000000000 : ℝ),
  (64030523/250000000000000000 : ℝ),
  (78495577/500000000000000000 : ℝ),
  (97610571/500000000000000000 : ℝ),
  (97836239/62500000000000000 : ℝ),
  (1114809851/500000000000000000 : ℝ),
  (157354777/500000000000000000 : ℝ),
  (57626821/250000000000000000 : ℝ),
  (346082709/1000000000000000000 : ℝ),
  (56037379/500000000000000000 : ℝ),
  (8326681/250000000000000000 : ℝ),
  (1202907/100000000000000000 : ℝ),
  (82728467/1000000000000000000 : ℝ),
  (56711279/250000000000000000 : ℝ),
  (61481689/125000000000000000 : ℝ),
  (125612521/200000000000000000 : ℝ),
  (230409533/200000000000000000 : ℝ),
  (335047319/500000000000000000 : ℝ),
  (715933827/500000000000000000 : ℝ),
  (499374117/500000000000000000 : ℝ),
  (735638673/1000000000000000000 : ℝ),
  (317328259/1000000000000000000 : ℝ),
  (109519869/1000000000000000000 : ℝ),
  (1914783/125000000000000000 : ℝ)]
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
theorem product_bound : tailProductUpper point center radius 49162 ≤ (12427003233/1000000000000000000 : ℝ) := by
  have h := Finset.sum_le_sum (fun (i : Fin 25) (_ : i ∈ Finset.univ) => product_rows i)
  change tailProductUpper point center radius 49162 ≤ ∑ i, productRowUpper i at h
  norm_num [productRowUpper, Fin.sum_univ_succ] at h
  exact h

end KsIndex.AlphaRemarkTrial.Energy8192Tail.Mplus
