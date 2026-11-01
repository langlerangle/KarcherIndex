module

public import KsIndexLean.AlphaEnergy8192MminusRows

@[expose] public section


/-! Outward rational bounds for the Mminus energy tail error sums. -/
namespace KsIndex.AlphaRemarkTrial.Energy8192Tail.Mminus
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable def radiusRow (i : Fin 25) : ℝ :=
  ∑ j, |tailMatrix point i j| * (|center i| * radius j+|center j| * radius i+radius i*radius j)
noncomputable def productRow (i : Fin 25) : ℝ :=
  ∑ j, |(coefficient i).re*(coefficient j).re| *
    (|49154-3*(exponent j*point i+exponent i*point j)/(exponent i+exponent j)| *
      (((point i+exponent i)^2*(|center i|+radius i)^2/(4*exponent i*point i)+
        (point j+exponent j)^2*(|center j|+radius j)^2/(4*exponent j*point j))/2))

theorem radius_row_0 : radiusRow (0 : Fin 25) ≤ (211/31250000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_0 : productRow (0 : Fin 25) ≤ (27203589/1000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_1 : radiusRow (Fin.succ (0 : Fin 24)) ≤ (16469/500000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_1 : productRow (Fin.succ (0 : Fin 24)) ≤ (1756897/20000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_2 : radiusRow (Fin.succ (Fin.succ (0 : Fin 23))) ≤ (20117/200000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_2 : productRow (Fin.succ (Fin.succ (0 : Fin 23))) ≤ (51277751/200000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_3 : radiusRow (Fin.succ (Fin.succ (Fin.succ (0 : Fin 22)))) ≤ (10491/100000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_3 : productRow (Fin.succ (Fin.succ (Fin.succ (0 : Fin 22)))) ≤ (15712009/100000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_4 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 21))))) ≤ (79141/500000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_4 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 21))))) ≤ (381541/1953125000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_5 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 20)))))) ≤ (126821/62500000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_5 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 20)))))) ≤ (1566051723/1000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_6 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 19))))))) ≤ (1014571/500000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_6 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 19))))))) ≤ (2229621149/1000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_7 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 18)))))))) ≤ (158281/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_7 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 18)))))))) ≤ (157324683/500000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_8 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 17))))))))) ≤ (104911/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_8 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 17))))))))) ≤ (230425987/1000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_9 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 16)))))))))) ≤ (100583/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_9 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 16)))))))))) ≤ (345883237/1000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_10 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 15))))))))))) ≤ (32939/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_10 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 15))))))))))) ≤ (4479809/40000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_11 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 14)))))))))))) ≤ (6751/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_11 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 14)))))))))))) ≤ (33274607/1000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_12 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 13))))))))))))) ≤ (1589/200000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_12 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 13))))))))))))) ≤ (12037451/1000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_13 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 12)))))))))))))) ≤ (13089/200000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_13 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 12)))))))))))))) ≤ (41395243/500000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_14 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 11))))))))))))))) ≤ (29053/125000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_14 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 11))))))))))))))) ≤ (3546667/15625000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_15 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 10)))))))))))))))) ≤ (4131/6250000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_15 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 10)))))))))))))))) ≤ (492165109/1000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_16 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 9))))))))))))))))) ≤ (11901/10000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_16 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 9))))))))))))))))) ≤ (628396983/1000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_17 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 8)))))))))))))))))) ≤ (573903/250000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_17 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 8)))))))))))))))))) ≤ (576226137/500000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_18 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 7))))))))))))))))))) ≤ (1339347/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_18 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 7))))))))))))))))))) ≤ (670179831/1000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_19 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 6)))))))))))))))))))) ≤ (1147851/500000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_19 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 6)))))))))))))))))))) ≤ (1431868927/1000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_20 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 5))))))))))))))))))))) ≤ (1190217/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_20 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 5))))))))))))))))))))) ≤ (49935323/50000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_21 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 4)))))))))))))))))))))) ≤ (330519/500000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_21 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 4)))))))))))))))))))))) ≤ (147110377/200000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_22 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 3))))))))))))))))))))))) ≤ (232469/1000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_22 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 3))))))))))))))))))))))) ≤ (317293913/1000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_23 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 2)))))))))))))))))))))))) ≤ (32729/500000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_23 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 2)))))))))))))))))))))))) ≤ (27373559/250000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem radius_row_24 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1))))))))))))))))))))))))) ≤ (1987/250000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem product_row_24 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1))))))))))))))))))))))))) ≤ (7657727/500000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, point, shift, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

noncomputable def radiusRowUpper : Fin 25 → ℝ := ![(211/31250000000000000 : ℝ),
  (16469/500000000000000000 : ℝ),
  (20117/200000000000000000 : ℝ),
  (10491/100000000000000000 : ℝ),
  (79141/500000000000000000 : ℝ),
  (126821/62500000000000000 : ℝ),
  (1014571/500000000000000000 : ℝ),
  (158281/1000000000000000000 : ℝ),
  (104911/1000000000000000000 : ℝ),
  (100583/1000000000000000000 : ℝ),
  (32939/1000000000000000000 : ℝ),
  (6751/1000000000000000000 : ℝ),
  (1589/200000000000000000 : ℝ),
  (13089/200000000000000000 : ℝ),
  (29053/125000000000000000 : ℝ),
  (4131/6250000000000000 : ℝ),
  (11901/10000000000000000 : ℝ),
  (573903/250000000000000000 : ℝ),
  (1339347/1000000000000000000 : ℝ),
  (1147851/500000000000000000 : ℝ),
  (1190217/1000000000000000000 : ℝ),
  (330519/500000000000000000 : ℝ),
  (232469/1000000000000000000 : ℝ),
  (32729/500000000000000000 : ℝ),
  (1987/250000000000000000 : ℝ)]
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
theorem radius_bound : tailRadius point center radius ≤ (120879/8000000000000000 : ℝ) := by
  have h := Finset.sum_le_sum (fun (i : Fin 25) (_ : i ∈ Finset.univ) => radius_rows i)
  change tailRadius point center radius ≤ ∑ i, radiusRowUpper i at h
  norm_num [radiusRowUpper, Fin.sum_univ_succ] at h
  exact h

noncomputable def productRowUpper : Fin 25 → ℝ := ![(27203589/1000000000000000000 : ℝ),
  (1756897/20000000000000000 : ℝ),
  (51277751/200000000000000000 : ℝ),
  (15712009/100000000000000000 : ℝ),
  (381541/1953125000000000 : ℝ),
  (1566051723/1000000000000000000 : ℝ),
  (2229621149/1000000000000000000 : ℝ),
  (157324683/500000000000000000 : ℝ),
  (230425987/1000000000000000000 : ℝ),
  (345883237/1000000000000000000 : ℝ),
  (4479809/40000000000000000 : ℝ),
  (33274607/1000000000000000000 : ℝ),
  (12037451/1000000000000000000 : ℝ),
  (41395243/500000000000000000 : ℝ),
  (3546667/15625000000000000 : ℝ),
  (492165109/1000000000000000000 : ℝ),
  (628396983/1000000000000000000 : ℝ),
  (576226137/500000000000000000 : ℝ),
  (670179831/1000000000000000000 : ℝ),
  (1431868927/1000000000000000000 : ℝ),
  (49935323/50000000000000000 : ℝ),
  (147110377/200000000000000000 : ℝ),
  (317293913/1000000000000000000 : ℝ),
  (27373559/250000000000000000 : ℝ),
  (7657727/500000000000000000 : ℝ)]
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
theorem product_bound : tailProductUpper point center radius 49154 ≤ (12429047267/1000000000000000000 : ℝ) := by
  have h := Finset.sum_le_sum (fun (i : Fin 25) (_ : i ∈ Finset.univ) => product_rows i)
  change tailProductUpper point center radius 49154 ≤ ∑ i, productRowUpper i at h
  norm_num [productRowUpper, Fin.sum_univ_succ] at h
  exact h

end KsIndex.AlphaRemarkTrial.Energy8192Tail.Mminus
