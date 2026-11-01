module

public import KsIndexLean.AlphaEnergy8192Data

@[expose] public section


/-! Rowwise rational enclosures of the Mminus energy tail. -/
namespace KsIndex.AlphaRemarkTrial.Energy8192Tail.Mminus
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
theorem leading_row_0 :
    |(∑ j : Fin 25, tailMatrix point (0 : Fin 25) j*(center (0 : Fin 25)*center j))-(9420769433/500000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_1 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (0 : Fin 24)) j*(center (Fin.succ (0 : Fin 24))*center j))-(-86280575483/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_2 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (0 : Fin 23))) j*(center (Fin.succ (Fin.succ (0 : Fin 23)))*center j))-(-280705430419/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_3 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (0 : Fin 22)))) j*(center (Fin.succ (Fin.succ (Fin.succ (0 : Fin 22))))*center j))-(137397974463/500000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_4 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 21))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 21)))))*center j))-(-13803216111/31250000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_5 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 20)))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 20))))))*center j))-(2657369726761/500000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_6 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 19))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 19)))))))*center j))-(2657229477893/500000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_7 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 18)))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 18))))))))*center j))-(88331258641/200000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_8 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 17))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 17)))))))))*center j))-(274752442441/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_9 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 16)))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 16))))))))))*center j))-(280646175763/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_10 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 15))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 15)))))))))))*center j))-(-86257809647/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_11 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 14)))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 14))))))))))))*center j))-(-18835573239/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_12 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 13))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 13)))))))))))))*center j))-(-11309936271/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_13 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 12)))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 12))))))))))))))*center j))-(10577649349/100000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_14 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 11))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 11)))))))))))))))*center j))-(165417394703/500000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_15 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 10)))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 10))))))))))))))))*center j))-(-1068174173607/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_16 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 9))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 9)))))))))))))))))*center j))-(-1693805786449/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_17 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 8)))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 8))))))))))))))))))*center j))-(3709526502859/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_18 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 7))))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 7)))))))))))))))))))*center j))-(-119124645021/62500000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_19 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 6)))))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 6))))))))))))))))))))*center j))-(-927317366997/250000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_20 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 5))))))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 5)))))))))))))))))))))*center j))-(-846785534307/500000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_21 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 4)))))))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 4))))))))))))))))))))))*center j))-(1067952150469/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_22 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 3))))))))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 3)))))))))))))))))))))))*center j))-(3307431057/10000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_23 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 2)))))))))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 2))))))))))))))))))))))))*center j))-(-21147970513/200000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_24 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1))))))))))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1)))))))))))))))))))))))))*center j))-(-11305235137/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

noncomputable def rowCenter : Fin 25 → ℝ := ![(9420769433/500000000000000000 : ℝ),
  (-86280575483/1000000000000000000 : ℝ),
  (-280705430419/1000000000000000000 : ℝ),
  (137397974463/500000000000000000 : ℝ),
  (-13803216111/31250000000000000 : ℝ),
  (2657369726761/500000000000000000 : ℝ),
  (2657229477893/500000000000000000 : ℝ),
  (88331258641/200000000000000000 : ℝ),
  (274752442441/1000000000000000000 : ℝ),
  (280646175763/1000000000000000000 : ℝ),
  (-86257809647/1000000000000000000 : ℝ),
  (-18835573239/1000000000000000000 : ℝ),
  (-11309936271/1000000000000000000 : ℝ),
  (10577649349/100000000000000000 : ℝ),
  (165417394703/500000000000000000 : ℝ),
  (-1068174173607/1000000000000000000 : ℝ),
  (-1693805786449/1000000000000000000 : ℝ),
  (3709526502859/1000000000000000000 : ℝ),
  (-119124645021/62500000000000000 : ℝ),
  (-927317366997/250000000000000000 : ℝ),
  (-846785534307/500000000000000000 : ℝ),
  (1067952150469/1000000000000000000 : ℝ),
  (3307431057/10000000000000000 : ℝ),
  (-21147970513/200000000000000000 : ℝ),
  (-11305235137/1000000000000000000 : ℝ)]
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
    |tailCenter point center-(3175885852563/500000000000000000 : ℝ)| ≤ (25/1000000000000000000 : ℝ) := by
  have h := CertifiedApproximation.finite_linear_error Finset.univ (fun _ : Fin 25 => (1:ℝ))
    (fun i => ∑ j : Fin 25, tailMatrix point i j*(center i*center j)) rowCenter
    (fun _ => (1/1000000000000000000 : ℝ)) (fun i _ => leading_rows i)
  simp only [one_mul, abs_one] at h
  change |tailCenter point center-(∑ i, rowCenter i)| ≤ ∑ _ : Fin 25, (1/1000000000000000000 : ℝ) at h
  norm_num [rowCenter, Fin.sum_univ_succ] at h
  convert! h using 1; norm_num

end KsIndex.AlphaRemarkTrial.Energy8192Tail.Mminus
