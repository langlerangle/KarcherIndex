module

public import KsIndexLean.AlphaEnergy8192Data

@[expose] public section


/-! Rowwise rational enclosures of the Mplus energy tail. -/
namespace KsIndex.AlphaRemarkTrial.Energy8192Tail.Mplus
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
theorem leading_row_0 :
    |(∑ j : Fin 25, tailMatrix point (0 : Fin 25) j*(center (0 : Fin 25)*center j))-(-23560288629/500000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_1 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (0 : Fin 24)) j*(center (Fin.succ (0 : Fin 24))*center j))-(-215789438411/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_2 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (0 : Fin 23))) j*(center (Fin.succ (Fin.succ (0 : Fin 23)))*center j))-(702086926563/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_3 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (0 : Fin 22)))) j*(center (Fin.succ (Fin.succ (Fin.succ (0 : Fin 22))))*center j))-(343671344669/500000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_4 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 21))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 21)))))*center j))-(69055169411/62500000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_5 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 20)))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 20))))))*center j))-(13295075584407/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_6 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 19))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 19)))))))*center j))-(6647888604049/500000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_7 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 18)))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 18))))))))*center j))-(-552499665353/500000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_8 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 17))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 17)))))))))*center j))-(21482859861/31250000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_9 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 16)))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 16))))))))))*center j))-(-702235144601/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_10 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 15))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 15)))))))))))*center j))-(-215846384209/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_11 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 14)))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 14))))))))))))*center j))-(47135499533/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_12 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 13))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 13)))))))))))))*center j))-(7210907557/250000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_13 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 12)))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 12))))))))))))))*center j))-(67444886411/250000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_14 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 11))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 11)))))))))))))))*center j))-(-421920979721/500000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_15 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 10)))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 10))))))))))))))))*center j))-(-2724721437883/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_16 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 9))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 9)))))))))))))))))*center j))-(4320895254531/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_17 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 8)))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 8))))))))))))))))))*center j))-(4731825280403/500000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_18 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 7))))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 7)))))))))))))))))))*center j))-(4862861621283/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_19 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 6)))))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 6))))))))))))))))))))*center j))-(-9464306249077/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_20 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 5))))))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 5)))))))))))))))))))))*center j))-(135046688343/31250000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_21 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 4)))))))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 4))))))))))))))))))))))*center j))-(8516524477/3125000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_22 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 3))))))))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 3)))))))))))))))))))))))*center j))-(-211018962207/250000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_23 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 2)))))))))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 2))))))))))))))))))))))))*center j))-(-269873017753/1000000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

theorem leading_row_24 :
    |(∑ j : Fin 25, tailMatrix point (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1))))))))))))))))))))))))) j*(center (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1)))))))))))))))))))))))))*center j))-(14427811507/500000000000000000 : ℝ)| ≤ (1/1000000000000000000 : ℝ) := by
  simp only [Fin.sum_univ_succ, tailMatrix, point, shift, center, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

noncomputable def rowCenter : Fin 25 → ℝ := ![(-23560288629/500000000000000000 : ℝ),
  (-215789438411/1000000000000000000 : ℝ),
  (702086926563/1000000000000000000 : ℝ),
  (343671344669/500000000000000000 : ℝ),
  (69055169411/62500000000000000 : ℝ),
  (13295075584407/1000000000000000000 : ℝ),
  (6647888604049/500000000000000000 : ℝ),
  (-552499665353/500000000000000000 : ℝ),
  (21482859861/31250000000000000 : ℝ),
  (-702235144601/1000000000000000000 : ℝ),
  (-215846384209/1000000000000000000 : ℝ),
  (47135499533/1000000000000000000 : ℝ),
  (7210907557/250000000000000000 : ℝ),
  (67444886411/250000000000000000 : ℝ),
  (-421920979721/500000000000000000 : ℝ),
  (-2724721437883/1000000000000000000 : ℝ),
  (4320895254531/1000000000000000000 : ℝ),
  (4731825280403/500000000000000000 : ℝ),
  (4862861621283/1000000000000000000 : ℝ),
  (-9464306249077/1000000000000000000 : ℝ),
  (135046688343/31250000000000000 : ℝ),
  (8516524477/3125000000000000 : ℝ),
  (-211018962207/250000000000000000 : ℝ),
  (-269873017753/1000000000000000000 : ℝ),
  (14427811507/500000000000000000 : ℝ)]
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
    |tailCenter point center-(39408610841021/1000000000000000000 : ℝ)| ≤ (25/1000000000000000000 : ℝ) := by
  have h := CertifiedApproximation.finite_linear_error Finset.univ (fun _ : Fin 25 => (1:ℝ))
    (fun i => ∑ j : Fin 25, tailMatrix point i j*(center i*center j)) rowCenter
    (fun _ => (1/1000000000000000000 : ℝ)) (fun i _ => leading_rows i)
  simp only [one_mul, abs_one] at h
  change |tailCenter point center-(∑ i, rowCenter i)| ≤ ∑ _ : Fin 25, (1/1000000000000000000 : ℝ) at h
  norm_num [rowCenter, Fin.sum_univ_succ] at h
  convert! h using 1; norm_num

end KsIndex.AlphaRemarkTrial.Energy8192Tail.Mplus
