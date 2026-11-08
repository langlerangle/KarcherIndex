module
public import KsIndexLean.AlphaEnergy4096RowData
@[expose] public section
namespace KsIndex.AlphaRemarkTrial.Energy4096Rows
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.style.longLine false
namespace Pplus
theorem center_row_5 : centerRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 20))))))) = (41292450445189603932675680175457243517907634828076395069268222359733909619355095833299652031672853741895361635526937 / 3002512500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [centerRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms center_row_5
theorem radius_row_5 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 20))))))) = (3727166892663824632818256472351236751440608374022693915069057653641041709240124129890267530029502560647815421 / 9007537500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms radius_row_5
theorem product_row_5 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 20))))))) = (2342657186784416221136505920254503731432777665881368892504631380336022048967017766755167250825254449537106672357621188839540276560052367846291848788862447 / 278201863376404591548672552742936824340162189327500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms product_row_5
theorem center_row_6 : centerRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 19)))))))) = (2294267158538112166366388123844428447504474031533596842437491882678167118414430761661805869401384918443413512101623 / 166806250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [centerRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms center_row_6
theorem radius_row_6 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 19)))))))) = (69028894338120066676792054784897035005316416943507010005556627000083013196710646035464676277706324932099413 / 166806250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms radius_row_6
theorem product_row_6 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 19)))))))) = (33573273823992536228425946089073929422449792270715992298522861300569942674796057386681657316484601547784006358300409024906737424974012083136912256557067281 / 2782018633764045915486725527429368243401621893275000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms product_row_6
theorem center_row_7 : centerRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 18))))))))) = (49703956743013196338920938729691064410546698387290664649259011842578619856074544464616592354051068903627 / 66722500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [centerRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms center_row_7
theorem radius_row_7 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 18))))))))) = (283930091928096652506018947333977058267279929895999928502203463494789205549884068986170944347821 / 33361250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms radius_row_7
theorem product_row_7 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 18))))))))) = (617615310717703280916714117651422016876931977999266933209943619284358313040566772418641228124113419811800897343906095729042180082013327715812667670523 / 723071769659271193108960500956301037921149290000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms product_row_7
theorem center_row_8 : centerRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 17)))))))))) = (213534358684879903009039135685976555877984380533907491555946771223063273410536354368977664337432753388323835828571 / 300251250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [centerRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms center_row_8
theorem radius_row_8 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 17)))))))))) = (38548363371794155714872657556859992759382465920659629759836759467676889249863734575223741411385763411530121 / 1801507500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms radius_row_8
theorem product_row_8 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 17)))))))))) = (53722698530595549163526999762326384611922645349016763288099634669301436623068561390349713800904819480932724432844783005092948175481263765083275985832221 / 42800286673293014084411161960451819129255721435000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms product_row_8
theorem center_row_9 : centerRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 16))))))))))) = (2429915029668557525630421083206124710600796786775979631498866622884487779100805402489637223945490648893 / 5132500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [centerRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms center_row_9
theorem radius_row_9 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 16))))))))))) = (333136937802395824348726946909307724320794922808532551624458317824815496438067141135841277922867 / 61590000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms radius_row_9
theorem product_row_9 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 16))))))))))) = (2659551981496162997840091866128724943616226725623356057546820000564839957928217559501412773077520398443157377788427406714361451403071696334422471901228187 / 2832600790741574023041029627928084029645287745880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms product_row_9
end Pplus
end KsIndex.AlphaRemarkTrial.Energy4096Rows
