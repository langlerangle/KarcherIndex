module
public import AlphaEnergy4096RowData
@[expose] public section
namespace KsIndex.AlphaRemarkTrial.Energy4096Rows
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.style.longLine false
namespace Pplus
theorem center_row_10 : centerRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 15)))))))))))) = (-68768379253144348842932054106911648874846766805988160003091384057464608752674619240729229657772094321565626511767 / 307950000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [centerRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms center_row_10
theorem radius_row_10 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 15)))))))))))) = (8965981021992175014211164349604718267021905452750323410865248303932170031232771217445027512162447716404627 / 1334450000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms radius_row_10
theorem product_row_10 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 15)))))))))))) = (522781115566888696207938793308177275685845501348407905306350948125822122911004665936597863592697254205160194536659595471055480256704105081792574518075727 / 856005733465860281688223239209036382585114428700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms product_row_10
theorem center_row_11 : centerRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 14))))))))))))) = (-1834983243069683840487072227877580683446053695687783491599544345520949905713811822150926005371625212689 / 57740625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [centerRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms center_row_11
theorem radius_row_11 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 14))))))))))))) = (251572870265478072325558496727984557819902841710981138697350230239996152199095055815116516509891 / 692887500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms radius_row_11
theorem product_row_11 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 14))))))))))))) = (1356619838742503277930422827594611609901938486841729179621730519987585409427452884003989215146933033300426417294107472543765036905647469024658047834401 / 15017644446769478626109179635246252326054639100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms product_row_11
theorem center_row_12 : centerRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 13)))))))))))))) = (-2273405607978067560731549102700796383634694609290976344259446031462994987836927121164121039423844953135873 / 70954775000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [centerRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms center_row_12
theorem radius_row_12 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 13)))))))))))))) = (2655385009216057659262837494408507483539050414816672091823474359440730893746868918878557925266661 / 7095477500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms radius_row_12
theorem product_row_12 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 13)))))))))))))) = (6141779878682663143596557296584543684845014021434973143321349257005627185761122832462828290813356932794642600597503625025024850415824032477656324842253 / 97370652181741607042035393460027888519056766264625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms product_row_12
theorem center_row_13 : centerRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 12))))))))))))))) = (34643223770170325897157905161994910035302988110072312913495868670679444338948337424969241577852237612624156982561 / 177386937500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [centerRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms center_row_13
theorem radius_row_13 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 12))))))))))))))) = (83589892305142462234519782061831174200322751616304607074629654807297035923623805626905013455030103096741 / 17738693750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms radius_row_13
theorem product_row_13 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 12))))))))))))))) = (83704066772651551273172698188624257168101586150344880250840523899734106711879694646503428322339459053411777910140704847182014117540785017715161323121 / 237634294525299834147737384893295640070913401500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms product_row_13
theorem center_row_14 : centerRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))))))))))))) = (1662869602609079163779327191590455264292253070617154885334720626935588865354162453812948909177922780305473 / 1773869375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [centerRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms center_row_14
theorem radius_row_14 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))))))))))))) = (1942266263245621501283250743781793959004780243165426127802054161713713072235371024608441907205989 / 177386937500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms radius_row_14
theorem product_row_14 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))))))))))))) = (57403767291596017674219062891451539222017788918782255221951315474607251264680098647627511961441347110877732447906969289359582833884786083048877114119063 / 48685326090870803521017696730013944259528383132312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms product_row_14
end Pplus
end KsIndex.AlphaRemarkTrial.Energy4096Rows
