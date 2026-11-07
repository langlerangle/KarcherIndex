module
public import AlphaEnergy4096RowData
@[expose] public section
namespace KsIndex.AlphaRemarkTrial.Energy4096Rows
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.style.longLine false
namespace Mplus
theorem center_row_20 : centerRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))))))))))))) = (3947169837869599607291195628723067562494493513248748757758537870451086563628275216145145121850383897570366873493349 / 443467343750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [centerRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms center_row_20
theorem radius_row_20 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))))))))))))) = (52184842071164283116897473946609201234177890305314195702973681332062763478201771076697070449861409276857463 / 886934687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms radius_row_20
theorem product_row_20 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))))))))))))) = (59566296104055273225597003289347807833236584023584398127204749332927843225126880463080232822025040870389637498779841079717332922663300159766235979510199057 / 15072083553783663042345170815402482717126323646928125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms product_row_20
theorem center_row_21 : centerRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))))))))))))) = (4978623874242009654164251478550723525091915748455552714859878047071301159874146511357454883982999978310433 / 886934687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [centerRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms center_row_21
theorem radius_row_21 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))))))))))))) = (15005236892281038538633153995125944155377670558668568700970655408198407358251732157297999868815399 / 1773869375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms radius_row_21
theorem product_row_21 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))))))))))))) = (394528095877866138037283774042887749450656891027699999850850874284089453465684745386688152115700537534222668166355210817465248906684270151506836615158501 / 133974076033632560376401518359133179707789543528250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms product_row_21
theorem center_row_22 : centerRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))))))))))))) = (-385508069432079451199914575357410936251862860377014058524036974265250043982488111425282551529703512522991246392171 / 221733671875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [centerRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms center_row_22
theorem radius_row_22 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))))))))))))) = (10193469522117424835904166861699734273592415923891127140166094474494295451895391528132087707399981558291007 / 886934687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms radius_row_22
theorem product_row_22 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))))))))))))) = (30336168210730747513287511170594469084107604139569550945301588856259654388263552685728550621146783653829338588206101995552555325111807177225955757847087419 / 24115333686053860867752273304643972347402117835085000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms product_row_22
theorem center_row_23 : centerRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))))))))))))) = (-49304494448890366728525117853949127572974499879770811721587640605066551679950406557359391934447291561871 / 88693468750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [centerRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms center_row_23
theorem radius_row_23 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))))))))))))) = (74300212041262872262046409994167306360452844188035879850835106539218550277568271473959364267223 / 88693468750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms radius_row_23
theorem product_row_23 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))))))))))))) = (2647059725423241776060681508803059849467339909825224192237600599735741058584836510935761654763994557333632699430716576979676502922304252483112424642107 / 6028833421513465216938068326160993086850529458771250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms product_row_23
theorem center_row_24 : centerRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))))))))))))) = (527196545405229088518325780509406524990695674428541630544510579338813325515458786242400256272728500957095815848989 / 8869346875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [centerRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms center_row_24
theorem radius_row_24 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))))))))))))) = (6969973320753793450840265271496792391423401691149508849909380749769981103374297919850075422348687600488689 / 17738693750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms radius_row_24
theorem product_row_24 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))))))))))))) = (5131515943395929723602021410276273910033720049933574435972383730566015273726406755247269738545495652289702266488637253848821480965388344716783158150963 / 84437442878339848976723646024663768723396771131250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms product_row_24
end Mplus
end KsIndex.AlphaRemarkTrial.Energy4096Rows
