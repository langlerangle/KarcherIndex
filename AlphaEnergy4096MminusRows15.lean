module
public import AlphaEnergy4096RowData
@[expose] public section
namespace KsIndex.AlphaRemarkTrial.Energy4096Rows
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.style.longLine false
namespace Mminus
theorem center_row_15 : centerRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))))))))))))) = (-35009324877115464945489229282138946669179825430985653754726066166334708798766062687693593520884200239584581 / 17738693750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [centerRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms center_row_15
theorem radius_row_15 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))))))))))))) = (60037087583225692004079773266050332665449559409214284693633617066128917074942017775160525961292311 / 7095477500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms radius_row_15
theorem product_row_15 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))))))))))))) = (3020591269017780768117965401949932127533475376230037943024639750652315142109284563824826341241243930099521966163780568488839886616594119232921351935571341 / 1530256323396862593326947157449550756119444633236703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms product_row_15
theorem center_row_16 : centerRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))))))))))))) = (-13878106917807400102825672178120834138859731614426106679439195283804343430106631763493834958819162876542347453523667 / 4434673437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [centerRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms center_row_16
theorem radius_row_16 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))))))))))))) = (10439730541438467427531849446168049368725030637349700084857612809882545308306947585310505262527372495784999 / 177386937500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms radius_row_16
theorem product_row_16 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))))))))))))) = (26288718753764156571802916596740172252820034319708091961475075813382624093368015270749561658903805615133503427812821786397516797528081630527498140307007421 / 10528280485864702027667481637493325794610608083425000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms product_row_16
theorem center_row_17 : centerRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))))))))))))) = (12157101320740477202268667217873712384205453122113665475609280045732942909659562393581885818682864745097287 / 1773869375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [centerRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms center_row_17
theorem radius_row_17 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))))))))))))) = (104240364433383945872519698405772550644700383708068667297505633419064697625904126483042224941359939 / 3547738750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms radius_row_17
theorem product_row_17 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))))))))))))) = (8092336067263508035001471939357817343789350051969023943419256124061666529060391019952510799002202445209011363180978252454610441237033129987182208944541 / 1760601714358806435275490497545024839255353365181250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms product_row_17
theorem center_row_18 : centerRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))))))))))))) = (-1249246403465878446450525781976022079326452898009263724397691807291103494392110820372729283489878094458628427141243 / 354773875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [centerRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms center_row_18
theorem radius_row_18 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))))))))))))) = (46986941047811817117030832689679884335389910665428351149393996474694579905685274435289798199755149478697423 / 709547750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms radius_row_18
theorem product_row_18 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))))))))))))) = (12253696246256336813294408395025838168103189525545001838249264437043721816026170591441433537921365927585605383073777209777595675084679381591119861766793873 / 4629346860696391038636142661191918253806723260211875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms product_row_18
theorem center_row_19 : centerRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))))))))))))) = (-9724333330621101004445146912245481362352207868744381928029115883193767466973483287869730029863104788772007 / 1419095500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [centerRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms center_row_19
theorem radius_row_19 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))))))))))))) = (416903677740308492015957459151430444162323140616511630980918027861988846150797467857288665525333987 / 14190955000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms radius_row_19
theorem product_row_19 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))))))))))))) = (1878550278130994155641967288921236641716900505197397326208979145380881132991397006199315963861261716342786258465925099538834860191064961862621022131590113 / 327912069299327698570060105167760876311309564265007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms product_row_19
end Mminus
end KsIndex.AlphaRemarkTrial.Energy4096Rows
