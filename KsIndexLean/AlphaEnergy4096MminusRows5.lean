module
public import KsIndexLean.AlphaEnergy4096RowData
@[expose] public section
namespace KsIndex.AlphaRemarkTrial.Energy4096Rows
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.style.longLine false
namespace Mminus
theorem center_row_5 : centerRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 20))))))) = (322967987659292537144366539446649082269077567520393242913738929145090880420786535386444542366775062613917 / 36030150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [centerRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms center_row_5
theorem radius_row_5 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 20))))))) = (16787566914629442654070294257862436962310710029005501987910043379783350567667106992889423526548697 / 450376875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms radius_row_5
theorem product_row_5 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 20))))))) = (18151226958777627070518444009185157214304860245834637550611027164240412294918541367400563010640317191065751893967303061294033288338882373255087165518677047027 / 3147955865273545906272577009610504412588571816944075000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms product_row_5
theorem center_row_6 : centerRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 19)))))))) = (40366737237595524965634078564410197673117718842683652804220294766110167085002779071139814995898445094771 / 4503768750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [centerRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms center_row_6
theorem radius_row_6 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 19)))))))) = (55952649872018192212780810227345633733800011885508753250970435567576513686958796007216945792095733 / 1501256250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms radius_row_6
theorem product_row_6 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 19)))))))) = (261036926006219681351275483624547477120813700021085083497724654411298232061783435022928457391016376158323981052756002029934347633153126288612251832580121321 / 31797533992662079861339161713237418308975472898425000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms product_row_6
theorem center_row_7 : centerRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 18))))))))) = (198789652324997167987672626651658752903913717026649005855333856453335401465487066547906590633731125327677578829 / 266890000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [centerRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms center_row_7
theorem radius_row_7 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 18))))))))) = (9903068798777795293011678907236008739532722779725790343937022128561381417343048861348816640248311031049 / 513250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms radius_row_7
theorem product_row_7 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 18))))))))) = (30115353668733545695292223018310210266437674391270064695165783679223620769626760436850782073171174349443568224057588233508499683274561673507018866847607 / 26082988360871206448525785148815182803783012817500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms product_row_7
theorem center_row_8 : centerRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 17)))))))))) = (222593235725724269402102627592477789307681399507836218402658819614379176027716190811083651417135831449 / 480402000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [centerRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms center_row_8
theorem radius_row_8 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 17)))))))))) = (1157018336885929827470745735304734151187464700567286251508791348527513513276302370925343000832439 / 600502500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms radius_row_8
theorem product_row_8 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 17)))))))))) = (2136489643818076380466585549825039363843384223041039496483354954985479927769012103603229247440869351600789654353588250697766729177375432157595569768981596839 / 2518364692218836725018061607688403530070857453555260000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms product_row_8
theorem center_row_9 : centerRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 16))))))))))) = (68208630651730997235660735956858643522431304739806467897382322151257467954586807605086257371562540752523019243179 / 144120600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [centerRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms center_row_9
theorem radius_row_9 : radiusRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 16))))))))))) = (44173184084212544654935620057990118918337982704879908300537286592551065463031630416755445194548210282111799 / 3603015000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [radiusRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms radius_row_9
theorem product_row_9 : productRow (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 16))))))))))) = (55929737005919601653080165148139989879915431533579475145633696002327854124418705804204859826800212648691941206871018158611865383803099255262904193544250674013 / 44071382113829642687816078134547061776240005437217050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [productRow, Fin.sum_univ_succ, tailMatrix, point, center, radius, coefficient, exponent,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
#print axioms product_row_9
end Mminus
end KsIndex.AlphaRemarkTrial.Energy4096Rows
