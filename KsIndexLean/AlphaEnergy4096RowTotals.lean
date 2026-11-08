module
public import KsIndexLean.AlphaEnergy4096PplusRows0
public import KsIndexLean.AlphaEnergy4096PplusRows5
public import KsIndexLean.AlphaEnergy4096PplusRows10
public import KsIndexLean.AlphaEnergy4096PplusRows15
public import KsIndexLean.AlphaEnergy4096PplusRows20
public import KsIndexLean.AlphaEnergy4096PminusRows0
public import KsIndexLean.AlphaEnergy4096PminusRows5
public import KsIndexLean.AlphaEnergy4096PminusRows10
public import KsIndexLean.AlphaEnergy4096PminusRows15
public import KsIndexLean.AlphaEnergy4096PminusRows20
public import KsIndexLean.AlphaEnergy4096MplusRows0
public import KsIndexLean.AlphaEnergy4096MplusRows5
public import KsIndexLean.AlphaEnergy4096MplusRows10
public import KsIndexLean.AlphaEnergy4096MplusRows15
public import KsIndexLean.AlphaEnergy4096MplusRows20
public import KsIndexLean.AlphaEnergy4096MminusRows0
public import KsIndexLean.AlphaEnergy4096MminusRows5
public import KsIndexLean.AlphaEnergy4096MminusRows10
public import KsIndexLean.AlphaEnergy4096MminusRows15
public import KsIndexLean.AlphaEnergy4096MminusRows20
@[expose] public section
namespace KsIndex.AlphaRemarkTrial.Energy4096Rows
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.style.longLine false
namespace Pplus
theorem center_total : tailCenter point center = (43428354679128720347110426230173923403610407202689951467042064538297948922260606494676224002034420789715138531464165934533 / 2840567984962500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  change (∑ i : Fin 25, centerRow i) = _
  simp only [Fin.sum_univ_succ, center_row_0, center_row_1, center_row_2, center_row_3, center_row_4, center_row_5, center_row_6, center_row_7, center_row_8, center_row_9, center_row_10, center_row_11, center_row_12, center_row_13, center_row_14, center_row_15, center_row_16, center_row_17, center_row_18, center_row_19, center_row_20, center_row_21, center_row_22, center_row_23, center_row_24]
  norm_num
#print axioms center_total
theorem radius_total : tailRadius point center radius = (790282234487018774657428277902442043167740990526713783798773397720476409429363604475987667779436110995685710773733 / 511302237293250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  change (∑ i : Fin 25, radiusRow i) = _
  simp only [Fin.sum_univ_succ, radius_row_0, radius_row_1, radius_row_2, radius_row_3, radius_row_4, radius_row_5, radius_row_6, radius_row_7, radius_row_8, radius_row_9, radius_row_10, radius_row_11, radius_row_12, radius_row_13, radius_row_14, radius_row_15, radius_row_16, radius_row_17, radius_row_18, radius_row_19, radius_row_20, radius_row_21, radius_row_22, radius_row_23, radius_row_24]
  norm_num
#print axioms radius_total
theorem product_total : tailProductUpper point center radius 24583 = (1133268587327390698664739610811141926344111166958321739984380607128615477046359131425043902317519138738214859808608043725473244591278649634156662126779650953 / 19474130436348321408407078692005577703811353252925000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  change (∑ i : Fin 25, productRow i) = _
  simp only [Fin.sum_univ_succ, product_row_0, product_row_1, product_row_2, product_row_3, product_row_4, product_row_5, product_row_6, product_row_7, product_row_8, product_row_9, product_row_10, product_row_11, product_row_12, product_row_13, product_row_14, product_row_15, product_row_16, product_row_17, product_row_18, product_row_19, product_row_20, product_row_21, product_row_22, product_row_23, product_row_24]
  norm_num
#print axioms product_total
end Pplus
namespace Pminus
theorem center_total : tailCenter point center = (331632710528175517626402254427489452480075404793140632512783951897990800932646438843672980938727080253386480573401140315467 / 2840567984962500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  change (∑ i : Fin 25, centerRow i) = _
  simp only [Fin.sum_univ_succ, center_row_0, center_row_1, center_row_2, center_row_3, center_row_4, center_row_5, center_row_6, center_row_7, center_row_8, center_row_9, center_row_10, center_row_11, center_row_12, center_row_13, center_row_14, center_row_15, center_row_16, center_row_17, center_row_18, center_row_19, center_row_20, center_row_21, center_row_22, center_row_23, center_row_24]
  norm_num
#print axioms center_total
theorem radius_total : tailRadius point center radius = (790282234487018774657428277902442043167740990526713783798773397720476409429363604475987667779436110995685710773733 / 511302237293250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  change (∑ i : Fin 25, radiusRow i) = _
  simp only [Fin.sum_univ_succ, radius_row_0, radius_row_1, radius_row_2, radius_row_3, radius_row_4, radius_row_5, radius_row_6, radius_row_7, radius_row_8, radius_row_9, radius_row_10, radius_row_11, radius_row_12, radius_row_13, radius_row_14, radius_row_15, radius_row_16, radius_row_17, radius_row_18, radius_row_19, radius_row_20, radius_row_21, radius_row_22, radius_row_23, radius_row_24]
  norm_num
#print axioms radius_total
theorem product_total : tailProductUpper point center radius 24581 = (1086402064465775419498128742583528289785938509300082320859768585975388437860240524851885031779583612918520530253765588357721570239622290224871857582059903 / 18671265998416415540179365955901800291286052975000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  change (∑ i : Fin 25, productRow i) = _
  simp only [Fin.sum_univ_succ, product_row_0, product_row_1, product_row_2, product_row_3, product_row_4, product_row_5, product_row_6, product_row_7, product_row_8, product_row_9, product_row_10, product_row_11, product_row_12, product_row_13, product_row_14, product_row_15, product_row_16, product_row_17, product_row_18, product_row_19, product_row_20, product_row_21, product_row_22, product_row_23, product_row_24]
  norm_num
#print axioms product_total
end Pminus
namespace Mplus
theorem center_total : tailCenter point center = (4501539303938470737470432164348624673378965757847265168723008201696524496845498596118549873681931934594111460448075075657 / 59178499686718750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  change (∑ i : Fin 25, centerRow i) = _
  simp only [Fin.sum_univ_succ, center_row_0, center_row_1, center_row_2, center_row_3, center_row_4, center_row_5, center_row_6, center_row_7, center_row_8, center_row_9, center_row_10, center_row_11, center_row_12, center_row_13, center_row_14, center_row_15, center_row_16, center_row_17, center_row_18, center_row_19, center_row_20, center_row_21, center_row_22, center_row_23, center_row_24]
  norm_num
#print axioms center_total
theorem radius_total : tailRadius point center radius = (211060309261132016334228205843927906012529643747155199145559894810955672920193169982047154100547250159832695138701 / 491636766628125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  change (∑ i : Fin 25, radiusRow i) = _
  simp only [Fin.sum_univ_succ, radius_row_0, radius_row_1, radius_row_2, radius_row_3, radius_row_4, radius_row_5, radius_row_6, radius_row_7, radius_row_8, radius_row_9, radius_row_10, radius_row_11, radius_row_12, radius_row_13, radius_row_14, radius_row_15, radius_row_16, radius_row_17, radius_row_18, radius_row_19, radius_row_20, radius_row_21, radius_row_22, radius_row_23, radius_row_24]
  norm_num
#print axioms radius_total
theorem product_total : tailProductUpper point center radius 24586 = (768542721039216327978257734871018827589829941688101326345472073937314628653628904847003977507714803711941581825500515099696517783818300000903792844555676681 / 16076889124035907245168182203095981564934745223390000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  change (∑ i : Fin 25, productRow i) = _
  simp only [Fin.sum_univ_succ, product_row_0, product_row_1, product_row_2, product_row_3, product_row_4, product_row_5, product_row_6, product_row_7, product_row_8, product_row_9, product_row_10, product_row_11, product_row_12, product_row_13, product_row_14, product_row_15, product_row_16, product_row_17, product_row_18, product_row_19, product_row_20, product_row_21, product_row_22, product_row_23, product_row_24]
  norm_num
#print axioms product_total
end Mplus
namespace Mminus
theorem center_total : tailCenter point center = (509443672466354212077797085775846441194431213511111738703582203832046704197135691472956737338580933945862599143529825589 / 51130223729325000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  change (∑ i : Fin 25, centerRow i) = _
  simp only [Fin.sum_univ_succ, center_row_0, center_row_1, center_row_2, center_row_3, center_row_4, center_row_5, center_row_6, center_row_7, center_row_8, center_row_9, center_row_10, center_row_11, center_row_12, center_row_13, center_row_14, center_row_15, center_row_16, center_row_17, center_row_18, center_row_19, center_row_20, center_row_21, center_row_22, center_row_23, center_row_24]
  norm_num
#print axioms center_total
theorem radius_total : tailRadius point center radius = (365931143508673671860979209103218106969721666911650503665031779649853568395314743778891520971820878365971719770461 / 852170395488750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  change (∑ i : Fin 25, radiusRow i) = _
  simp only [Fin.sum_univ_succ, radius_row_0, radius_row_1, radius_row_2, radius_row_3, radius_row_4, radius_row_5, radius_row_6, radius_row_7, radius_row_8, radius_row_9, radius_row_10, radius_row_11, radius_row_12, radius_row_13, radius_row_14, radius_row_15, radius_row_16, radius_row_17, radius_row_18, radius_row_19, radius_row_20, radius_row_21, radius_row_22, radius_row_23, radius_row_24]
  norm_num
#print axioms radius_total
theorem product_total : tailProductUpper point center radius 24578 = (702497655480160003735037596783007685701624882067124696052058158387484146820730813680230817190752510164628294488448379408801020276468750573021043832563633610153 / 14690460704609880895938692711515687258746668479072350000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  change (∑ i : Fin 25, productRow i) = _
  simp only [Fin.sum_univ_succ, product_row_0, product_row_1, product_row_2, product_row_3, product_row_4, product_row_5, product_row_6, product_row_7, product_row_8, product_row_9, product_row_10, product_row_11, product_row_12, product_row_13, product_row_14, product_row_15, product_row_16, product_row_17, product_row_18, product_row_19, product_row_20, product_row_21, product_row_22, product_row_23, product_row_24]
  norm_num
#print axioms product_total
end Mminus
end KsIndex.AlphaRemarkTrial.Energy4096Rows
