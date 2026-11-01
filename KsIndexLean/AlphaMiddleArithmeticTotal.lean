module

public import KsIndexLean.AlphaMiddleArithmeticBlock0
public import KsIndexLean.AlphaMiddleArithmeticBlock32
public import KsIndexLean.AlphaMiddleArithmeticBlock64
public import KsIndexLean.AlphaMiddleArithmeticBlock96
public import KsIndexLean.AlphaMiddleArithmeticBlock128
public import KsIndexLean.AlphaMiddleArithmeticBlock160
public import KsIndexLean.AlphaMiddleArithmeticBlock192
public import KsIndexLean.AlphaMiddleArithmeticBlock224
public import KsIndexLean.AlphaMiddleArithmeticBlock256
public import KsIndexLean.AlphaMiddleArithmeticBlock288
public import KsIndexLean.AlphaMiddleArithmeticBlock320
public import KsIndexLean.AlphaMiddleArithmeticBlock352
public import KsIndexLean.AlphaMiddleArithmeticBlock384
public import KsIndexLean.AlphaMiddleArithmeticBlock416
public import KsIndexLean.AlphaMiddleArithmeticBlock448
public import KsIndexLean.AlphaMiddleArithmeticBlock480
public import KsIndexLean.AlphaMiddleArithmeticBlock512
public import KsIndexLean.AlphaMiddleArithmeticBlock544
public import KsIndexLean.AlphaMiddleArithmeticBlock576
public import KsIndexLean.AlphaMiddleArithmeticBlock608
public import KsIndexLean.AlphaMiddleArithmeticBlock640
public import KsIndexLean.AlphaMiddleArithmeticBlock672
public import KsIndexLean.AlphaMiddleArithmeticBlock704
public import KsIndexLean.AlphaMiddleArithmeticBlock736
public import KsIndexLean.AlphaMiddleArithmeticBlock768
public import KsIndexLean.AlphaMiddleArithmeticBlock800
public import KsIndexLean.AlphaMiddleArithmeticBlock832
public import KsIndexLean.AlphaMiddleArithmeticBlock864
public import KsIndexLean.AlphaMiddleArithmeticBlock896
public import KsIndexLean.AlphaMiddleArithmeticBlock928
public import KsIndexLean.AlphaMiddleArithmeticBlock960
public import KsIndexLean.AlphaMiddleArithmeticBlock992
public import KsIndexLean.AlphaMiddleArithmeticBlock1024
public import KsIndexLean.AlphaMiddleArithmeticBlock1056
public import KsIndexLean.AlphaMiddleArithmeticBlock1088
public import KsIndexLean.AlphaMiddleArithmeticBlock1120
public import KsIndexLean.AlphaMiddleArithmeticBlock1152
public import KsIndexLean.AlphaMiddleArithmeticBlock1184
public import KsIndexLean.AlphaMiddleArithmeticBlock1216
public import KsIndexLean.AlphaMiddleArithmeticBlock1248
public import KsIndexLean.AlphaMiddleArithmeticBlock1280
public import KsIndexLean.AlphaMiddleArithmeticBlock1312
public import KsIndexLean.AlphaMiddleArithmeticBlock1344
public import KsIndexLean.AlphaMiddleArithmeticBlock1376
public import KsIndexLean.AlphaMiddleArithmeticBlock1408
public import KsIndexLean.AlphaMiddleArithmeticBlock1440
public import KsIndexLean.AlphaMiddleArithmeticBlock1472
public import KsIndexLean.AlphaMiddleArithmeticBlock1504
public import KsIndexLean.AlphaMiddleArithmeticBlock1536
public import KsIndexLean.AlphaMiddleArithmeticBlock1568
public import KsIndexLean.AlphaMiddleArithmeticBlock1600
public import KsIndexLean.AlphaMiddleArithmeticBlock1632
public import KsIndexLean.AlphaMiddleArithmeticBlock1664
public import KsIndexLean.AlphaMiddleArithmeticBlock1696
public import KsIndexLean.AlphaMiddleArithmeticBlock1728
public import KsIndexLean.AlphaMiddleArithmeticBlock1760
public import KsIndexLean.AlphaMiddleArithmeticBlock1792
public import KsIndexLean.AlphaMiddleArithmeticBlock1824
public import KsIndexLean.AlphaMiddleArithmeticBlock1856
public import KsIndexLean.AlphaMiddleArithmeticBlock1888
public import KsIndexLean.AlphaMiddleArithmeticBlock1920
public import KsIndexLean.AlphaMiddleArithmeticBlock1952
public import KsIndexLean.AlphaMiddleArithmeticBlock1984
public import KsIndexLean.AlphaMiddleArithmeticBlock2016

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.MiddleArithmeticTotal
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
def blockEnergy : Fin 64 → ℚ := ![(∑ i : Fin 32, MiddleBlock0.energy i),(∑ i : Fin 32, MiddleBlock32.energy i),(∑ i : Fin 32, MiddleBlock64.energy i),(∑ i : Fin 32, MiddleBlock96.energy i),(∑ i : Fin 32, MiddleBlock128.energy i),(∑ i : Fin 32, MiddleBlock160.energy i),(∑ i : Fin 32, MiddleBlock192.energy i),(∑ i : Fin 32, MiddleBlock224.energy i),(∑ i : Fin 32, MiddleBlock256.energy i),(∑ i : Fin 32, MiddleBlock288.energy i),(∑ i : Fin 32, MiddleBlock320.energy i),(∑ i : Fin 32, MiddleBlock352.energy i),(∑ i : Fin 32, MiddleBlock384.energy i),(∑ i : Fin 32, MiddleBlock416.energy i),(∑ i : Fin 32, MiddleBlock448.energy i),(∑ i : Fin 32, MiddleBlock480.energy i),(∑ i : Fin 32, MiddleBlock512.energy i),(∑ i : Fin 32, MiddleBlock544.energy i),(∑ i : Fin 32, MiddleBlock576.energy i),(∑ i : Fin 32, MiddleBlock608.energy i),(∑ i : Fin 32, MiddleBlock640.energy i),(∑ i : Fin 32, MiddleBlock672.energy i),(∑ i : Fin 32, MiddleBlock704.energy i),(∑ i : Fin 32, MiddleBlock736.energy i),(∑ i : Fin 32, MiddleBlock768.energy i),(∑ i : Fin 32, MiddleBlock800.energy i),(∑ i : Fin 32, MiddleBlock832.energy i),(∑ i : Fin 32, MiddleBlock864.energy i),(∑ i : Fin 32, MiddleBlock896.energy i),(∑ i : Fin 32, MiddleBlock928.energy i),(∑ i : Fin 32, MiddleBlock960.energy i),(∑ i : Fin 32, MiddleBlock992.energy i),(∑ i : Fin 32, MiddleBlock1024.energy i),(∑ i : Fin 32, MiddleBlock1056.energy i),(∑ i : Fin 32, MiddleBlock1088.energy i),(∑ i : Fin 32, MiddleBlock1120.energy i),(∑ i : Fin 32, MiddleBlock1152.energy i),(∑ i : Fin 32, MiddleBlock1184.energy i),(∑ i : Fin 32, MiddleBlock1216.energy i),(∑ i : Fin 32, MiddleBlock1248.energy i),(∑ i : Fin 32, MiddleBlock1280.energy i),(∑ i : Fin 32, MiddleBlock1312.energy i),(∑ i : Fin 32, MiddleBlock1344.energy i),(∑ i : Fin 32, MiddleBlock1376.energy i),(∑ i : Fin 32, MiddleBlock1408.energy i),(∑ i : Fin 32, MiddleBlock1440.energy i),(∑ i : Fin 32, MiddleBlock1472.energy i),(∑ i : Fin 32, MiddleBlock1504.energy i),(∑ i : Fin 32, MiddleBlock1536.energy i),(∑ i : Fin 32, MiddleBlock1568.energy i),(∑ i : Fin 32, MiddleBlock1600.energy i),(∑ i : Fin 32, MiddleBlock1632.energy i),(∑ i : Fin 32, MiddleBlock1664.energy i),(∑ i : Fin 32, MiddleBlock1696.energy i),(∑ i : Fin 32, MiddleBlock1728.energy i),(∑ i : Fin 32, MiddleBlock1760.energy i),(∑ i : Fin 32, MiddleBlock1792.energy i),(∑ i : Fin 32, MiddleBlock1824.energy i),(∑ i : Fin 32, MiddleBlock1856.energy i),(∑ i : Fin 32, MiddleBlock1888.energy i),(∑ i : Fin 32, MiddleBlock1920.energy i),(∑ i : Fin 32, MiddleBlock1952.energy i),(∑ i : Fin 32, MiddleBlock1984.energy i),(∑ i : Fin 30, MiddleBlock2016.energy i)]
def certifiedTotal : Fin 64 → ℚ := ![(255736436772/1000000000000000000),(106991531428/1000000000000000000),(31969772021/1000000000000000000),(13318161784/1000000000000000000),(6825130227/1000000000000000000),(3991735547/1000000000000000000),(2550185636/1000000000000000000),(1735463612/1000000000000000000),(1238474741/1000000000000000000),(917109447/1000000000000000000),(699540730/1000000000000000000),(546675574/1000000000000000000),(435934212/1000000000000000000),(353623121/1000000000000000000),(291092646/1000000000000000000),(242687180/1000000000000000000),(204597482/1000000000000000000),(174190981/1000000000000000000),(149606829/1000000000000000000),(129503158/1000000000000000000),(112895023/1000000000000000000),(99047890/1000000000000000000),(87406056/1000000000000000000),(77543624/1000000000000000000),(69130306/1000000000000000000),(61907171/1000000000000000000),(55669218/1000000000000000000),(50252650/1000000000000000000),(45525484/1000000000000000000),(41380535/1000000000000000000),(37730132/1000000000000000000),(34502067/1000000000000000000),(31636499/1000000000000000000),(29083533/1000000000000000000),(26801344/1000000000000000000),(24754680/1000000000000000000),(22913699/1000000000000000000),(21252987/1000000000000000000),(19750850/1000000000000000000),(18388648/1000000000000000000),(17150349/1000000000000000000),(16022065/1000000000000000000),(14991746/1000000000000000000),(14048927/1000000000000000000),(13184437/1000000000000000000),(12390238/1000000000000000000),(11659288/1000000000000000000),(10985362/1000000000000000000),(10362972/1000000000000000000),(9787241/1000000000000000000),(9253856/1000000000000000000),(8758954/1000000000000000000),(8299114/1000000000000000000),(7871258/1000000000000000000),(7472631/1000000000000000000),(7100769/1000000000000000000),(6753439/1000000000000000000),(6428640/1000000000000000000),(6124564/1000000000000000000),(5839572/1000000000000000000),(5572176/1000000000000000000),(5321036/1000000000000000000),(5084921/1000000000000000000),(4565060/1000000000000000000)]
theorem blockEnergy_eq (b : Fin 64) : blockEnergy b = certifiedTotal b := by
  fin_cases b
  · exact MiddleBlock0.total
  · exact MiddleBlock32.total
  · exact MiddleBlock64.total
  · exact MiddleBlock96.total
  · exact MiddleBlock128.total
  · exact MiddleBlock160.total
  · exact MiddleBlock192.total
  · exact MiddleBlock224.total
  · exact MiddleBlock256.total
  · exact MiddleBlock288.total
  · exact MiddleBlock320.total
  · exact MiddleBlock352.total
  · exact MiddleBlock384.total
  · exact MiddleBlock416.total
  · exact MiddleBlock448.total
  · exact MiddleBlock480.total
  · exact MiddleBlock512.total
  · exact MiddleBlock544.total
  · exact MiddleBlock576.total
  · exact MiddleBlock608.total
  · exact MiddleBlock640.total
  · exact MiddleBlock672.total
  · exact MiddleBlock704.total
  · exact MiddleBlock736.total
  · exact MiddleBlock768.total
  · exact MiddleBlock800.total
  · exact MiddleBlock832.total
  · exact MiddleBlock864.total
  · exact MiddleBlock896.total
  · exact MiddleBlock928.total
  · exact MiddleBlock960.total
  · exact MiddleBlock992.total
  · exact MiddleBlock1024.total
  · exact MiddleBlock1056.total
  · exact MiddleBlock1088.total
  · exact MiddleBlock1120.total
  · exact MiddleBlock1152.total
  · exact MiddleBlock1184.total
  · exact MiddleBlock1216.total
  · exact MiddleBlock1248.total
  · exact MiddleBlock1280.total
  · exact MiddleBlock1312.total
  · exact MiddleBlock1344.total
  · exact MiddleBlock1376.total
  · exact MiddleBlock1408.total
  · exact MiddleBlock1440.total
  · exact MiddleBlock1472.total
  · exact MiddleBlock1504.total
  · exact MiddleBlock1536.total
  · exact MiddleBlock1568.total
  · exact MiddleBlock1600.total
  · exact MiddleBlock1632.total
  · exact MiddleBlock1664.total
  · exact MiddleBlock1696.total
  · exact MiddleBlock1728.total
  · exact MiddleBlock1760.total
  · exact MiddleBlock1792.total
  · exact MiddleBlock1824.total
  · exact MiddleBlock1856.total
  · exact MiddleBlock1888.total
  · exact MiddleBlock1920.total
  · exact MiddleBlock1952.total
  · exact MiddleBlock1984.total
  · exact MiddleBlock2016.total
theorem total_exact : (∑ b : Fin 64, blockEnergy b) = (429694054139/1000000000000000000 : ℚ) := by
  calc
    _ = ∑ b : Fin 64, certifiedTotal b := by
      apply Finset.sum_congr rfl
      intro b _
      exact blockEnergy_eq b
    _ = _ := by decide +kernel
theorem budget : (∑ b : Fin 64, blockEnergy b) ≤ (6/10000000 : ℚ) := by
  rw [total_exact]
  norm_num
def blockLength : Fin 64 → ℕ := ![32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,30]
theorem row_count : (∑ b : Fin 64, blockLength b) = 2046 := by decide +kernel
#print axioms total_exact
#print axioms budget
#print axioms row_count
end KsIndex.AlphaRemarkTrial.MiddleArithmeticTotal
