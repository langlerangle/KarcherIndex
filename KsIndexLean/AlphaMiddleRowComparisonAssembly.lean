module

public import KsIndexLean.AlphaMiddleRowComparisonBlock0
public import KsIndexLean.AlphaMiddleRowComparisonBlock32
public import KsIndexLean.AlphaMiddleRowComparisonBlock64
public import KsIndexLean.AlphaMiddleRowComparisonBlock96
public import KsIndexLean.AlphaMiddleRowComparisonBlock128
public import KsIndexLean.AlphaMiddleRowComparisonBlock160
public import KsIndexLean.AlphaMiddleRowComparisonBlock192
public import KsIndexLean.AlphaMiddleRowComparisonBlock224
public import KsIndexLean.AlphaMiddleRowComparisonBlock256
public import KsIndexLean.AlphaMiddleRowComparisonBlock288
public import KsIndexLean.AlphaMiddleRowComparisonBlock320
public import KsIndexLean.AlphaMiddleRowComparisonBlock352
public import KsIndexLean.AlphaMiddleRowComparisonBlock384
public import KsIndexLean.AlphaMiddleRowComparisonBlock416
public import KsIndexLean.AlphaMiddleRowComparisonBlock448
public import KsIndexLean.AlphaMiddleRowComparisonBlock480
public import KsIndexLean.AlphaMiddleRowComparisonBlock512
public import KsIndexLean.AlphaMiddleRowComparisonBlock544
public import KsIndexLean.AlphaMiddleRowComparisonBlock576
public import KsIndexLean.AlphaMiddleRowComparisonBlock608
public import KsIndexLean.AlphaMiddleRowComparisonBlock640
public import KsIndexLean.AlphaMiddleRowComparisonBlock672
public import KsIndexLean.AlphaMiddleRowComparisonBlock704
public import KsIndexLean.AlphaMiddleRowComparisonBlock736
public import KsIndexLean.AlphaMiddleRowComparisonBlock768
public import KsIndexLean.AlphaMiddleRowComparisonBlock800
public import KsIndexLean.AlphaMiddleRowComparisonBlock832
public import KsIndexLean.AlphaMiddleRowComparisonBlock864
public import KsIndexLean.AlphaMiddleRowComparisonBlock896
public import KsIndexLean.AlphaMiddleRowComparisonBlock928
public import KsIndexLean.AlphaMiddleRowComparisonBlock960
public import KsIndexLean.AlphaMiddleRowComparisonBlock992
public import KsIndexLean.AlphaMiddleRowComparisonBlock1024
public import KsIndexLean.AlphaMiddleRowComparisonBlock1056
public import KsIndexLean.AlphaMiddleRowComparisonBlock1088
public import KsIndexLean.AlphaMiddleRowComparisonBlock1120
public import KsIndexLean.AlphaMiddleRowComparisonBlock1152
public import KsIndexLean.AlphaMiddleRowComparisonBlock1184
public import KsIndexLean.AlphaMiddleRowComparisonBlock1216
public import KsIndexLean.AlphaMiddleRowComparisonBlock1248
public import KsIndexLean.AlphaMiddleRowComparisonBlock1280
public import KsIndexLean.AlphaMiddleRowComparisonBlock1312
public import KsIndexLean.AlphaMiddleRowComparisonBlock1344
public import KsIndexLean.AlphaMiddleRowComparisonBlock1376
public import KsIndexLean.AlphaMiddleRowComparisonBlock1408
public import KsIndexLean.AlphaMiddleRowComparisonBlock1440
public import KsIndexLean.AlphaMiddleRowComparisonBlock1472
public import KsIndexLean.AlphaMiddleRowComparisonBlock1504
public import KsIndexLean.AlphaMiddleRowComparisonBlock1536
public import KsIndexLean.AlphaMiddleRowComparisonBlock1568
public import KsIndexLean.AlphaMiddleRowComparisonBlock1600
public import KsIndexLean.AlphaMiddleRowComparisonBlock1632
public import KsIndexLean.AlphaMiddleRowComparisonBlock1664
public import KsIndexLean.AlphaMiddleRowComparisonBlock1696
public import KsIndexLean.AlphaMiddleRowComparisonBlock1728
public import KsIndexLean.AlphaMiddleRowComparisonBlock1760
public import KsIndexLean.AlphaMiddleRowComparisonBlock1792
public import KsIndexLean.AlphaMiddleRowComparisonBlock1824
public import KsIndexLean.AlphaMiddleRowComparisonBlock1856
public import KsIndexLean.AlphaMiddleRowComparisonBlock1888
public import KsIndexLean.AlphaMiddleRowComparisonBlock1920
public import KsIndexLean.AlphaMiddleRowComparisonBlock1952
public import KsIndexLean.AlphaMiddleRowComparisonBlock1984
public import KsIndexLean.AlphaMiddleRowComparisonBlock2016
public import KsIndexLean.AlphaMiddleArithmeticConsumer

@[expose] public section


/-! Optional assembly. The analytic moment bounds and raw-remainder identities
remain explicit premises. Numerical comparisons are kernel checked separately. -/
namespace KsIndex.AlphaRemarkTrial.MiddleComparisonAssembly
open CircleQ AlphaResidual MiddleInterval MiddleComparison
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def negative (b : Fin 64) (i : Fin (middleBlockLength b)) : Bool :=
  (middleBlockIndex ⟨b, i⟩).val % 2 != 0

def magnitude (b : Fin 64) (i : Fin (middleBlockLength b)) : ℕ :=
  (middleBlockIndex ⟨b, i⟩).val / 2 + 3

theorem magnitude_bounds (b : Fin 64) (i : Fin (middleBlockLength b)) :
    3 ≤ magnitude b i ∧ magnitude b i ≤ 1025 := by
  have h := (middleBlockIndex ⟨b, i⟩).isLt
  simp only [magnitude]
  omega

theorem mode_eq (b : Fin 64) (i : Fin (middleBlockLength b)) :
    rowMode (negative b i) (magnitude b i) = middleMode (middleBlockIndex ⟨b, i⟩) := by
  by_cases h : (middleBlockIndex ⟨b, i⟩).val % 2 = 0
  · simp [rowMode, negative, magnitude, middleMode, h]
  · simp [rowMode, negative, magnitude, middleMode, h]

theorem comparison (b : Fin 64) (i : Fin (middleBlockLength b)) :
    MiddleArithmeticConsumer.lo b i ≤
        rowLo (negative b i) (magnitude b i) (uLo (negative b i)) (uHi (negative b i)) ∧
    rowHi (negative b i) (magnitude b i) (uLo (negative b i)) (uHi (negative b i)) ≤
        MiddleArithmeticConsumer.hi b i := by
  fin_cases b
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock0.negative, MiddleComparisonBlock0.magnitude] using MiddleComparisonBlock0.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock32.negative, MiddleComparisonBlock32.magnitude] using MiddleComparisonBlock32.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock64.negative, MiddleComparisonBlock64.magnitude] using MiddleComparisonBlock64.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock96.negative, MiddleComparisonBlock96.magnitude] using MiddleComparisonBlock96.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock128.negative, MiddleComparisonBlock128.magnitude] using MiddleComparisonBlock128.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock160.negative, MiddleComparisonBlock160.magnitude] using MiddleComparisonBlock160.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock192.negative, MiddleComparisonBlock192.magnitude] using MiddleComparisonBlock192.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock224.negative, MiddleComparisonBlock224.magnitude] using MiddleComparisonBlock224.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock256.negative, MiddleComparisonBlock256.magnitude] using MiddleComparisonBlock256.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock288.negative, MiddleComparisonBlock288.magnitude] using MiddleComparisonBlock288.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock320.negative, MiddleComparisonBlock320.magnitude] using MiddleComparisonBlock320.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock352.negative, MiddleComparisonBlock352.magnitude] using MiddleComparisonBlock352.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock384.negative, MiddleComparisonBlock384.magnitude] using MiddleComparisonBlock384.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock416.negative, MiddleComparisonBlock416.magnitude] using MiddleComparisonBlock416.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock448.negative, MiddleComparisonBlock448.magnitude] using MiddleComparisonBlock448.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock480.negative, MiddleComparisonBlock480.magnitude] using MiddleComparisonBlock480.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock512.negative, MiddleComparisonBlock512.magnitude] using MiddleComparisonBlock512.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock544.negative, MiddleComparisonBlock544.magnitude] using MiddleComparisonBlock544.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock576.negative, MiddleComparisonBlock576.magnitude] using MiddleComparisonBlock576.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock608.negative, MiddleComparisonBlock608.magnitude] using MiddleComparisonBlock608.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock640.negative, MiddleComparisonBlock640.magnitude] using MiddleComparisonBlock640.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock672.negative, MiddleComparisonBlock672.magnitude] using MiddleComparisonBlock672.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock704.negative, MiddleComparisonBlock704.magnitude] using MiddleComparisonBlock704.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock736.negative, MiddleComparisonBlock736.magnitude] using MiddleComparisonBlock736.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock768.negative, MiddleComparisonBlock768.magnitude] using MiddleComparisonBlock768.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock800.negative, MiddleComparisonBlock800.magnitude] using MiddleComparisonBlock800.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock832.negative, MiddleComparisonBlock832.magnitude] using MiddleComparisonBlock832.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock864.negative, MiddleComparisonBlock864.magnitude] using MiddleComparisonBlock864.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock896.negative, MiddleComparisonBlock896.magnitude] using MiddleComparisonBlock896.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock928.negative, MiddleComparisonBlock928.magnitude] using MiddleComparisonBlock928.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock960.negative, MiddleComparisonBlock960.magnitude] using MiddleComparisonBlock960.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock992.negative, MiddleComparisonBlock992.magnitude] using MiddleComparisonBlock992.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1024.negative, MiddleComparisonBlock1024.magnitude] using MiddleComparisonBlock1024.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1056.negative, MiddleComparisonBlock1056.magnitude] using MiddleComparisonBlock1056.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1088.negative, MiddleComparisonBlock1088.magnitude] using MiddleComparisonBlock1088.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1120.negative, MiddleComparisonBlock1120.magnitude] using MiddleComparisonBlock1120.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1152.negative, MiddleComparisonBlock1152.magnitude] using MiddleComparisonBlock1152.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1184.negative, MiddleComparisonBlock1184.magnitude] using MiddleComparisonBlock1184.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1216.negative, MiddleComparisonBlock1216.magnitude] using MiddleComparisonBlock1216.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1248.negative, MiddleComparisonBlock1248.magnitude] using MiddleComparisonBlock1248.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1280.negative, MiddleComparisonBlock1280.magnitude] using MiddleComparisonBlock1280.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1312.negative, MiddleComparisonBlock1312.magnitude] using MiddleComparisonBlock1312.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1344.negative, MiddleComparisonBlock1344.magnitude] using MiddleComparisonBlock1344.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1376.negative, MiddleComparisonBlock1376.magnitude] using MiddleComparisonBlock1376.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1408.negative, MiddleComparisonBlock1408.magnitude] using MiddleComparisonBlock1408.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1440.negative, MiddleComparisonBlock1440.magnitude] using MiddleComparisonBlock1440.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1472.negative, MiddleComparisonBlock1472.magnitude] using MiddleComparisonBlock1472.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1504.negative, MiddleComparisonBlock1504.magnitude] using MiddleComparisonBlock1504.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1536.negative, MiddleComparisonBlock1536.magnitude] using MiddleComparisonBlock1536.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1568.negative, MiddleComparisonBlock1568.magnitude] using MiddleComparisonBlock1568.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1600.negative, MiddleComparisonBlock1600.magnitude] using MiddleComparisonBlock1600.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1632.negative, MiddleComparisonBlock1632.magnitude] using MiddleComparisonBlock1632.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1664.negative, MiddleComparisonBlock1664.magnitude] using MiddleComparisonBlock1664.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1696.negative, MiddleComparisonBlock1696.magnitude] using MiddleComparisonBlock1696.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1728.negative, MiddleComparisonBlock1728.magnitude] using MiddleComparisonBlock1728.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1760.negative, MiddleComparisonBlock1760.magnitude] using MiddleComparisonBlock1760.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1792.negative, MiddleComparisonBlock1792.magnitude] using MiddleComparisonBlock1792.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1824.negative, MiddleComparisonBlock1824.magnitude] using MiddleComparisonBlock1824.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1856.negative, MiddleComparisonBlock1856.magnitude] using MiddleComparisonBlock1856.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1888.negative, MiddleComparisonBlock1888.magnitude] using MiddleComparisonBlock1888.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1920.negative, MiddleComparisonBlock1920.magnitude] using MiddleComparisonBlock1920.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1952.negative, MiddleComparisonBlock1952.magnitude] using MiddleComparisonBlock1952.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock1984.negative, MiddleComparisonBlock1984.magnitude] using MiddleComparisonBlock1984.enclosure i
  · simpa [MiddleArithmeticConsumer.lo, MiddleArithmeticConsumer.hi, negative, magnitude, middleBlockIndex, MiddleComparisonBlock2016.negative, MiddleComparisonBlock2016.magnitude] using MiddleComparisonBlock2016.enclosure i

/-- Fully checked middle energy conditional only on the moment and raw-identity suppliers. -/
theorem middle_energy (U : Bool → ℝ)
    (hU : ∀ neg, (uLo neg : ℝ) ≤ U neg ∧ U neg ≤ (uHi neg : ℝ))
    (hidentity : ∀ neg (n : ℕ), 3 ≤ n → n ≤ 1025 →
      (if neg then rawRemainderNegative (n : ℝ) else rawRemainder (n : ℝ)) =
        remainderValue neg n (U neg)) :
    (∑ n ∈ residualWindow 1025 \ residualWindow 2,
      realResidual AlphaRemark.spectralUpper n ^ 2 / residualWeight n) ≤
        (6 / 10000000 : ℝ) := by
  apply MiddleArithmeticConsumer.middle_energy
  intro b i
  have hn := magnitude_bounds b i
  have h := actual_row_enclosed (negative b i) (magnitude b i) hn.1 hn.2
    (uLo (negative b i)) (uHi (negative b i)) (U (negative b i))
    (hU _) (hidentity _ _ hn.1 hn.2)
  rw [mode_eq] at h
  have hc := comparison b i
  exact ⟨((Rat.cast_le (K := ℝ)).2 hc.1).trans h.1,
    h.2.trans ((Rat.cast_le (K := ℝ)).2 hc.2)⟩

end KsIndex.AlphaRemarkTrial.MiddleComparisonAssembly
#print axioms KsIndex.AlphaRemarkTrial.MiddleComparisonAssembly.middle_energy
