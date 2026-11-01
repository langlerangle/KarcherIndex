module

public import KsIndexLean.AlphaMiddleArithmeticTotal
public import KsIndexLean.AlphaMiddleWindowIndex

@[expose] public section


/-! Optional consumer of the already verified arithmetic blocks. Actual residual
row enclosures remain explicit hypotheses; this is not an unconditional bound. -/
namespace KsIndex.AlphaRemarkTrial.MiddleArithmeticConsumer
open CircleQ AlphaResidual
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def lo (b : Fin 64) : Fin (middleBlockLength b) → ℚ :=
  match b with
  | ⟨0, _⟩ => MiddleBlock0.lo
  | ⟨1, _⟩ => MiddleBlock32.lo
  | ⟨2, _⟩ => MiddleBlock64.lo
  | ⟨3, _⟩ => MiddleBlock96.lo
  | ⟨4, _⟩ => MiddleBlock128.lo
  | ⟨5, _⟩ => MiddleBlock160.lo
  | ⟨6, _⟩ => MiddleBlock192.lo
  | ⟨7, _⟩ => MiddleBlock224.lo
  | ⟨8, _⟩ => MiddleBlock256.lo
  | ⟨9, _⟩ => MiddleBlock288.lo
  | ⟨10, _⟩ => MiddleBlock320.lo
  | ⟨11, _⟩ => MiddleBlock352.lo
  | ⟨12, _⟩ => MiddleBlock384.lo
  | ⟨13, _⟩ => MiddleBlock416.lo
  | ⟨14, _⟩ => MiddleBlock448.lo
  | ⟨15, _⟩ => MiddleBlock480.lo
  | ⟨16, _⟩ => MiddleBlock512.lo
  | ⟨17, _⟩ => MiddleBlock544.lo
  | ⟨18, _⟩ => MiddleBlock576.lo
  | ⟨19, _⟩ => MiddleBlock608.lo
  | ⟨20, _⟩ => MiddleBlock640.lo
  | ⟨21, _⟩ => MiddleBlock672.lo
  | ⟨22, _⟩ => MiddleBlock704.lo
  | ⟨23, _⟩ => MiddleBlock736.lo
  | ⟨24, _⟩ => MiddleBlock768.lo
  | ⟨25, _⟩ => MiddleBlock800.lo
  | ⟨26, _⟩ => MiddleBlock832.lo
  | ⟨27, _⟩ => MiddleBlock864.lo
  | ⟨28, _⟩ => MiddleBlock896.lo
  | ⟨29, _⟩ => MiddleBlock928.lo
  | ⟨30, _⟩ => MiddleBlock960.lo
  | ⟨31, _⟩ => MiddleBlock992.lo
  | ⟨32, _⟩ => MiddleBlock1024.lo
  | ⟨33, _⟩ => MiddleBlock1056.lo
  | ⟨34, _⟩ => MiddleBlock1088.lo
  | ⟨35, _⟩ => MiddleBlock1120.lo
  | ⟨36, _⟩ => MiddleBlock1152.lo
  | ⟨37, _⟩ => MiddleBlock1184.lo
  | ⟨38, _⟩ => MiddleBlock1216.lo
  | ⟨39, _⟩ => MiddleBlock1248.lo
  | ⟨40, _⟩ => MiddleBlock1280.lo
  | ⟨41, _⟩ => MiddleBlock1312.lo
  | ⟨42, _⟩ => MiddleBlock1344.lo
  | ⟨43, _⟩ => MiddleBlock1376.lo
  | ⟨44, _⟩ => MiddleBlock1408.lo
  | ⟨45, _⟩ => MiddleBlock1440.lo
  | ⟨46, _⟩ => MiddleBlock1472.lo
  | ⟨47, _⟩ => MiddleBlock1504.lo
  | ⟨48, _⟩ => MiddleBlock1536.lo
  | ⟨49, _⟩ => MiddleBlock1568.lo
  | ⟨50, _⟩ => MiddleBlock1600.lo
  | ⟨51, _⟩ => MiddleBlock1632.lo
  | ⟨52, _⟩ => MiddleBlock1664.lo
  | ⟨53, _⟩ => MiddleBlock1696.lo
  | ⟨54, _⟩ => MiddleBlock1728.lo
  | ⟨55, _⟩ => MiddleBlock1760.lo
  | ⟨56, _⟩ => MiddleBlock1792.lo
  | ⟨57, _⟩ => MiddleBlock1824.lo
  | ⟨58, _⟩ => MiddleBlock1856.lo
  | ⟨59, _⟩ => MiddleBlock1888.lo
  | ⟨60, _⟩ => MiddleBlock1920.lo
  | ⟨61, _⟩ => MiddleBlock1952.lo
  | ⟨62, _⟩ => MiddleBlock1984.lo
  | ⟨63, _⟩ => MiddleBlock2016.lo
  | ⟨n + 64, h⟩ => False.elim (by omega)

def hi (b : Fin 64) : Fin (middleBlockLength b) → ℚ :=
  match b with
  | ⟨0, _⟩ => MiddleBlock0.hi
  | ⟨1, _⟩ => MiddleBlock32.hi
  | ⟨2, _⟩ => MiddleBlock64.hi
  | ⟨3, _⟩ => MiddleBlock96.hi
  | ⟨4, _⟩ => MiddleBlock128.hi
  | ⟨5, _⟩ => MiddleBlock160.hi
  | ⟨6, _⟩ => MiddleBlock192.hi
  | ⟨7, _⟩ => MiddleBlock224.hi
  | ⟨8, _⟩ => MiddleBlock256.hi
  | ⟨9, _⟩ => MiddleBlock288.hi
  | ⟨10, _⟩ => MiddleBlock320.hi
  | ⟨11, _⟩ => MiddleBlock352.hi
  | ⟨12, _⟩ => MiddleBlock384.hi
  | ⟨13, _⟩ => MiddleBlock416.hi
  | ⟨14, _⟩ => MiddleBlock448.hi
  | ⟨15, _⟩ => MiddleBlock480.hi
  | ⟨16, _⟩ => MiddleBlock512.hi
  | ⟨17, _⟩ => MiddleBlock544.hi
  | ⟨18, _⟩ => MiddleBlock576.hi
  | ⟨19, _⟩ => MiddleBlock608.hi
  | ⟨20, _⟩ => MiddleBlock640.hi
  | ⟨21, _⟩ => MiddleBlock672.hi
  | ⟨22, _⟩ => MiddleBlock704.hi
  | ⟨23, _⟩ => MiddleBlock736.hi
  | ⟨24, _⟩ => MiddleBlock768.hi
  | ⟨25, _⟩ => MiddleBlock800.hi
  | ⟨26, _⟩ => MiddleBlock832.hi
  | ⟨27, _⟩ => MiddleBlock864.hi
  | ⟨28, _⟩ => MiddleBlock896.hi
  | ⟨29, _⟩ => MiddleBlock928.hi
  | ⟨30, _⟩ => MiddleBlock960.hi
  | ⟨31, _⟩ => MiddleBlock992.hi
  | ⟨32, _⟩ => MiddleBlock1024.hi
  | ⟨33, _⟩ => MiddleBlock1056.hi
  | ⟨34, _⟩ => MiddleBlock1088.hi
  | ⟨35, _⟩ => MiddleBlock1120.hi
  | ⟨36, _⟩ => MiddleBlock1152.hi
  | ⟨37, _⟩ => MiddleBlock1184.hi
  | ⟨38, _⟩ => MiddleBlock1216.hi
  | ⟨39, _⟩ => MiddleBlock1248.hi
  | ⟨40, _⟩ => MiddleBlock1280.hi
  | ⟨41, _⟩ => MiddleBlock1312.hi
  | ⟨42, _⟩ => MiddleBlock1344.hi
  | ⟨43, _⟩ => MiddleBlock1376.hi
  | ⟨44, _⟩ => MiddleBlock1408.hi
  | ⟨45, _⟩ => MiddleBlock1440.hi
  | ⟨46, _⟩ => MiddleBlock1472.hi
  | ⟨47, _⟩ => MiddleBlock1504.hi
  | ⟨48, _⟩ => MiddleBlock1536.hi
  | ⟨49, _⟩ => MiddleBlock1568.hi
  | ⟨50, _⟩ => MiddleBlock1600.hi
  | ⟨51, _⟩ => MiddleBlock1632.hi
  | ⟨52, _⟩ => MiddleBlock1664.hi
  | ⟨53, _⟩ => MiddleBlock1696.hi
  | ⟨54, _⟩ => MiddleBlock1728.hi
  | ⟨55, _⟩ => MiddleBlock1760.hi
  | ⟨56, _⟩ => MiddleBlock1792.hi
  | ⟨57, _⟩ => MiddleBlock1824.hi
  | ⟨58, _⟩ => MiddleBlock1856.hi
  | ⟨59, _⟩ => MiddleBlock1888.hi
  | ⟨60, _⟩ => MiddleBlock1920.hi
  | ⟨61, _⟩ => MiddleBlock1952.hi
  | ⟨62, _⟩ => MiddleBlock1984.hi
  | ⟨63, _⟩ => MiddleBlock2016.hi
  | ⟨n + 64, h⟩ => False.elim (by omega)

def energy (b : Fin 64) : Fin (middleBlockLength b) → ℚ :=
  match b with
  | ⟨0, _⟩ => MiddleBlock0.energy
  | ⟨1, _⟩ => MiddleBlock32.energy
  | ⟨2, _⟩ => MiddleBlock64.energy
  | ⟨3, _⟩ => MiddleBlock96.energy
  | ⟨4, _⟩ => MiddleBlock128.energy
  | ⟨5, _⟩ => MiddleBlock160.energy
  | ⟨6, _⟩ => MiddleBlock192.energy
  | ⟨7, _⟩ => MiddleBlock224.energy
  | ⟨8, _⟩ => MiddleBlock256.energy
  | ⟨9, _⟩ => MiddleBlock288.energy
  | ⟨10, _⟩ => MiddleBlock320.energy
  | ⟨11, _⟩ => MiddleBlock352.energy
  | ⟨12, _⟩ => MiddleBlock384.energy
  | ⟨13, _⟩ => MiddleBlock416.energy
  | ⟨14, _⟩ => MiddleBlock448.energy
  | ⟨15, _⟩ => MiddleBlock480.energy
  | ⟨16, _⟩ => MiddleBlock512.energy
  | ⟨17, _⟩ => MiddleBlock544.energy
  | ⟨18, _⟩ => MiddleBlock576.energy
  | ⟨19, _⟩ => MiddleBlock608.energy
  | ⟨20, _⟩ => MiddleBlock640.energy
  | ⟨21, _⟩ => MiddleBlock672.energy
  | ⟨22, _⟩ => MiddleBlock704.energy
  | ⟨23, _⟩ => MiddleBlock736.energy
  | ⟨24, _⟩ => MiddleBlock768.energy
  | ⟨25, _⟩ => MiddleBlock800.energy
  | ⟨26, _⟩ => MiddleBlock832.energy
  | ⟨27, _⟩ => MiddleBlock864.energy
  | ⟨28, _⟩ => MiddleBlock896.energy
  | ⟨29, _⟩ => MiddleBlock928.energy
  | ⟨30, _⟩ => MiddleBlock960.energy
  | ⟨31, _⟩ => MiddleBlock992.energy
  | ⟨32, _⟩ => MiddleBlock1024.energy
  | ⟨33, _⟩ => MiddleBlock1056.energy
  | ⟨34, _⟩ => MiddleBlock1088.energy
  | ⟨35, _⟩ => MiddleBlock1120.energy
  | ⟨36, _⟩ => MiddleBlock1152.energy
  | ⟨37, _⟩ => MiddleBlock1184.energy
  | ⟨38, _⟩ => MiddleBlock1216.energy
  | ⟨39, _⟩ => MiddleBlock1248.energy
  | ⟨40, _⟩ => MiddleBlock1280.energy
  | ⟨41, _⟩ => MiddleBlock1312.energy
  | ⟨42, _⟩ => MiddleBlock1344.energy
  | ⟨43, _⟩ => MiddleBlock1376.energy
  | ⟨44, _⟩ => MiddleBlock1408.energy
  | ⟨45, _⟩ => MiddleBlock1440.energy
  | ⟨46, _⟩ => MiddleBlock1472.energy
  | ⟨47, _⟩ => MiddleBlock1504.energy
  | ⟨48, _⟩ => MiddleBlock1536.energy
  | ⟨49, _⟩ => MiddleBlock1568.energy
  | ⟨50, _⟩ => MiddleBlock1600.energy
  | ⟨51, _⟩ => MiddleBlock1632.energy
  | ⟨52, _⟩ => MiddleBlock1664.energy
  | ⟨53, _⟩ => MiddleBlock1696.energy
  | ⟨54, _⟩ => MiddleBlock1728.energy
  | ⟨55, _⟩ => MiddleBlock1760.energy
  | ⟨56, _⟩ => MiddleBlock1792.energy
  | ⟨57, _⟩ => MiddleBlock1824.energy
  | ⟨58, _⟩ => MiddleBlock1856.energy
  | ⟨59, _⟩ => MiddleBlock1888.energy
  | ⟨60, _⟩ => MiddleBlock1920.energy
  | ⟨61, _⟩ => MiddleBlock1952.energy
  | ⟨62, _⟩ => MiddleBlock1984.energy
  | ⟨63, _⟩ => MiddleBlock2016.energy
  | ⟨n + 64, h⟩ => False.elim (by omega)

theorem row_arithmetic (b : Fin 64) (i : Fin (middleBlockLength b)) :
    signedIntervalRadius (lo b i) (hi b i)^2 /
      residualWeightRat (middleMode (middleBlockIndex ⟨b, i⟩)) ≤ energy b i := by
  fin_cases b
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock0.mode] using (MiddleBlock0.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock32.mode] using (MiddleBlock32.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock64.mode] using (MiddleBlock64.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock96.mode] using (MiddleBlock96.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock128.mode] using (MiddleBlock128.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock160.mode] using (MiddleBlock160.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock192.mode] using (MiddleBlock192.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock224.mode] using (MiddleBlock224.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock256.mode] using (MiddleBlock256.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock288.mode] using (MiddleBlock288.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock320.mode] using (MiddleBlock320.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock352.mode] using (MiddleBlock352.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock384.mode] using (MiddleBlock384.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock416.mode] using (MiddleBlock416.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock448.mode] using (MiddleBlock448.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock480.mode] using (MiddleBlock480.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock512.mode] using (MiddleBlock512.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock544.mode] using (MiddleBlock544.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock576.mode] using (MiddleBlock576.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock608.mode] using (MiddleBlock608.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock640.mode] using (MiddleBlock640.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock672.mode] using (MiddleBlock672.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock704.mode] using (MiddleBlock704.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock736.mode] using (MiddleBlock736.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock768.mode] using (MiddleBlock768.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock800.mode] using (MiddleBlock800.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock832.mode] using (MiddleBlock832.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock864.mode] using (MiddleBlock864.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock896.mode] using (MiddleBlock896.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock928.mode] using (MiddleBlock928.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock960.mode] using (MiddleBlock960.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock992.mode] using (MiddleBlock992.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1024.mode] using (MiddleBlock1024.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1056.mode] using (MiddleBlock1056.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1088.mode] using (MiddleBlock1088.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1120.mode] using (MiddleBlock1120.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1152.mode] using (MiddleBlock1152.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1184.mode] using (MiddleBlock1184.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1216.mode] using (MiddleBlock1216.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1248.mode] using (MiddleBlock1248.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1280.mode] using (MiddleBlock1280.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1312.mode] using (MiddleBlock1312.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1344.mode] using (MiddleBlock1344.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1376.mode] using (MiddleBlock1376.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1408.mode] using (MiddleBlock1408.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1440.mode] using (MiddleBlock1440.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1472.mode] using (MiddleBlock1472.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1504.mode] using (MiddleBlock1504.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1536.mode] using (MiddleBlock1536.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1568.mode] using (MiddleBlock1568.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1600.mode] using (MiddleBlock1600.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1632.mode] using (MiddleBlock1632.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1664.mode] using (MiddleBlock1664.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1696.mode] using (MiddleBlock1696.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1728.mode] using (MiddleBlock1728.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1760.mode] using (MiddleBlock1760.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1792.mode] using (MiddleBlock1792.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1824.mode] using (MiddleBlock1824.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1856.mode] using (MiddleBlock1856.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1888.mode] using (MiddleBlock1888.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1920.mode] using (MiddleBlock1920.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1952.mode] using (MiddleBlock1952.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock1984.mode] using (MiddleBlock1984.arithmetic i).2
  · simpa [lo, hi, energy, middleMode, middleBlockIndex, MiddleBlock2016.mode] using (MiddleBlock2016.arithmetic i).2

theorem block_energy (b : Fin 64) :
    (∑ i, energy b i) = MiddleArithmeticTotal.blockEnergy b := by
  fin_cases b <;> rfl

theorem middle_energy
    (hencloses : ∀ (b : Fin 64) (i : Fin (middleBlockLength b)),
      (lo b i : ℝ) ≤ realResidual AlphaRemark.spectralUpper
        (middleMode (middleBlockIndex ⟨b, i⟩)) ∧
      realResidual AlphaRemark.spectralUpper (middleMode (middleBlockIndex ⟨b, i⟩))
        ≤ (hi b i : ℝ)) :
    (∑ n ∈ residualWindow 1025 \ residualWindow 2,
      realResidual AlphaRemark.spectralUpper n ^ 2 / residualWeight n)
        ≤ (6/10000000 : ℝ) := by
  rw [middleWindow_sum, middleBlock_sum]
  have hrow (b : Fin 64) (i : Fin (middleBlockLength b)) :
      realResidual AlphaRemark.spectralUpper (middleMode (middleBlockIndex ⟨b, i⟩)) ^ 2 /
        residualWeight (middleMode (middleBlockIndex ⟨b, i⟩)) ≤ (energy b i : ℝ) := by
    have habs := signedIntervalRadius_bounds (lo b i) (hi b i) _
      (hencloses b i).1 (hencloses b i).2
    have hnonneg : (0 : ℝ) ≤ signedIntervalRadius (lo b i) (hi b i) :=
      (abs_nonneg _).trans habs
    have hs := (sq_le_sq₀ (abs_nonneg _) hnonneg).mpr habs
    rw [sq_abs] at hs
    have hr : (signedIntervalRadius (lo b i) (hi b i) : ℝ)^2 /
        residualWeight (middleMode (middleBlockIndex ⟨b, i⟩)) ≤ (energy b i : ℝ) := by
      rw [← residualWeightRat_cast]
      exact_mod_cast row_arithmetic b i
    exact (div_le_div_of_nonneg_right hs (residualWeight_pos _).le).trans hr
  have hsum : (∑ b : Fin 64, ∑ i : Fin (middleBlockLength b), energy b i) ≤
      (6/10000000 : ℚ) := by
    simp_rw [block_energy]
    exact MiddleArithmeticTotal.budget
  calc
    _ ≤ ∑ b : Fin 64, ∑ i : Fin (middleBlockLength b), (energy b i : ℝ) :=
      Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun i _ => hrow b i))
    _ = ((∑ b : Fin 64, ∑ i : Fin (middleBlockLength b), energy b i : ℚ) : ℝ) := by simp
    _ ≤ _ := by
      have h := (Rat.cast_le (K := ℝ)).2 hsum
      simpa only [Rat.cast_div, Rat.cast_ofNat] using h

end KsIndex.AlphaRemarkTrial.MiddleArithmeticConsumer
#print axioms KsIndex.AlphaRemarkTrial.MiddleArithmeticConsumer.middle_energy
