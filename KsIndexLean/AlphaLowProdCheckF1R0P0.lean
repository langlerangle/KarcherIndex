module

public import KsIndexLean.AlphaLowProdAccessorFast

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (1,0), part 0. -/
namespace KsIndex.PositiveEnergyAlphaLowProd
theorem block10_0 : ∀ m : Fin 128, tFast 2838191 0 (m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (m.val))) * tFast 2838191 0 (m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (m.val) + 2)) := by decide +kernel
theorem block10_1 : ∀ m : Fin 128, tFast 2838191 0 (128 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (128 + m.val))) * tFast 2838191 0 (128 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (128 + m.val) + 2)) := by decide +kernel
theorem block10_2 : ∀ m : Fin 128, tFast 2838191 0 (256 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (256 + m.val))) * tFast 2838191 0 (256 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (256 + m.val) + 2)) := by decide +kernel
theorem block10_3 : ∀ m : Fin 128, tFast 2838191 0 (384 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (384 + m.val))) * tFast 2838191 0 (384 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (384 + m.val) + 2)) := by decide +kernel
theorem block10_4 : ∀ m : Fin 128, tFast 2838191 0 (512 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (512 + m.val))) * tFast 2838191 0 (512 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (512 + m.val) + 2)) := by decide +kernel
theorem block10_5 : ∀ m : Fin 128, tFast 2838191 0 (640 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (640 + m.val))) * tFast 2838191 0 (640 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (640 + m.val) + 2)) := by decide +kernel
theorem block10_6 : ∀ m : Fin 128, tFast 2838191 0 (768 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (768 + m.val))) * tFast 2838191 0 (768 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (768 + m.val) + 2)) := by decide +kernel
theorem block10_7 : ∀ m : Fin 128, tFast 2838191 0 (896 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (896 + m.val))) * tFast 2838191 0 (896 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (896 + m.val) + 2)) := by decide +kernel
theorem zero10 : tFast 2838191 0 0 = 10 ^ 30 := by decide +kernel
end KsIndex.PositiveEnergyAlphaLowProd
