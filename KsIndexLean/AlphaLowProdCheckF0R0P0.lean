module

public import KsIndexLean.AlphaLowProdAccessorFast

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (0,0), part 0. -/
namespace KsIndex.PositiveEnergyAlphaLowProd
theorem block00_0 : ∀ m : Fin 128, tFast 2161809 0 (m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (m.val))) * tFast 2161809 0 (m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (m.val) + 2)) := by decide +kernel
theorem block00_1 : ∀ m : Fin 128, tFast 2161809 0 (128 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (128 + m.val))) * tFast 2161809 0 (128 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (128 + m.val) + 2)) := by decide +kernel
theorem block00_2 : ∀ m : Fin 128, tFast 2161809 0 (256 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (256 + m.val))) * tFast 2161809 0 (256 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (256 + m.val) + 2)) := by decide +kernel
theorem block00_3 : ∀ m : Fin 128, tFast 2161809 0 (384 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (384 + m.val))) * tFast 2161809 0 (384 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (384 + m.val) + 2)) := by decide +kernel
theorem block00_4 : ∀ m : Fin 128, tFast 2161809 0 (512 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (512 + m.val))) * tFast 2161809 0 (512 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (512 + m.val) + 2)) := by decide +kernel
theorem block00_5 : ∀ m : Fin 128, tFast 2161809 0 (640 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (640 + m.val))) * tFast 2161809 0 (640 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (640 + m.val) + 2)) := by decide +kernel
theorem block00_6 : ∀ m : Fin 128, tFast 2161809 0 (768 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (768 + m.val))) * tFast 2161809 0 (768 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (768 + m.val) + 2)) := by decide +kernel
theorem block00_7 : ∀ m : Fin 128, tFast 2161809 0 (896 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (896 + m.val))) * tFast 2161809 0 (896 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (896 + m.val) + 2)) := by decide +kernel
theorem zero00 : tFast 2161809 0 0 = 10 ^ 30 := by decide +kernel
end KsIndex.PositiveEnergyAlphaLowProd
