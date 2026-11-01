module

public import KsIndexLean.AlphaLowProdAccessorFast

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (0,1), part 1. -/
namespace KsIndex.PositiveEnergyAlphaLowProd
theorem block01_8 : ∀ m : Fin 128, tFast 2161809 1 (1024 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (1024 + m.val))) * tFast 2161809 1 (1024 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (1024 + m.val) + 2)) := by decide +kernel
theorem block01_9 : ∀ m : Fin 128, tFast 2161809 1 (1152 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (1152 + m.val))) * tFast 2161809 1 (1152 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (1152 + m.val) + 2)) := by decide +kernel
theorem block01_10 : ∀ m : Fin 128, tFast 2161809 1 (1280 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (1280 + m.val))) * tFast 2161809 1 (1280 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (1280 + m.val) + 2)) := by decide +kernel
theorem block01_11 : ∀ m : Fin 128, tFast 2161809 1 (1408 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (1408 + m.val))) * tFast 2161809 1 (1408 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (1408 + m.val) + 2)) := by decide +kernel
theorem block01_12 : ∀ m : Fin 128, tFast 2161809 1 (1536 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (1536 + m.val))) * tFast 2161809 1 (1536 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (1536 + m.val) + 2)) := by decide +kernel
theorem block01_13 : ∀ m : Fin 128, tFast 2161809 1 (1664 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (1664 + m.val))) * tFast 2161809 1 (1664 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (1664 + m.val) + 2)) := by decide +kernel
theorem block01_14 : ∀ m : Fin 128, tFast 2161809 1 (1792 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (1792 + m.val))) * tFast 2161809 1 (1792 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (1792 + m.val) + 2)) := by decide +kernel
theorem block01_15 : ∀ m : Fin 128, tFast 2161809 1 (1920 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (1920 + m.val))) * tFast 2161809 1 (1920 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (1920 + m.val) + 2)) := by decide +kernel
end KsIndex.PositiveEnergyAlphaLowProd
