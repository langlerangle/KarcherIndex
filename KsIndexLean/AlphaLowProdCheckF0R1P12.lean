module

public import KsIndexLean.AlphaLowProdAccessorFast

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (0,1), part 12. -/
namespace KsIndex.PositiveEnergyAlphaLowProd
theorem block01_96 : ∀ m : Fin 128, tFast 2161809 1 (12288 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (12288 + m.val))) * tFast 2161809 1 (12288 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (12288 + m.val) + 2)) := by decide +kernel
theorem block01_97 : ∀ m : Fin 128, tFast 2161809 1 (12416 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (12416 + m.val))) * tFast 2161809 1 (12416 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (12416 + m.val) + 2)) := by decide +kernel
theorem block01_98 : ∀ m : Fin 128, tFast 2161809 1 (12544 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (12544 + m.val))) * tFast 2161809 1 (12544 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (12544 + m.val) + 2)) := by decide +kernel
theorem block01_99 : ∀ m : Fin 128, tFast 2161809 1 (12672 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (12672 + m.val))) * tFast 2161809 1 (12672 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (12672 + m.val) + 2)) := by decide +kernel
theorem block01_100 : ∀ m : Fin 128, tFast 2161809 1 (12800 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (12800 + m.val))) * tFast 2161809 1 (12800 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (12800 + m.val) + 2)) := by decide +kernel
theorem block01_101 : ∀ m : Fin 128, tFast 2161809 1 (12928 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (12928 + m.val))) * tFast 2161809 1 (12928 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (12928 + m.val) + 2)) := by decide +kernel
theorem block01_102 : ∀ m : Fin 128, tFast 2161809 1 (13056 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (13056 + m.val))) * tFast 2161809 1 (13056 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (13056 + m.val) + 2)) := by decide +kernel
theorem block01_103 : ∀ m : Fin 128, tFast 2161809 1 (13184 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (13184 + m.val))) * tFast 2161809 1 (13184 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (13184 + m.val) + 2)) := by decide +kernel
end KsIndex.PositiveEnergyAlphaLowProd
