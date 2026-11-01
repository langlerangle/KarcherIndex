module

public import KsIndexLean.AlphaLowProdAccessorFast

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (0,1), part 3. -/
namespace KsIndex.PositiveEnergyAlphaLowProd
theorem block01_24 : ∀ m : Fin 128, tFast 2161809 1 (3072 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (3072 + m.val))) * tFast 2161809 1 (3072 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (3072 + m.val) + 2)) := by decide +kernel
theorem block01_25 : ∀ m : Fin 128, tFast 2161809 1 (3200 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (3200 + m.val))) * tFast 2161809 1 (3200 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (3200 + m.val) + 2)) := by decide +kernel
theorem block01_26 : ∀ m : Fin 128, tFast 2161809 1 (3328 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (3328 + m.val))) * tFast 2161809 1 (3328 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (3328 + m.val) + 2)) := by decide +kernel
theorem block01_27 : ∀ m : Fin 128, tFast 2161809 1 (3456 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (3456 + m.val))) * tFast 2161809 1 (3456 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (3456 + m.val) + 2)) := by decide +kernel
theorem block01_28 : ∀ m : Fin 128, tFast 2161809 1 (3584 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (3584 + m.val))) * tFast 2161809 1 (3584 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (3584 + m.val) + 2)) := by decide +kernel
theorem block01_29 : ∀ m : Fin 128, tFast 2161809 1 (3712 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (3712 + m.val))) * tFast 2161809 1 (3712 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (3712 + m.val) + 2)) := by decide +kernel
theorem block01_30 : ∀ m : Fin 128, tFast 2161809 1 (3840 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (3840 + m.val))) * tFast 2161809 1 (3840 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (3840 + m.val) + 2)) := by decide +kernel
theorem block01_31 : ∀ m : Fin 128, tFast 2161809 1 (3968 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (3968 + m.val))) * tFast 2161809 1 (3968 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (3968 + m.val) + 2)) := by decide +kernel
end KsIndex.PositiveEnergyAlphaLowProd
