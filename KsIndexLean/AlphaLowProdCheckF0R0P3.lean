module

public import KsIndexLean.AlphaLowProdAccessorFast

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (0,0), part 3. -/
namespace KsIndex.PositiveEnergyAlphaLowProd
theorem block00_24 : ∀ m : Fin 128, tFast 2161809 0 (3072 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (3072 + m.val))) * tFast 2161809 0 (3072 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (3072 + m.val) + 2)) := by decide +kernel
theorem block00_25 : ∀ m : Fin 128, tFast 2161809 0 (3200 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (3200 + m.val))) * tFast 2161809 0 (3200 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (3200 + m.val) + 2)) := by decide +kernel
theorem block00_26 : ∀ m : Fin 128, tFast 2161809 0 (3328 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (3328 + m.val))) * tFast 2161809 0 (3328 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (3328 + m.val) + 2)) := by decide +kernel
theorem block00_27 : ∀ m : Fin 128, tFast 2161809 0 (3456 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (3456 + m.val))) * tFast 2161809 0 (3456 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (3456 + m.val) + 2)) := by decide +kernel
theorem block00_28 : ∀ m : Fin 128, tFast 2161809 0 (3584 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (3584 + m.val))) * tFast 2161809 0 (3584 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (3584 + m.val) + 2)) := by decide +kernel
theorem block00_29 : ∀ m : Fin 128, tFast 2161809 0 (3712 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (3712 + m.val))) * tFast 2161809 0 (3712 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (3712 + m.val) + 2)) := by decide +kernel
theorem block00_30 : ∀ m : Fin 128, tFast 2161809 0 (3840 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (3840 + m.val))) * tFast 2161809 0 (3840 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (3840 + m.val) + 2)) := by decide +kernel
theorem block00_31 : ∀ m : Fin 128, tFast 2161809 0 (3968 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (3968 + m.val))) * tFast 2161809 0 (3968 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (3968 + m.val) + 2)) := by decide +kernel
end KsIndex.PositiveEnergyAlphaLowProd
