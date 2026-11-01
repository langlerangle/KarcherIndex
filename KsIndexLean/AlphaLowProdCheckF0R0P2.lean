module

public import KsIndexLean.AlphaLowProdAccessorFast

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (0,0), part 2. -/
namespace KsIndex.PositiveEnergyAlphaLowProd
theorem block00_16 : ∀ m : Fin 128, tFast 2161809 0 (2048 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (2048 + m.val))) * tFast 2161809 0 (2048 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (2048 + m.val) + 2)) := by decide +kernel
theorem block00_17 : ∀ m : Fin 128, tFast 2161809 0 (2176 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (2176 + m.val))) * tFast 2161809 0 (2176 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (2176 + m.val) + 2)) := by decide +kernel
theorem block00_18 : ∀ m : Fin 128, tFast 2161809 0 (2304 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (2304 + m.val))) * tFast 2161809 0 (2304 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (2304 + m.val) + 2)) := by decide +kernel
theorem block00_19 : ∀ m : Fin 128, tFast 2161809 0 (2432 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (2432 + m.val))) * tFast 2161809 0 (2432 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (2432 + m.val) + 2)) := by decide +kernel
theorem block00_20 : ∀ m : Fin 128, tFast 2161809 0 (2560 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (2560 + m.val))) * tFast 2161809 0 (2560 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (2560 + m.val) + 2)) := by decide +kernel
theorem block00_21 : ∀ m : Fin 128, tFast 2161809 0 (2688 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (2688 + m.val))) * tFast 2161809 0 (2688 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (2688 + m.val) + 2)) := by decide +kernel
theorem block00_22 : ∀ m : Fin 128, tFast 2161809 0 (2816 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (2816 + m.val))) * tFast 2161809 0 (2816 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (2816 + m.val) + 2)) := by decide +kernel
theorem block00_23 : ∀ m : Fin 128, tFast 2161809 0 (2944 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (2944 + m.val))) * tFast 2161809 0 (2944 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (2944 + m.val) + 2)) := by decide +kernel
end KsIndex.PositiveEnergyAlphaLowProd
