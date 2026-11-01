module

public import KsIndexLean.AlphaLowProdAccessorFast

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (0,1), part 9. -/
namespace KsIndex.PositiveEnergyAlphaLowProd
theorem block01_72 : ∀ m : Fin 128, tFast 2161809 1 (9216 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (9216 + m.val))) * tFast 2161809 1 (9216 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (9216 + m.val) + 2)) := by decide +kernel
theorem block01_73 : ∀ m : Fin 128, tFast 2161809 1 (9344 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (9344 + m.val))) * tFast 2161809 1 (9344 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (9344 + m.val) + 2)) := by decide +kernel
theorem block01_74 : ∀ m : Fin 128, tFast 2161809 1 (9472 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (9472 + m.val))) * tFast 2161809 1 (9472 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (9472 + m.val) + 2)) := by decide +kernel
theorem block01_75 : ∀ m : Fin 128, tFast 2161809 1 (9600 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (9600 + m.val))) * tFast 2161809 1 (9600 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (9600 + m.val) + 2)) := by decide +kernel
theorem block01_76 : ∀ m : Fin 128, tFast 2161809 1 (9728 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (9728 + m.val))) * tFast 2161809 1 (9728 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (9728 + m.val) + 2)) := by decide +kernel
theorem block01_77 : ∀ m : Fin 128, tFast 2161809 1 (9856 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (9856 + m.val))) * tFast 2161809 1 (9856 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (9856 + m.val) + 2)) := by decide +kernel
theorem block01_78 : ∀ m : Fin 128, tFast 2161809 1 (9984 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (9984 + m.val))) * tFast 2161809 1 (9984 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (9984 + m.val) + 2)) := by decide +kernel
theorem block01_79 : ∀ m : Fin 128, tFast 2161809 1 (10112 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (10112 + m.val))) * tFast 2161809 1 (10112 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (10112 + m.val) + 2)) := by decide +kernel
end KsIndex.PositiveEnergyAlphaLowProd
