module

public import KsIndexLean.AlphaLowProdAccessorFast

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (0,1), part 15. -/
namespace KsIndex.PositiveEnergyAlphaLowProd
theorem block01_120 : ∀ m : Fin 128, tFast 2161809 1 (15360 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (15360 + m.val))) * tFast 2161809 1 (15360 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (15360 + m.val) + 2)) := by decide +kernel
theorem block01_121 : ∀ m : Fin 128, tFast 2161809 1 (15488 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (15488 + m.val))) * tFast 2161809 1 (15488 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (15488 + m.val) + 2)) := by decide +kernel
theorem block01_122 : ∀ m : Fin 128, tFast 2161809 1 (15616 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (15616 + m.val))) * tFast 2161809 1 (15616 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (15616 + m.val) + 2)) := by decide +kernel
theorem block01_123 : ∀ m : Fin 128, tFast 2161809 1 (15744 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (15744 + m.val))) * tFast 2161809 1 (15744 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (15744 + m.val) + 2)) := by decide +kernel
theorem block01_124 : ∀ m : Fin 128, tFast 2161809 1 (15872 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (15872 + m.val))) * tFast 2161809 1 (15872 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (15872 + m.val) + 2)) := by decide +kernel
theorem block01_125 : ∀ m : Fin 128, tFast 2161809 1 (16000 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (16000 + m.val))) * tFast 2161809 1 (16000 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (16000 + m.val) + 2)) := by decide +kernel
theorem block01_126 : ∀ m : Fin 128, tFast 2161809 1 (16128 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (16128 + m.val))) * tFast 2161809 1 (16128 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (16128 + m.val) + 2)) := by decide +kernel
theorem block01_127 : ∀ m : Fin 128, tFast 2161809 1 (16256 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (16256 + m.val))) * tFast 2161809 1 (16256 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (16256 + m.val) + 2)) := by decide +kernel
end KsIndex.PositiveEnergyAlphaLowProd
