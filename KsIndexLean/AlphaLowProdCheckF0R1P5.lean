module

public import KsIndexLean.AlphaLowProdAccessorFast

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (0,1), part 5. -/
namespace KsIndex.PositiveEnergyAlphaLowProd
theorem block01_40 : ∀ m : Fin 128, tFast 2161809 1 (5120 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (5120 + m.val))) * tFast 2161809 1 (5120 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (5120 + m.val) + 2)) := by decide +kernel
theorem block01_41 : ∀ m : Fin 128, tFast 2161809 1 (5248 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (5248 + m.val))) * tFast 2161809 1 (5248 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (5248 + m.val) + 2)) := by decide +kernel
theorem block01_42 : ∀ m : Fin 128, tFast 2161809 1 (5376 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (5376 + m.val))) * tFast 2161809 1 (5376 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (5376 + m.val) + 2)) := by decide +kernel
theorem block01_43 : ∀ m : Fin 128, tFast 2161809 1 (5504 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (5504 + m.val))) * tFast 2161809 1 (5504 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (5504 + m.val) + 2)) := by decide +kernel
theorem block01_44 : ∀ m : Fin 128, tFast 2161809 1 (5632 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (5632 + m.val))) * tFast 2161809 1 (5632 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (5632 + m.val) + 2)) := by decide +kernel
theorem block01_45 : ∀ m : Fin 128, tFast 2161809 1 (5760 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (5760 + m.val))) * tFast 2161809 1 (5760 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (5760 + m.val) + 2)) := by decide +kernel
theorem block01_46 : ∀ m : Fin 128, tFast 2161809 1 (5888 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (5888 + m.val))) * tFast 2161809 1 (5888 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (5888 + m.val) + 2)) := by decide +kernel
theorem block01_47 : ∀ m : Fin 128, tFast 2161809 1 (6016 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (6016 + m.val))) * tFast 2161809 1 (6016 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (6016 + m.val) + 2)) := by decide +kernel
end KsIndex.PositiveEnergyAlphaLowProd
