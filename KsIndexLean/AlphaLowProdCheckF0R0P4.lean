module

public import KsIndexLean.AlphaLowProdAccessorFast

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (0,0), part 4. -/
namespace KsIndex.PositiveEnergyAlphaLowProd
theorem block00_32 : ∀ m : Fin 128, tFast 2161809 0 (4096 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (4096 + m.val))) * tFast 2161809 0 (4096 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (4096 + m.val) + 2)) := by decide +kernel
theorem block00_33 : ∀ m : Fin 128, tFast 2161809 0 (4224 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (4224 + m.val))) * tFast 2161809 0 (4224 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (4224 + m.val) + 2)) := by decide +kernel
theorem block00_34 : ∀ m : Fin 128, tFast 2161809 0 (4352 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (4352 + m.val))) * tFast 2161809 0 (4352 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (4352 + m.val) + 2)) := by decide +kernel
theorem block00_35 : ∀ m : Fin 128, tFast 2161809 0 (4480 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (4480 + m.val))) * tFast 2161809 0 (4480 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (4480 + m.val) + 2)) := by decide +kernel
theorem block00_36 : ∀ m : Fin 128, tFast 2161809 0 (4608 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (4608 + m.val))) * tFast 2161809 0 (4608 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (4608 + m.val) + 2)) := by decide +kernel
theorem block00_37 : ∀ m : Fin 128, tFast 2161809 0 (4736 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (4736 + m.val))) * tFast 2161809 0 (4736 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (4736 + m.val) + 2)) := by decide +kernel
theorem block00_38 : ∀ m : Fin 128, tFast 2161809 0 (4864 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (4864 + m.val))) * tFast 2161809 0 (4864 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (4864 + m.val) + 2)) := by decide +kernel
theorem block00_39 : ∀ m : Fin 128, tFast 2161809 0 (4992 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (4992 + m.val))) * tFast 2161809 0 (4992 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (4992 + m.val) + 2)) := by decide +kernel
end KsIndex.PositiveEnergyAlphaLowProd
