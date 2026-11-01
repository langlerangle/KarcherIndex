module

public import KsIndexLean.AlphaLowProdAccessorFast

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (0,1), part 14. -/
namespace KsIndex.PositiveEnergyAlphaLowProd
theorem block01_112 : ∀ m : Fin 128, tFast 2161809 1 (14336 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (14336 + m.val))) * tFast 2161809 1 (14336 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (14336 + m.val) + 2)) := by decide +kernel
theorem block01_113 : ∀ m : Fin 128, tFast 2161809 1 (14464 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (14464 + m.val))) * tFast 2161809 1 (14464 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (14464 + m.val) + 2)) := by decide +kernel
theorem block01_114 : ∀ m : Fin 128, tFast 2161809 1 (14592 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (14592 + m.val))) * tFast 2161809 1 (14592 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (14592 + m.val) + 2)) := by decide +kernel
theorem block01_115 : ∀ m : Fin 128, tFast 2161809 1 (14720 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (14720 + m.val))) * tFast 2161809 1 (14720 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (14720 + m.val) + 2)) := by decide +kernel
theorem block01_116 : ∀ m : Fin 128, tFast 2161809 1 (14848 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (14848 + m.val))) * tFast 2161809 1 (14848 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (14848 + m.val) + 2)) := by decide +kernel
theorem block01_117 : ∀ m : Fin 128, tFast 2161809 1 (14976 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (14976 + m.val))) * tFast 2161809 1 (14976 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (14976 + m.val) + 2)) := by decide +kernel
theorem block01_118 : ∀ m : Fin 128, tFast 2161809 1 (15104 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (15104 + m.val))) * tFast 2161809 1 (15104 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (15104 + m.val) + 2)) := by decide +kernel
theorem block01_119 : ∀ m : Fin 128, tFast 2161809 1 (15232 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (15232 + m.val))) * tFast 2161809 1 (15232 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (15232 + m.val) + 2)) := by decide +kernel
end KsIndex.PositiveEnergyAlphaLowProd
