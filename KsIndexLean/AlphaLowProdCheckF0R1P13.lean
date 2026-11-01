module

public import KsIndexLean.AlphaLowProdAccessorFast

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (0,1), part 13. -/
namespace KsIndex.PositiveEnergyAlphaLowProd
theorem block01_104 : ∀ m : Fin 128, tFast 2161809 1 (13312 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (13312 + m.val))) * tFast 2161809 1 (13312 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (13312 + m.val) + 2)) := by decide +kernel
theorem block01_105 : ∀ m : Fin 128, tFast 2161809 1 (13440 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (13440 + m.val))) * tFast 2161809 1 (13440 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (13440 + m.val) + 2)) := by decide +kernel
theorem block01_106 : ∀ m : Fin 128, tFast 2161809 1 (13568 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (13568 + m.val))) * tFast 2161809 1 (13568 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (13568 + m.val) + 2)) := by decide +kernel
theorem block01_107 : ∀ m : Fin 128, tFast 2161809 1 (13696 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (13696 + m.val))) * tFast 2161809 1 (13696 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (13696 + m.val) + 2)) := by decide +kernel
theorem block01_108 : ∀ m : Fin 128, tFast 2161809 1 (13824 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (13824 + m.val))) * tFast 2161809 1 (13824 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (13824 + m.val) + 2)) := by decide +kernel
theorem block01_109 : ∀ m : Fin 128, tFast 2161809 1 (13952 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (13952 + m.val))) * tFast 2161809 1 (13952 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (13952 + m.val) + 2)) := by decide +kernel
theorem block01_110 : ∀ m : Fin 128, tFast 2161809 1 (14080 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (14080 + m.val))) * tFast 2161809 1 (14080 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (14080 + m.val) + 2)) := by decide +kernel
theorem block01_111 : ∀ m : Fin 128, tFast 2161809 1 (14208 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (14208 + m.val))) * tFast 2161809 1 (14208 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (14208 + m.val) + 2)) := by decide +kernel
end KsIndex.PositiveEnergyAlphaLowProd
