module

public import KsIndexLean.AlphaLowProdAccessorFast

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (0,1), part 10. -/
namespace KsIndex.PositiveEnergyAlphaLowProd
theorem block01_80 : ∀ m : Fin 128, tFast 2161809 1 (10240 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (10240 + m.val))) * tFast 2161809 1 (10240 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (10240 + m.val) + 2)) := by decide +kernel
theorem block01_81 : ∀ m : Fin 128, tFast 2161809 1 (10368 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (10368 + m.val))) * tFast 2161809 1 (10368 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (10368 + m.val) + 2)) := by decide +kernel
theorem block01_82 : ∀ m : Fin 128, tFast 2161809 1 (10496 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (10496 + m.val))) * tFast 2161809 1 (10496 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (10496 + m.val) + 2)) := by decide +kernel
theorem block01_83 : ∀ m : Fin 128, tFast 2161809 1 (10624 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (10624 + m.val))) * tFast 2161809 1 (10624 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (10624 + m.val) + 2)) := by decide +kernel
theorem block01_84 : ∀ m : Fin 128, tFast 2161809 1 (10752 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (10752 + m.val))) * tFast 2161809 1 (10752 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (10752 + m.val) + 2)) := by decide +kernel
theorem block01_85 : ∀ m : Fin 128, tFast 2161809 1 (10880 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (10880 + m.val))) * tFast 2161809 1 (10880 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (10880 + m.val) + 2)) := by decide +kernel
theorem block01_86 : ∀ m : Fin 128, tFast 2161809 1 (11008 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (11008 + m.val))) * tFast 2161809 1 (11008 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (11008 + m.val) + 2)) := by decide +kernel
theorem block01_87 : ∀ m : Fin 128, tFast 2161809 1 (11136 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (11136 + m.val))) * tFast 2161809 1 (11136 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (11136 + m.val) + 2)) := by decide +kernel
end KsIndex.PositiveEnergyAlphaLowProd
