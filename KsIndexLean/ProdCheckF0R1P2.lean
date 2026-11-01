module

public import KsIndexLean.ProdAccessor

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (0,1), part 2. -/
namespace KsIndex.NegSignProd
theorem block01_16 : ∀ m : Fin 128, t 2161809 1 (2048 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (2048 + m.val))) * t 2161809 1 (2048 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (2048 + m.val) + 2)) := by decide +kernel
theorem block01_17 : ∀ m : Fin 128, t 2161809 1 (2176 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (2176 + m.val))) * t 2161809 1 (2176 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (2176 + m.val) + 2)) := by decide +kernel
theorem block01_18 : ∀ m : Fin 128, t 2161809 1 (2304 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (2304 + m.val))) * t 2161809 1 (2304 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (2304 + m.val) + 2)) := by decide +kernel
theorem block01_19 : ∀ m : Fin 128, t 2161809 1 (2432 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (2432 + m.val))) * t 2161809 1 (2432 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (2432 + m.val) + 2)) := by decide +kernel
theorem block01_20 : ∀ m : Fin 128, t 2161809 1 (2560 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (2560 + m.val))) * t 2161809 1 (2560 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (2560 + m.val) + 2)) := by decide +kernel
theorem block01_21 : ∀ m : Fin 128, t 2161809 1 (2688 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (2688 + m.val))) * t 2161809 1 (2688 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (2688 + m.val) + 2)) := by decide +kernel
theorem block01_22 : ∀ m : Fin 128, t 2161809 1 (2816 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (2816 + m.val))) * t 2161809 1 (2816 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (2816 + m.val) + 2)) := by decide +kernel
theorem block01_23 : ∀ m : Fin 128, t 2161809 1 (2944 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (2944 + m.val))) * t 2161809 1 (2944 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (2944 + m.val) + 2)) := by decide +kernel
end KsIndex.NegSignProd
