module

public import KsIndexLean.AlphaLowProdAccessorFast

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (1,1), part 2. -/
namespace KsIndex.PositiveEnergyAlphaLowProd
theorem block11_16 : ∀ m : Fin 128, tFast 2838191 1 (2048 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (2048 + m.val))) * tFast 2838191 1 (2048 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (2048 + m.val) + 2)) := by decide +kernel
theorem block11_17 : ∀ m : Fin 128, tFast 2838191 1 (2176 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (2176 + m.val))) * tFast 2838191 1 (2176 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (2176 + m.val) + 2)) := by decide +kernel
theorem block11_18 : ∀ m : Fin 128, tFast 2838191 1 (2304 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (2304 + m.val))) * tFast 2838191 1 (2304 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (2304 + m.val) + 2)) := by decide +kernel
theorem block11_19 : ∀ m : Fin 128, tFast 2838191 1 (2432 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (2432 + m.val))) * tFast 2838191 1 (2432 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (2432 + m.val) + 2)) := by decide +kernel
theorem block11_20 : ∀ m : Fin 128, tFast 2838191 1 (2560 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (2560 + m.val))) * tFast 2838191 1 (2560 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (2560 + m.val) + 2)) := by decide +kernel
theorem block11_21 : ∀ m : Fin 128, tFast 2838191 1 (2688 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (2688 + m.val))) * tFast 2838191 1 (2688 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (2688 + m.val) + 2)) := by decide +kernel
theorem block11_22 : ∀ m : Fin 128, tFast 2838191 1 (2816 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (2816 + m.val))) * tFast 2838191 1 (2816 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (2816 + m.val) + 2)) := by decide +kernel
theorem block11_23 : ∀ m : Fin 128, tFast 2838191 1 (2944 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (2944 + m.val))) * tFast 2838191 1 (2944 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (2944 + m.val) + 2)) := by decide +kernel
end KsIndex.PositiveEnergyAlphaLowProd
