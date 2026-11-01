module

public import KsIndexLean.AlphaLowProdAccessorFast

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (1,0), part 12. -/
namespace KsIndex.PositiveEnergyAlphaLowProd
theorem block10_96 : ∀ m : Fin 128, tFast 2838191 0 (12288 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (12288 + m.val))) * tFast 2838191 0 (12288 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (12288 + m.val) + 2)) := by decide +kernel
theorem block10_97 : ∀ m : Fin 128, tFast 2838191 0 (12416 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (12416 + m.val))) * tFast 2838191 0 (12416 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (12416 + m.val) + 2)) := by decide +kernel
theorem block10_98 : ∀ m : Fin 128, tFast 2838191 0 (12544 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (12544 + m.val))) * tFast 2838191 0 (12544 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (12544 + m.val) + 2)) := by decide +kernel
theorem block10_99 : ∀ m : Fin 128, tFast 2838191 0 (12672 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (12672 + m.val))) * tFast 2838191 0 (12672 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (12672 + m.val) + 2)) := by decide +kernel
theorem block10_100 : ∀ m : Fin 128, tFast 2838191 0 (12800 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (12800 + m.val))) * tFast 2838191 0 (12800 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (12800 + m.val) + 2)) := by decide +kernel
theorem block10_101 : ∀ m : Fin 128, tFast 2838191 0 (12928 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (12928 + m.val))) * tFast 2838191 0 (12928 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (12928 + m.val) + 2)) := by decide +kernel
theorem block10_102 : ∀ m : Fin 128, tFast 2838191 0 (13056 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (13056 + m.val))) * tFast 2838191 0 (13056 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (13056 + m.val) + 2)) := by decide +kernel
theorem block10_103 : ∀ m : Fin 128, tFast 2838191 0 (13184 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (13184 + m.val))) * tFast 2838191 0 (13184 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (13184 + m.val) + 2)) := by decide +kernel
end KsIndex.PositiveEnergyAlphaLowProd
