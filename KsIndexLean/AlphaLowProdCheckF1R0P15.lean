module

public import KsIndexLean.AlphaLowProdAccessorFast

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (1,0), part 15. -/
namespace KsIndex.PositiveEnergyAlphaLowProd
theorem block10_120 : ∀ m : Fin 128, tFast 2838191 0 (15360 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (15360 + m.val))) * tFast 2838191 0 (15360 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (15360 + m.val) + 2)) := by decide +kernel
theorem block10_121 : ∀ m : Fin 128, tFast 2838191 0 (15488 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (15488 + m.val))) * tFast 2838191 0 (15488 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (15488 + m.val) + 2)) := by decide +kernel
theorem block10_122 : ∀ m : Fin 128, tFast 2838191 0 (15616 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (15616 + m.val))) * tFast 2838191 0 (15616 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (15616 + m.val) + 2)) := by decide +kernel
theorem block10_123 : ∀ m : Fin 128, tFast 2838191 0 (15744 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (15744 + m.val))) * tFast 2838191 0 (15744 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (15744 + m.val) + 2)) := by decide +kernel
theorem block10_124 : ∀ m : Fin 128, tFast 2838191 0 (15872 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (15872 + m.val))) * tFast 2838191 0 (15872 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (15872 + m.val) + 2)) := by decide +kernel
theorem block10_125 : ∀ m : Fin 128, tFast 2838191 0 (16000 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (16000 + m.val))) * tFast 2838191 0 (16000 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (16000 + m.val) + 2)) := by decide +kernel
theorem block10_126 : ∀ m : Fin 128, tFast 2838191 0 (16128 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (16128 + m.val))) * tFast 2838191 0 (16128 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (16128 + m.val) + 2)) := by decide +kernel
theorem block10_127 : ∀ m : Fin 128, tFast 2838191 0 (16256 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (16256 + m.val))) * tFast 2838191 0 (16256 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (16256 + m.val) + 2)) := by decide +kernel
end KsIndex.PositiveEnergyAlphaLowProd
