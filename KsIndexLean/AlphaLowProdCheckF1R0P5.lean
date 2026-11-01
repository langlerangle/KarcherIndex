module

public import KsIndexLean.AlphaLowProdAccessorFast

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (1,0), part 5. -/
namespace KsIndex.PositiveEnergyAlphaLowProd
theorem block10_40 : ∀ m : Fin 128, tFast 2838191 0 (5120 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (5120 + m.val))) * tFast 2838191 0 (5120 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (5120 + m.val) + 2)) := by decide +kernel
theorem block10_41 : ∀ m : Fin 128, tFast 2838191 0 (5248 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (5248 + m.val))) * tFast 2838191 0 (5248 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (5248 + m.val) + 2)) := by decide +kernel
theorem block10_42 : ∀ m : Fin 128, tFast 2838191 0 (5376 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (5376 + m.val))) * tFast 2838191 0 (5376 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (5376 + m.val) + 2)) := by decide +kernel
theorem block10_43 : ∀ m : Fin 128, tFast 2838191 0 (5504 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (5504 + m.val))) * tFast 2838191 0 (5504 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (5504 + m.val) + 2)) := by decide +kernel
theorem block10_44 : ∀ m : Fin 128, tFast 2838191 0 (5632 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (5632 + m.val))) * tFast 2838191 0 (5632 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (5632 + m.val) + 2)) := by decide +kernel
theorem block10_45 : ∀ m : Fin 128, tFast 2838191 0 (5760 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (5760 + m.val))) * tFast 2838191 0 (5760 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (5760 + m.val) + 2)) := by decide +kernel
theorem block10_46 : ∀ m : Fin 128, tFast 2838191 0 (5888 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (5888 + m.val))) * tFast 2838191 0 (5888 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (5888 + m.val) + 2)) := by decide +kernel
theorem block10_47 : ∀ m : Fin 128, tFast 2838191 0 (6016 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (6016 + m.val))) * tFast 2838191 0 (6016 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (6016 + m.val) + 2)) := by decide +kernel
end KsIndex.PositiveEnergyAlphaLowProd
