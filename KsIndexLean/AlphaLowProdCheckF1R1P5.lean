module

public import KsIndexLean.AlphaLowProdAccessorFast

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (1,1), part 5. -/
namespace KsIndex.PositiveEnergyAlphaLowProd
theorem block11_40 : ∀ m : Fin 128, tFast 2838191 1 (5120 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (5120 + m.val))) * tFast 2838191 1 (5120 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (5120 + m.val) + 2)) := by decide +kernel
theorem block11_41 : ∀ m : Fin 128, tFast 2838191 1 (5248 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (5248 + m.val))) * tFast 2838191 1 (5248 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (5248 + m.val) + 2)) := by decide +kernel
theorem block11_42 : ∀ m : Fin 128, tFast 2838191 1 (5376 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (5376 + m.val))) * tFast 2838191 1 (5376 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (5376 + m.val) + 2)) := by decide +kernel
theorem block11_43 : ∀ m : Fin 128, tFast 2838191 1 (5504 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (5504 + m.val))) * tFast 2838191 1 (5504 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (5504 + m.val) + 2)) := by decide +kernel
theorem block11_44 : ∀ m : Fin 128, tFast 2838191 1 (5632 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (5632 + m.val))) * tFast 2838191 1 (5632 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (5632 + m.val) + 2)) := by decide +kernel
theorem block11_45 : ∀ m : Fin 128, tFast 2838191 1 (5760 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (5760 + m.val))) * tFast 2838191 1 (5760 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (5760 + m.val) + 2)) := by decide +kernel
theorem block11_46 : ∀ m : Fin 128, tFast 2838191 1 (5888 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (5888 + m.val))) * tFast 2838191 1 (5888 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (5888 + m.val) + 2)) := by decide +kernel
theorem block11_47 : ∀ m : Fin 128, tFast 2838191 1 (6016 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (6016 + m.val))) * tFast 2838191 1 (6016 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (6016 + m.val) + 2)) := by decide +kernel
end KsIndex.PositiveEnergyAlphaLowProd
