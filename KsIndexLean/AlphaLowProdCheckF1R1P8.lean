module

public import KsIndexLean.AlphaLowProdAccessorFast

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (1,1), part 8. -/
namespace KsIndex.PositiveEnergyAlphaLowProd
theorem block11_64 : ∀ m : Fin 128, tFast 2838191 1 (8192 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (8192 + m.val))) * tFast 2838191 1 (8192 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (8192 + m.val) + 2)) := by decide +kernel
theorem block11_65 : ∀ m : Fin 128, tFast 2838191 1 (8320 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (8320 + m.val))) * tFast 2838191 1 (8320 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (8320 + m.val) + 2)) := by decide +kernel
theorem block11_66 : ∀ m : Fin 128, tFast 2838191 1 (8448 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (8448 + m.val))) * tFast 2838191 1 (8448 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (8448 + m.val) + 2)) := by decide +kernel
theorem block11_67 : ∀ m : Fin 128, tFast 2838191 1 (8576 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (8576 + m.val))) * tFast 2838191 1 (8576 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (8576 + m.val) + 2)) := by decide +kernel
theorem block11_68 : ∀ m : Fin 128, tFast 2838191 1 (8704 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (8704 + m.val))) * tFast 2838191 1 (8704 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (8704 + m.val) + 2)) := by decide +kernel
theorem block11_69 : ∀ m : Fin 128, tFast 2838191 1 (8832 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (8832 + m.val))) * tFast 2838191 1 (8832 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (8832 + m.val) + 2)) := by decide +kernel
theorem block11_70 : ∀ m : Fin 128, tFast 2838191 1 (8960 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (8960 + m.val))) * tFast 2838191 1 (8960 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (8960 + m.val) + 2)) := by decide +kernel
theorem block11_71 : ∀ m : Fin 128, tFast 2838191 1 (9088 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (9088 + m.val))) * tFast 2838191 1 (9088 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (9088 + m.val) + 2)) := by decide +kernel
end KsIndex.PositiveEnergyAlphaLowProd
