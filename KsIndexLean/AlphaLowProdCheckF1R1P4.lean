module

public import KsIndexLean.AlphaLowProdAccessorFast

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (1,1), part 4. -/
namespace KsIndex.PositiveEnergyAlphaLowProd
theorem block11_32 : ∀ m : Fin 128, tFast 2838191 1 (4096 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (4096 + m.val))) * tFast 2838191 1 (4096 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (4096 + m.val) + 2)) := by decide +kernel
theorem block11_33 : ∀ m : Fin 128, tFast 2838191 1 (4224 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (4224 + m.val))) * tFast 2838191 1 (4224 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (4224 + m.val) + 2)) := by decide +kernel
theorem block11_34 : ∀ m : Fin 128, tFast 2838191 1 (4352 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (4352 + m.val))) * tFast 2838191 1 (4352 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (4352 + m.val) + 2)) := by decide +kernel
theorem block11_35 : ∀ m : Fin 128, tFast 2838191 1 (4480 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (4480 + m.val))) * tFast 2838191 1 (4480 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (4480 + m.val) + 2)) := by decide +kernel
theorem block11_36 : ∀ m : Fin 128, tFast 2838191 1 (4608 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (4608 + m.val))) * tFast 2838191 1 (4608 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (4608 + m.val) + 2)) := by decide +kernel
theorem block11_37 : ∀ m : Fin 128, tFast 2838191 1 (4736 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (4736 + m.val))) * tFast 2838191 1 (4736 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (4736 + m.val) + 2)) := by decide +kernel
theorem block11_38 : ∀ m : Fin 128, tFast 2838191 1 (4864 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (4864 + m.val))) * tFast 2838191 1 (4864 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (4864 + m.val) + 2)) := by decide +kernel
theorem block11_39 : ∀ m : Fin 128, tFast 2838191 1 (4992 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (4992 + m.val))) * tFast 2838191 1 (4992 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (4992 + m.val) + 2)) := by decide +kernel
end KsIndex.PositiveEnergyAlphaLowProd
