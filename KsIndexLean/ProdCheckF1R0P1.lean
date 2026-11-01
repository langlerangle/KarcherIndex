module

public import KsIndexLean.ProdAccessor

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (1,0), part 1. -/
namespace KsIndex.NegSignProd
theorem block10_8 : ∀ m : Fin 128, t 2838191 0 (1024 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (1024 + m.val))) * t 2838191 0 (1024 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (1024 + m.val) + 2)) := by decide +kernel
theorem block10_9 : ∀ m : Fin 128, t 2838191 0 (1152 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (1152 + m.val))) * t 2838191 0 (1152 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (1152 + m.val) + 2)) := by decide +kernel
theorem block10_10 : ∀ m : Fin 128, t 2838191 0 (1280 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (1280 + m.val))) * t 2838191 0 (1280 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (1280 + m.val) + 2)) := by decide +kernel
theorem block10_11 : ∀ m : Fin 128, t 2838191 0 (1408 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (1408 + m.val))) * t 2838191 0 (1408 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (1408 + m.val) + 2)) := by decide +kernel
theorem block10_12 : ∀ m : Fin 128, t 2838191 0 (1536 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (1536 + m.val))) * t 2838191 0 (1536 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (1536 + m.val) + 2)) := by decide +kernel
theorem block10_13 : ∀ m : Fin 128, t 2838191 0 (1664 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (1664 + m.val))) * t 2838191 0 (1664 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (1664 + m.val) + 2)) := by decide +kernel
theorem block10_14 : ∀ m : Fin 128, t 2838191 0 (1792 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (1792 + m.val))) * t 2838191 0 (1792 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (1792 + m.val) + 2)) := by decide +kernel
theorem block10_15 : ∀ m : Fin 128, t 2838191 0 (1920 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (1920 + m.val))) * t 2838191 0 (1920 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (1920 + m.val) + 2)) := by decide +kernel
end KsIndex.NegSignProd
