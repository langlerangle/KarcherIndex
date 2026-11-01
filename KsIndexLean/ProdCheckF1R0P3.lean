module

public import KsIndexLean.ProdAccessor

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (1,0), part 3. -/
namespace KsIndex.NegSignProd
theorem block10_24 : ∀ m : Fin 128, t 2838191 0 (3072 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (3072 + m.val))) * t 2838191 0 (3072 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (3072 + m.val) + 2)) := by decide +kernel
theorem block10_25 : ∀ m : Fin 128, t 2838191 0 (3200 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (3200 + m.val))) * t 2838191 0 (3200 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (3200 + m.val) + 2)) := by decide +kernel
theorem block10_26 : ∀ m : Fin 128, t 2838191 0 (3328 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (3328 + m.val))) * t 2838191 0 (3328 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (3328 + m.val) + 2)) := by decide +kernel
theorem block10_27 : ∀ m : Fin 128, t 2838191 0 (3456 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (3456 + m.val))) * t 2838191 0 (3456 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (3456 + m.val) + 2)) := by decide +kernel
theorem block10_28 : ∀ m : Fin 128, t 2838191 0 (3584 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (3584 + m.val))) * t 2838191 0 (3584 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (3584 + m.val) + 2)) := by decide +kernel
theorem block10_29 : ∀ m : Fin 128, t 2838191 0 (3712 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (3712 + m.val))) * t 2838191 0 (3712 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (3712 + m.val) + 2)) := by decide +kernel
theorem block10_30 : ∀ m : Fin 128, t 2838191 0 (3840 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (3840 + m.val))) * t 2838191 0 (3840 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (3840 + m.val) + 2)) := by decide +kernel
theorem block10_31 : ∀ m : Fin 128, t 2838191 0 (3968 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (3968 + m.val))) * t 2838191 0 (3968 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (3968 + m.val) + 2)) := by decide +kernel
end KsIndex.NegSignProd
