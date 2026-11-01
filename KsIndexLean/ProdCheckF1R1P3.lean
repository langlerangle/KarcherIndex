module

public import KsIndexLean.ProdAccessor

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (1,1), part 3. -/
namespace KsIndex.NegSignProd
theorem block11_24 : ∀ m : Fin 128, t 2838191 1 (3072 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (3072 + m.val))) * t 2838191 1 (3072 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (3072 + m.val) + 2)) := by decide +kernel
theorem block11_25 : ∀ m : Fin 128, t 2838191 1 (3200 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (3200 + m.val))) * t 2838191 1 (3200 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (3200 + m.val) + 2)) := by decide +kernel
theorem block11_26 : ∀ m : Fin 128, t 2838191 1 (3328 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (3328 + m.val))) * t 2838191 1 (3328 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (3328 + m.val) + 2)) := by decide +kernel
theorem block11_27 : ∀ m : Fin 128, t 2838191 1 (3456 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (3456 + m.val))) * t 2838191 1 (3456 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (3456 + m.val) + 2)) := by decide +kernel
theorem block11_28 : ∀ m : Fin 128, t 2838191 1 (3584 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (3584 + m.val))) * t 2838191 1 (3584 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (3584 + m.val) + 2)) := by decide +kernel
theorem block11_29 : ∀ m : Fin 128, t 2838191 1 (3712 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (3712 + m.val))) * t 2838191 1 (3712 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (3712 + m.val) + 2)) := by decide +kernel
theorem block11_30 : ∀ m : Fin 128, t 2838191 1 (3840 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (3840 + m.val))) * t 2838191 1 (3840 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (3840 + m.val) + 2)) := by decide +kernel
theorem block11_31 : ∀ m : Fin 128, t 2838191 1 (3968 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (3968 + m.val))) * t 2838191 1 (3968 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (3968 + m.val) + 2)) := by decide +kernel
end KsIndex.NegSignProd
