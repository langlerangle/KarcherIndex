module

public import KsIndexLean.ProdAccessor

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (1,1), part 0. -/
namespace KsIndex.NegSignProd
theorem block11_0 : ∀ m : Fin 128, t 2838191 1 (m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (m.val))) * t 2838191 1 (m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (m.val) + 2)) := by decide +kernel
theorem block11_1 : ∀ m : Fin 128, t 2838191 1 (128 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (128 + m.val))) * t 2838191 1 (128 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (128 + m.val) + 2)) := by decide +kernel
theorem block11_2 : ∀ m : Fin 128, t 2838191 1 (256 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (256 + m.val))) * t 2838191 1 (256 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (256 + m.val) + 2)) := by decide +kernel
theorem block11_3 : ∀ m : Fin 128, t 2838191 1 (384 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (384 + m.val))) * t 2838191 1 (384 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (384 + m.val) + 2)) := by decide +kernel
theorem block11_4 : ∀ m : Fin 128, t 2838191 1 (512 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (512 + m.val))) * t 2838191 1 (512 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (512 + m.val) + 2)) := by decide +kernel
theorem block11_5 : ∀ m : Fin 128, t 2838191 1 (640 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (640 + m.val))) * t 2838191 1 (640 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (640 + m.val) + 2)) := by decide +kernel
theorem block11_6 : ∀ m : Fin 128, t 2838191 1 (768 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (768 + m.val))) * t 2838191 1 (768 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (768 + m.val) + 2)) := by decide +kernel
theorem block11_7 : ∀ m : Fin 128, t 2838191 1 (896 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (896 + m.val))) * t 2838191 1 (896 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (896 + m.val) + 2)) := by decide +kernel
theorem zero11 : t 2838191 1 0 = 10 ^ 30 := by decide +kernel
end KsIndex.NegSignProd
