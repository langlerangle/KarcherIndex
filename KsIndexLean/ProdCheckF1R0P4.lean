module

public import KsIndexLean.ProdAccessor

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (1,0), part 4. -/
namespace KsIndex.NegSignProd
theorem block10_32 : ∀ m : Fin 128, t 2838191 0 (4096 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (4096 + m.val))) * t 2838191 0 (4096 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (4096 + m.val) + 2)) := by decide +kernel
theorem block10_33 : ∀ m : Fin 128, t 2838191 0 (4224 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (4224 + m.val))) * t 2838191 0 (4224 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (4224 + m.val) + 2)) := by decide +kernel
theorem block10_34 : ∀ m : Fin 128, t 2838191 0 (4352 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (4352 + m.val))) * t 2838191 0 (4352 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (4352 + m.val) + 2)) := by decide +kernel
theorem block10_35 : ∀ m : Fin 128, t 2838191 0 (4480 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (4480 + m.val))) * t 2838191 0 (4480 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (4480 + m.val) + 2)) := by decide +kernel
theorem block10_36 : ∀ m : Fin 128, t 2838191 0 (4608 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (4608 + m.val))) * t 2838191 0 (4608 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (4608 + m.val) + 2)) := by decide +kernel
theorem block10_37 : ∀ m : Fin 128, t 2838191 0 (4736 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (4736 + m.val))) * t 2838191 0 (4736 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (4736 + m.val) + 2)) := by decide +kernel
theorem block10_38 : ∀ m : Fin 128, t 2838191 0 (4864 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (4864 + m.val))) * t 2838191 0 (4864 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (4864 + m.val) + 2)) := by decide +kernel
theorem block10_39 : ∀ m : Fin 128, t 2838191 0 (4992 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (4992 + m.val))) * t 2838191 0 (4992 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (4992 + m.val) + 2)) := by decide +kernel
end KsIndex.NegSignProd
