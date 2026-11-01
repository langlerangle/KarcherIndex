module

public import KsIndexLean.ProdAccessor

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (1,0), part 6. -/
namespace KsIndex.NegSignProd
theorem block10_48 : ∀ m : Fin 128, t 2838191 0 (6144 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (6144 + m.val))) * t 2838191 0 (6144 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (6144 + m.val) + 2)) := by decide +kernel
theorem block10_49 : ∀ m : Fin 128, t 2838191 0 (6272 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (6272 + m.val))) * t 2838191 0 (6272 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (6272 + m.val) + 2)) := by decide +kernel
theorem block10_50 : ∀ m : Fin 128, t 2838191 0 (6400 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (6400 + m.val))) * t 2838191 0 (6400 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (6400 + m.val) + 2)) := by decide +kernel
theorem block10_51 : ∀ m : Fin 128, t 2838191 0 (6528 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (6528 + m.val))) * t 2838191 0 (6528 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (6528 + m.val) + 2)) := by decide +kernel
theorem block10_52 : ∀ m : Fin 128, t 2838191 0 (6656 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (6656 + m.val))) * t 2838191 0 (6656 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (6656 + m.val) + 2)) := by decide +kernel
theorem block10_53 : ∀ m : Fin 128, t 2838191 0 (6784 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (6784 + m.val))) * t 2838191 0 (6784 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (6784 + m.val) + 2)) := by decide +kernel
theorem block10_54 : ∀ m : Fin 128, t 2838191 0 (6912 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (6912 + m.val))) * t 2838191 0 (6912 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (6912 + m.val) + 2)) := by decide +kernel
theorem block10_55 : ∀ m : Fin 128, t 2838191 0 (7040 + m.val + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * (7040 + m.val))) * t 2838191 0 (7040 + m.val) /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * (7040 + m.val) + 2)) := by decide +kernel
end KsIndex.NegSignProd
