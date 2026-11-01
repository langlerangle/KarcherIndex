module

public import KsIndexLean.ProdAccessor

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (1,1), part 6. -/
namespace KsIndex.NegSignProd
theorem block11_48 : ∀ m : Fin 128, t 2838191 1 (6144 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (6144 + m.val))) * t 2838191 1 (6144 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (6144 + m.val) + 2)) := by decide +kernel
theorem block11_49 : ∀ m : Fin 128, t 2838191 1 (6272 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (6272 + m.val))) * t 2838191 1 (6272 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (6272 + m.val) + 2)) := by decide +kernel
theorem block11_50 : ∀ m : Fin 128, t 2838191 1 (6400 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (6400 + m.val))) * t 2838191 1 (6400 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (6400 + m.val) + 2)) := by decide +kernel
theorem block11_51 : ∀ m : Fin 128, t 2838191 1 (6528 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (6528 + m.val))) * t 2838191 1 (6528 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (6528 + m.val) + 2)) := by decide +kernel
theorem block11_52 : ∀ m : Fin 128, t 2838191 1 (6656 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (6656 + m.val))) * t 2838191 1 (6656 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (6656 + m.val) + 2)) := by decide +kernel
theorem block11_53 : ∀ m : Fin 128, t 2838191 1 (6784 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (6784 + m.val))) * t 2838191 1 (6784 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (6784 + m.val) + 2)) := by decide +kernel
theorem block11_54 : ∀ m : Fin 128, t 2838191 1 (6912 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (6912 + m.val))) * t 2838191 1 (6912 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (6912 + m.val) + 2)) := by decide +kernel
theorem block11_55 : ∀ m : Fin 128, t 2838191 1 (7040 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (7040 + m.val))) * t 2838191 1 (7040 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (7040 + m.val) + 2)) := by decide +kernel
end KsIndex.NegSignProd
