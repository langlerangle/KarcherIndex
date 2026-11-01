module

public import KsIndexLean.ProdAccessor

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (1,1), part 8. -/
namespace KsIndex.NegSignProd
theorem block11_64 : ∀ m : Fin 4, t 2838191 1 (8192 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (8192 + m.val))) * t 2838191 1 (8192 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (8192 + m.val) + 2)) := by decide +kernel
end KsIndex.NegSignProd
