module

public import KsIndexLean.ProdAccessor

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (0,0), part 8. -/
namespace KsIndex.NegSignProd
theorem block00_64 : ∀ m : Fin 4, t 2161809 0 (8192 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (8192 + m.val))) * t 2161809 0 (8192 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (8192 + m.val) + 2)) := by decide +kernel
end KsIndex.NegSignProd
