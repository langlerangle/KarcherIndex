module

public import KsIndexLean.AlphaLowProdAccessorFast

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (1,1), part 16. -/
namespace KsIndex.PositiveEnergyAlphaLowProd
theorem block11_128 : ∀ m : Fin 5, tFast 2838191 1 (16384 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (16384 + m.val))) * tFast 2838191 1 (16384 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (16384 + m.val) + 2)) := by decide +kernel
end KsIndex.PositiveEnergyAlphaLowProd
