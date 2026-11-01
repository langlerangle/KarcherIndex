module

public import KsIndexLean.AlphaLowProdAccessorFast

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (0,0), part 16. -/
namespace KsIndex.PositiveEnergyAlphaLowProd
theorem block00_128 : ∀ m : Fin 5, tFast 2161809 0 (16384 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (16384 + m.val))) * tFast 2161809 0 (16384 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (16384 + m.val) + 2)) := by decide +kernel
end KsIndex.PositiveEnergyAlphaLowProd
