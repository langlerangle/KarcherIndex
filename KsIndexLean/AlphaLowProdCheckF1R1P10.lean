module

public import KsIndexLean.AlphaLowProdAccessorFast

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (1,1), part 10. -/
namespace KsIndex.PositiveEnergyAlphaLowProd
theorem block11_80 : ∀ m : Fin 128, tFast 2838191 1 (10240 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (10240 + m.val))) * tFast 2838191 1 (10240 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (10240 + m.val) + 2)) := by decide +kernel
theorem block11_81 : ∀ m : Fin 128, tFast 2838191 1 (10368 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (10368 + m.val))) * tFast 2838191 1 (10368 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (10368 + m.val) + 2)) := by decide +kernel
theorem block11_82 : ∀ m : Fin 128, tFast 2838191 1 (10496 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (10496 + m.val))) * tFast 2838191 1 (10496 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (10496 + m.val) + 2)) := by decide +kernel
theorem block11_83 : ∀ m : Fin 128, tFast 2838191 1 (10624 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (10624 + m.val))) * tFast 2838191 1 (10624 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (10624 + m.val) + 2)) := by decide +kernel
theorem block11_84 : ∀ m : Fin 128, tFast 2838191 1 (10752 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (10752 + m.val))) * tFast 2838191 1 (10752 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (10752 + m.val) + 2)) := by decide +kernel
theorem block11_85 : ∀ m : Fin 128, tFast 2838191 1 (10880 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (10880 + m.val))) * tFast 2838191 1 (10880 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (10880 + m.val) + 2)) := by decide +kernel
theorem block11_86 : ∀ m : Fin 128, tFast 2838191 1 (11008 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (11008 + m.val))) * tFast 2838191 1 (11008 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (11008 + m.val) + 2)) := by decide +kernel
theorem block11_87 : ∀ m : Fin 128, tFast 2838191 1 (11136 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (11136 + m.val))) * tFast 2838191 1 (11136 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (11136 + m.val) + 2)) := by decide +kernel
end KsIndex.PositiveEnergyAlphaLowProd
