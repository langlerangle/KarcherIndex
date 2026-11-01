module

public import KsIndexLean.ProtoAccessor

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (1,1), part 0. -/
namespace KsIndex.NegSignProto
theorem block11_0 : ∀ m : Fin 32, t 2838191 1 (m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (m.val))) * t 2838191 1 (m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (m.val) + 2)) := by decide +kernel
theorem block11_1 : ∀ m : Fin 32, t 2838191 1 (32 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (32 + m.val))) * t 2838191 1 (32 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (32 + m.val) + 2)) := by decide +kernel
theorem block11_2 : ∀ m : Fin 4, t 2838191 1 (64 + m.val + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * (64 + m.val))) * t 2838191 1 (64 + m.val) /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * (64 + m.val) + 2)) := by decide +kernel
theorem zero11 : t 2838191 1 0 = 10 ^ 30 := by decide +kernel
end KsIndex.NegSignProto
