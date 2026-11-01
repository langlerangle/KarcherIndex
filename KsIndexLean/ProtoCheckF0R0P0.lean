module

public import KsIndexLean.ProtoAccessor

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (0,0), part 0. -/
namespace KsIndex.NegSignProto
theorem block00_0 : ∀ m : Fin 32, t 2161809 0 (m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (m.val))) * t 2161809 0 (m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (m.val) + 2)) := by decide +kernel
theorem block00_1 : ∀ m : Fin 32, t 2161809 0 (32 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (32 + m.val))) * t 2161809 0 (32 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (32 + m.val) + 2)) := by decide +kernel
theorem block00_2 : ∀ m : Fin 4, t 2161809 0 (64 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (64 + m.val))) * t 2161809 0 (64 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (64 + m.val) + 2)) := by decide +kernel
theorem zero00 : t 2161809 0 0 = 10 ^ 30 := by decide +kernel
end KsIndex.NegSignProto
