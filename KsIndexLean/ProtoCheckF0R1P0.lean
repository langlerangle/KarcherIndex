module

public import KsIndexLean.ProtoAccessor

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (0,1), part 0. -/
namespace KsIndex.NegSignProto
theorem block01_0 : ∀ m : Fin 32, t 2161809 1 (m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (m.val))) * t 2161809 1 (m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (m.val) + 2)) := by decide +kernel
theorem block01_1 : ∀ m : Fin 32, t 2161809 1 (32 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (32 + m.val))) * t 2161809 1 (32 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (32 + m.val) + 2)) := by decide +kernel
theorem block01_2 : ∀ m : Fin 4, t 2161809 1 (64 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (64 + m.val))) * t 2161809 1 (64 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (64 + m.val) + 2)) := by decide +kernel
theorem zero01 : t 2161809 1 0 = 10 ^ 30 := by decide +kernel
end KsIndex.NegSignProto
