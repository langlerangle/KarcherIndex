module

public import KsIndexLean.ProdAccessor

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (0,0), part 5. -/
namespace KsIndex.NegSignProd
theorem block00_40 : ∀ m : Fin 128, t 2161809 0 (5120 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (5120 + m.val))) * t 2161809 0 (5120 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (5120 + m.val) + 2)) := by decide +kernel
theorem block00_41 : ∀ m : Fin 128, t 2161809 0 (5248 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (5248 + m.val))) * t 2161809 0 (5248 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (5248 + m.val) + 2)) := by decide +kernel
theorem block00_42 : ∀ m : Fin 128, t 2161809 0 (5376 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (5376 + m.val))) * t 2161809 0 (5376 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (5376 + m.val) + 2)) := by decide +kernel
theorem block00_43 : ∀ m : Fin 128, t 2161809 0 (5504 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (5504 + m.val))) * t 2161809 0 (5504 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (5504 + m.val) + 2)) := by decide +kernel
theorem block00_44 : ∀ m : Fin 128, t 2161809 0 (5632 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (5632 + m.val))) * t 2161809 0 (5632 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (5632 + m.val) + 2)) := by decide +kernel
theorem block00_45 : ∀ m : Fin 128, t 2161809 0 (5760 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (5760 + m.val))) * t 2161809 0 (5760 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (5760 + m.val) + 2)) := by decide +kernel
theorem block00_46 : ∀ m : Fin 128, t 2161809 0 (5888 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (5888 + m.val))) * t 2161809 0 (5888 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (5888 + m.val) + 2)) := by decide +kernel
theorem block00_47 : ∀ m : Fin 128, t 2161809 0 (6016 + m.val + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * (6016 + m.val))) * t 2161809 0 (6016 + m.val) /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * (6016 + m.val) + 2)) := by decide +kernel
end KsIndex.NegSignProd
