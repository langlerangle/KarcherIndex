module

public import KsIndexLean.ProdAccessor

@[expose] public section

set_option linter.style.longLine false
/-! Block checks, stream (0,1), part 6. -/
namespace KsIndex.NegSignProd
theorem block01_48 : ∀ m : Fin 128, t 2161809 1 (6144 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (6144 + m.val))) * t 2161809 1 (6144 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (6144 + m.val) + 2)) := by decide +kernel
theorem block01_49 : ∀ m : Fin 128, t 2161809 1 (6272 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (6272 + m.val))) * t 2161809 1 (6272 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (6272 + m.val) + 2)) := by decide +kernel
theorem block01_50 : ∀ m : Fin 128, t 2161809 1 (6400 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (6400 + m.val))) * t 2161809 1 (6400 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (6400 + m.val) + 2)) := by decide +kernel
theorem block01_51 : ∀ m : Fin 128, t 2161809 1 (6528 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (6528 + m.val))) * t 2161809 1 (6528 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (6528 + m.val) + 2)) := by decide +kernel
theorem block01_52 : ∀ m : Fin 128, t 2161809 1 (6656 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (6656 + m.val))) * t 2161809 1 (6656 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (6656 + m.val) + 2)) := by decide +kernel
theorem block01_53 : ∀ m : Fin 128, t 2161809 1 (6784 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (6784 + m.val))) * t 2161809 1 (6784 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (6784 + m.val) + 2)) := by decide +kernel
theorem block01_54 : ∀ m : Fin 128, t 2161809 1 (6912 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (6912 + m.val))) * t 2161809 1 (6912 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (6912 + m.val) + 2)) := by decide +kernel
theorem block01_55 : ∀ m : Fin 128, t 2161809 1 (7040 + m.val + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * (7040 + m.val))) * t 2161809 1 (7040 + m.val) /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * (7040 + m.val) + 2)) := by decide +kernel
end KsIndex.NegSignProd
