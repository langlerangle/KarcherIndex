module

public import KsIndexLean.ProtoCheckF0R1P0

@[expose] public section

/-! Step assembly for stream (0,1). -/
namespace KsIndex.NegSignProto
theorem step01 : ∀ n < 68, t 2161809 1 (n + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * n)) * t 2161809 1 n /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * n + 2)) := by
  intro n hn
  by_cases h0 : n < 32
  · exact block01_0 ⟨n, h0⟩
  by_cases h32 : n < 64
  · have e : 32 + (n - 32) = n := by omega
    rw [← e]
    exact block01_1 ⟨n - 32, by omega⟩
  · have e : 64 + (n - 64) = n := by omega
    rw [← e]
    exact block01_2 ⟨n - 64, by omega⟩
end KsIndex.NegSignProto
