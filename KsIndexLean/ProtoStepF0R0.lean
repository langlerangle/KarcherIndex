module

public import KsIndexLean.ProtoCheckF0R0P0

@[expose] public section

/-! Step assembly for stream (0,0). -/
namespace KsIndex.NegSignProto
theorem step00 : ∀ n < 68, t 2161809 0 (n + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * n)) * t 2161809 0 n /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * n + 2)) := by
  intro n hn
  by_cases h0 : n < 32
  · exact block00_0 ⟨n, h0⟩
  by_cases h32 : n < 64
  · have e : 32 + (n - 32) = n := by omega
    rw [← e]
    exact block00_1 ⟨n - 32, by omega⟩
  · have e : 64 + (n - 64) = n := by omega
    rw [← e]
    exact block00_2 ⟨n - 64, by omega⟩
end KsIndex.NegSignProto
