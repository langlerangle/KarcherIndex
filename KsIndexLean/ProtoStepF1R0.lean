module

public import KsIndexLean.ProtoCheckF1R0P0

@[expose] public section

/-! Step assembly for stream (1,0). -/
namespace KsIndex.NegSignProto
theorem step10 : ∀ n < 68, t 2838191 0 (n + 1) =
    (2838191 - 5000000 * ((0 : ℤ) + 2 * n)) * t 2838191 0 n /
      (2838191 + 5000000 * ((0 : ℤ) + 2 * n + 2)) := by
  intro n hn
  by_cases h0 : n < 32
  · exact block10_0 ⟨n, h0⟩
  by_cases h32 : n < 64
  · have e : 32 + (n - 32) = n := by omega
    rw [← e]
    exact block10_1 ⟨n - 32, by omega⟩
  · have e : 64 + (n - 64) = n := by omega
    rw [← e]
    exact block10_2 ⟨n - 64, by omega⟩
end KsIndex.NegSignProto
