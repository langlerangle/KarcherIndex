module

public import KsIndexLean.ProtoCheckF1R1P0

@[expose] public section

/-! Step assembly for stream (1,1). -/
namespace KsIndex.NegSignProto
theorem step11 : ∀ n < 68, t 2838191 1 (n + 1) =
    (2838191 - 5000000 * ((1 : ℤ) + 2 * n)) * t 2838191 1 n /
      (2838191 + 5000000 * ((1 : ℤ) + 2 * n + 2)) := by
  intro n hn
  by_cases h0 : n < 32
  · exact block11_0 ⟨n, h0⟩
  by_cases h32 : n < 64
  · have e : 32 + (n - 32) = n := by omega
    rw [← e]
    exact block11_1 ⟨n - 32, by omega⟩
  · have e : 64 + (n - 64) = n := by omega
    rw [← e]
    exact block11_2 ⟨n - 64, by omega⟩
end KsIndex.NegSignProto
