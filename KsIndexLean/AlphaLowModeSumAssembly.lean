module

public import KsIndexLean.AlphaLowModePartition

@[expose] public section


/-! Exact integer assembly for the 128 full blocks and the final two terms. -/
namespace KsIndex.AlphaRemarkTrial

theorem lowLinearNumerator_from_blocks (n : ℤ) (a : Fin 129 → ℤ)
    (h : ∀ b : Fin 128,
      lowLinearNumerator (Finset.Ico (-16385+(b.val*256 : ℕ))
        (-16385+(b.val*256 : ℕ)+256)) n = a b.castSucc)
    (hlast : lowLinearNumerator (Finset.Ico 16383 16385) n = a (Fin.last 128)) :
    lowLinearNumerator (Finset.Ico (-16385) 16385) n = ∑ b : Fin 129, a b := by
  calc
    _ = (∑ b : Fin 128,
        lowLinearNumerator (Finset.Ico (-16385+(b.val*256 : ℕ))
          (-16385+(b.val*256 : ℕ)+256)) n) +
        lowLinearNumerator (Finset.Ico 16383 16385) n := by
      unfold lowLinearNumerator
      exact sum_int_window_intervals (-16385) 128 256 2
        (fun m => (rationalKernelWeight n m).num * sampleNumerator (2*m+1) /
          ((rationalKernelWeight n m).den : ℤ))
    _ = _ := by
      rw [Fin.sum_univ_castSucc a, hlast]
      congr 1
      apply Finset.sum_congr rfl
      intro b hb
      exact h b

theorem lowLinearRadius_from_blocks (n : ℤ) (e : Fin 129 → ℤ)
    (h : ∀ b : Fin 128,
      lowLinearRadius (Finset.Ico (-16385+(b.val*256 : ℕ))
        (-16385+(b.val*256 : ℕ)+256)) n = e b.castSucc)
    (hlast : lowLinearRadius (Finset.Ico 16383 16385) n = e (Fin.last 128)) :
    lowLinearRadius (Finset.Ico (-16385) 16385) n = ∑ b : Fin 129, e b := by
  calc
    _ = (∑ b : Fin 128,
        lowLinearRadius (Finset.Ico (-16385+(b.val*256 : ℕ))
          (-16385+(b.val*256 : ℕ)+256)) n) +
        lowLinearRadius (Finset.Ico 16383 16385) n := by
      unfold lowLinearRadius
      exact sum_int_window_intervals (-16385) 128 256 2
        (fun m => (|(rationalKernelWeight n m).num| * sampleRadius (2*m+1) /
          ((rationalKernelWeight n m).den : ℤ) + 2))
    _ = _ := by
      rw [Fin.sum_univ_castSucc e, hlast]
      congr 1
      apply Finset.sum_congr rfl
      intro b hb
      exact h b

end KsIndex.AlphaRemarkTrial
