module

public import KsIndexLean.PaperResonantSectorNullity

@[expose] public section


/-! Exact k=3 arbitrary-period nullity on the chain encoding. The EW/model
identification is not asserted by these theorems. -/
noncomputable section
open Classical
namespace KsIndex.PaperSlitTransport
open KsIndex.Surface KsIndex.NullityDecomp KsIndex.Staircase KsIndex.BandArithmetic

theorem nulSurface_eq_three_add_two_endpoints {m : ℕ} [NeZero m] :
    nulSurface 3 m = 3 + 2 * (endpoints alphaStar m).card := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [nulSurface_eq_sum_isotypic 3 m (by norm_num) hm, Finset.sum_comm,
    Fin.sum_univ_eq_sum_range
      (fun n => ∑ r : Fin 3, Cardinal.toENat (Module.rank ℂ (isotypicFiber 3 m (r : ℕ) n))) m,
    ← Finset.add_sum_erase (Finset.range m) _ (Finset.mem_range.mpr hm)]
  have hEsub : endpoints alphaStar m ⊆ (Finset.range m).erase 0 := by
    intro n hn
    rw [endpoints, Finset.mem_filter, Finset.mem_Ico] at hn
    exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr hn.1.2⟩
  apply congrArg₂ (· + ·)
  · calc (∑ r : Fin 3, Cardinal.toENat (Module.rank ℂ (isotypicFiber 3 m (r : ℕ) 0)))
        = ∑ _r : Fin 3, (1 : ℕ∞) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [isotypicFiber_rank_toENat, isotypicFiber_zeroPhase_finrank_eq_one r.isLt]
          rfl
      _ = 3 := by simp
  · calc (∑ n ∈ (Finset.range m).erase 0,
            ∑ r : Fin 3, Cardinal.toENat (Module.rank ℂ (isotypicFiber 3 m (r : ℕ) n)))
        = ∑ n ∈ (Finset.range m).erase 0,
            (if n ∈ endpoints alphaStar m then (2 : ℕ∞) else 0) := by
          refine Finset.sum_congr rfl fun n hn => ?_
          obtain ⟨hn0, hnm⟩ := Finset.mem_erase.mp hn
          have hnlt : n < m := Finset.mem_range.mp hnm
          rw [interiorPhase_total_eq_endpoint (Nat.pos_of_ne_zero hn0) hnlt]
          have hI : n ∈ Finset.Ico 1 m := Finset.mem_Ico.mpr ⟨by omega, hnlt⟩
          simp only [endpoints, Finset.mem_filter, hI, true_and]
      _ = ∑ _n ∈ (Finset.range m).erase 0 ∩ endpoints alphaStar m, (2 : ℕ∞) :=
          Finset.sum_ite_mem _ _ _
      _ = ∑ _n ∈ endpoints alphaStar m, (2 : ℕ∞) := by
          rw [Finset.inter_eq_right.mpr hEsub]
      _ = 2 * (endpoints alphaStar m).card := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- The paper's resonant dichotomy, unconditional on the k=3 chain carrier. -/
theorem nulSurface_eq_seven_or_three {m : ℕ} [NeZero m] :
    nulSurface 3 m = if ∃ z : ℤ, (m : ℝ) * alphaStar = (z : ℝ) then 7 else 3 := by
  rw [nulSurface_eq_three_add_two_endpoints]
  have hb := resonance_bookkeeping m (Nat.one_le_iff_ne_zero.mpr (NeZero.ne m))
  have hcast : (3 : ℕ∞) + 2 * ((endpoints alphaStar m).card : ℕ∞) =
      ((3 + 2 * (endpoints alphaStar m).card : ℕ) : ℕ∞) := by
    push_cast
    ring
  rw [hcast, hb]
  simp only [Nat.cast_ite, Nat.cast_ofNat]

end KsIndex.PaperSlitTransport
