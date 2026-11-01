module

public import KsIndexLean.GeneralDirichletValues
public import KsIndexLean.GeneralNeumannClasses
public import KsIndexLean.MixedOrientationRotation
public import KsIndexLean.NullityRadical
public import KsIndexLean.JacobiFamily

@[expose] public section


/-!
# Surface nullity three from middle-class single-arc bounds

For `k ≥ 3`, the theorem derives `nulSurface k 2 = 3` assuming
`SingleArcUpperBound k j` for every middle class `2 ≤ j` and `j + 2 ≤ k`.
The upper bound combines the sector decomposition and rank comparison with
Dirichlet nullity values, the Neumann class-sum bound, and conditional mixed-sector
vanishing in both orientations. The translation fields supply the lower bound.
The single-arc estimates remain explicit hypotheses of this theorem.
-/

noncomputable section
namespace KsIndex.NullityDecomp
open KsIndex.Surface KsIndex.WeakH1 KsIndex.Trace KsIndex.Spectral KsIndex.FormIndex

variable {k : ℕ}

/-- **The conditional general capstone.** -/
theorem nulSurface_eq_three_of_singleArc (hk : 3 ≤ k)
    (hC : ∀ j : ℕ, 2 ≤ j → j + 2 ≤ k →
      KsIndex.SingleArcReindex.SingleArcUpperBound k j) :
    nulSurface k 2 = 3 := by
  have hk2 : 2 ≤ k := by omega
  have : NeZero k := ⟨by omega⟩
  apply le_antisymm
  · rw [nulSurface_eq_sum_sectors k (by omega)]
    -- per-sector rank bound, then the ℕ-level block sum
    have hb : ∀ (r : Fin k) (s₁ s₀ : Fin 2),
        Cardinal.toENat (Module.rank ℂ
          (boundedJacobiSector k (r : ℕ) (s₁ : ℕ) (s₀ : ℕ))) ≤
        (diskWeakNullity (mixedCharacterDomain k (r : ℕ)
            (decide ((s₁ : ℕ) = 0)) (decide ((s₀ : ℕ) = 0)))
          (surfacePotential k) : ℕ∞) :=
      fun r s₁ s₀ => sector_rank_le_nullity hk2 s₁.isLt s₀.isLt
    calc (∑ r : Fin k, ∑ s₁ : Fin 2, ∑ s₀ : Fin 2, Cardinal.toENat (Module.rank ℂ
          (boundedJacobiSector k (r : ℕ) (s₁ : ℕ) (s₀ : ℕ))))
        ≤ ∑ r : Fin k, ∑ s₁ : Fin 2, ∑ s₀ : Fin 2,
            (diskWeakNullity (mixedCharacterDomain k (r : ℕ)
                (decide ((s₁ : ℕ) = 0)) (decide ((s₀ : ℕ) = 0)))
              (surfacePotential k) : ℕ∞) :=
          Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s₁ _ =>
            Finset.sum_le_sum fun s₀ _ => hb r s₁ s₀
      _ = ((∑ r : Fin k, ∑ s₁ : Fin 2, ∑ s₀ : Fin 2,
            diskWeakNullity (mixedCharacterDomain k (r : ℕ)
              (decide ((s₁ : ℕ) = 0)) (decide ((s₀ : ℕ) = 0)))
              (surfacePotential k) : ℕ) : ℕ∞) := by
          push_cast
          rfl
      _ ≤ ((3 : ℕ) : ℕ∞) := by
          apply Nat.cast_le.mpr
          -- expand the flag square and regroup the four columns
          have hexp : (∑ r : Fin k, ∑ s₁ : Fin 2, ∑ s₀ : Fin 2,
              diskWeakNullity (mixedCharacterDomain k (r : ℕ)
                (decide ((s₁ : ℕ) = 0)) (decide ((s₀ : ℕ) = 0)))
                (surfacePotential k)) =
              (∑ r : Fin k, diskWeakNullity
                (mixedCharacterDomain k (r : ℕ) true true) (surfacePotential k)) +
              (∑ r : Fin k, diskWeakNullity
                (mixedCharacterDomain k (r : ℕ) true false) (surfacePotential k)) +
              (∑ r : Fin k, diskWeakNullity
                (mixedCharacterDomain k (r : ℕ) false true) (surfacePotential k)) +
              (∑ r : Fin k, diskWeakNullity
                (mixedCharacterDomain k (r : ℕ) false false) (surfacePotential k)) := by
            simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
            rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
              ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro r _
            norm_num
            ring
          rw [hexp]
          have hND : (∑ r : Fin k, diskWeakNullity
              (mixedCharacterDomain k (r : ℕ) true false) (surfacePotential k)) = 0 :=
            Finset.sum_eq_zero fun r _ =>
              both_mixed_nullities_zero_of_middle_bounds hk hC (r : ℕ) r.isLt
                true false (by decide)
          have hDN : (∑ r : Fin k, diskWeakNullity
              (mixedCharacterDomain k (r : ℕ) false true) (surfacePotential k)) = 0 :=
            Finset.sum_eq_zero fun r _ =>
              both_mixed_nullities_zero_of_middle_bounds hk hC (r : ℕ) r.isLt
                false true (by decide)
          have hDD : (∑ r : Fin k, diskWeakNullity
              (mixedCharacterDomain k (r : ℕ) false false) (surfacePotential k)) = 1 := by
            have hval : ∀ r : Fin k, diskWeakNullity
                (mixedCharacterDomain k (r : ℕ) false false) (surfacePotential k) =
                if (r : ℕ) = 0 then 1 else 0 := fun r =>
              pureSector_dirichlet_nullity_gen hk2 r.isLt
            rw [Finset.sum_congr rfl fun r _ => hval r,
              Finset.sum_eq_single (0 : Fin k)
                (fun b _ hb => by
                  rw [ite_eq_right_iff]
                  intro h
                  exact (hb (Fin.ext (by simpa using h))).elim)
                (fun h => absurd (Finset.mem_univ _) h)]
            simp
          have hNN := neumann_classes_nullity_sum_le_two hk
          omega
  · exact KsIndex.JacobiFamily.three_le_nulSurface k 2 hk2

end KsIndex.NullityDecomp
