module

public import KsIndexLean.NullityRadical
public import KsIndexLean.PureSectorValues
public import KsIndexLean.CountUnconditional
public import KsIndexLean.JacobiFamily

@[expose] public section


/-!
# Bounded Jacobi nullity of `Ξ_{3,2}`

Upper bound: `nulSurface_eq_sum_sectors` splits the surface nullity
over the twelve joint symmetry sectors; each sector's rank is bounded by the disk weak
nullity of its parity-matched mixed character domain (`sector_rank_le_nullity`); the
twelve values are the pure-sector table (NN `[j≠0]`, DD `δ_{j,0}`) and
the Zaremba edge vanishing (all three classes are edge at `k = 3`: the middle window
`2 ≤ r ≤ k−2` is empty).  Total: `2 + 1 + 0 = 3`.  Lower bound: the three translation
fields (`three_le_nulSurface`).
-/

noncomputable section
namespace KsIndex.NullityDecomp
open KsIndex.Surface KsIndex.WeakH1 KsIndex.Trace KsIndex.Spectral KsIndex.FormIndex

/-- The bounded-Jacobi nullity of `Ξ_{3,2}` is exactly `3`. -/
theorem nulSurface_three_two : nulSurface 3 2 = 3 := by
  apply le_antisymm
  · -- upper bound through the sector split and the twelve domain nullities
    rw [nulSurface_eq_sum_sectors 3 (by norm_num)]
    have hb : ∀ (r : Fin 3) (s₁ s₀ : Fin 2),
        Cardinal.toENat (Module.rank ℂ
          (boundedJacobiSector 3 (r : ℕ) (s₁ : ℕ) (s₀ : ℕ))) ≤
        (diskWeakNullity (mixedCharacterDomain 3 (r : ℕ)
            (decide ((s₁ : ℕ) = 0)) (decide ((s₀ : ℕ) = 0)))
          (surfacePotential 3) : ℕ∞) :=
      fun r s₁ s₀ => sector_rank_le_nullity (by norm_num) s₁.isLt s₀.isLt
    calc (∑ r : Fin 3, ∑ s₁ : Fin 2, ∑ s₀ : Fin 2, Cardinal.toENat (Module.rank ℂ
          (boundedJacobiSector 3 (r : ℕ) (s₁ : ℕ) (s₀ : ℕ))))
        ≤ ∑ r : Fin 3, ∑ s₁ : Fin 2, ∑ s₀ : Fin 2,
            (diskWeakNullity (mixedCharacterDomain 3 (r : ℕ)
                (decide ((s₁ : ℕ) = 0)) (decide ((s₀ : ℕ) = 0)))
              (surfacePotential 3) : ℕ∞) :=
          Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s₁ _ =>
            Finset.sum_le_sum fun s₀ _ => hb r s₁ s₀
      _ = 3 := by
          -- the twelve values
          have hNN0 : diskWeakNullity (mixedCharacterDomain 3 0 true true)
              (surfacePotential 3) = 0 := by
            simpa using pureSector_neumann_nullity 0 (by norm_num)
          have hNN1 : diskWeakNullity (mixedCharacterDomain 3 1 true true)
              (surfacePotential 3) = 1 := by
            simpa using pureSector_neumann_nullity 1 (by norm_num)
          have hNN2 : diskWeakNullity (mixedCharacterDomain 3 2 true true)
              (surfacePotential 3) = 1 := by
            simpa using pureSector_neumann_nullity 2 (by norm_num)
          have hDD0 : diskWeakNullity (mixedCharacterDomain 3 0 false false)
              (surfacePotential 3) = 1 := by
            simpa using pureSector_dirichlet_nullity 0 (by norm_num)
          have hDD1 : diskWeakNullity (mixedCharacterDomain 3 1 false false)
              (surfacePotential 3) = 0 := by
            simpa using pureSector_dirichlet_nullity 1 (by norm_num)
          have hDD2 : diskWeakNullity (mixedCharacterDomain 3 2 false false)
              (surfacePotential 3) = 0 := by
            simpa using pureSector_dirichlet_nullity 2 (by norm_num)
          have hND : ∀ r : ℕ, r < 3 → diskWeakNullity (mixedCharacterDomain 3 r true false)
              (surfacePotential 3) = 0 := fun r hr =>
            zaremba_nullity_zero_edge_uncond (by norm_num) (by omega) (by decide)
          have hDN : ∀ r : ℕ, r < 3 → diskWeakNullity (mixedCharacterDomain 3 r false true)
              (surfacePotential 3) = 0 := fun r hr =>
            zaremba_nullity_zero_edge_uncond (by norm_num) (by omega) (by decide)
          simp only [Fin.sum_univ_three, Fin.sum_univ_two, Fin.val_zero, Fin.val_one,
            Fin.val_two]
          norm_num [hNN0, hNN1, hNN2, hDD0, hDD1, hDD2,
            hND 0 (by norm_num), hND 1 (by norm_num), hND 2 (by norm_num),
            hDN 0 (by norm_num), hDN 1 (by norm_num), hDN 2 (by norm_num)]
  · -- lower bound: the three translation fields
    exact KsIndex.JacobiFamily.three_le_nulSurface 3 2 (by norm_num)

end KsIndex.NullityDecomp
