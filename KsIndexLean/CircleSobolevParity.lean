module

public import KsIndexLean.CircleSobolevMultiplier

@[expose] public section


/-! Bounded residue projections on every real-order Fourier Sobolev space.
The two classes `1 + 6ℤ` and `4 + 6ℤ` split the class `1 + 3ℤ`.
Character indices use the convention `-j + kℤ`. -/
noncomputable section
namespace KsIndex.CircleSobolev
open Classical

/-- Bounded coordinate projection onto the residue class `-j + kℤ`. -/
def residueProjection (s : ℝ) (j k : ℤ) : Space s →L[ℂ] Space s :=
  multiplierCLM (fun n => if ∃ m : ℤ, n = -j + k * m then 1 else 0)
    (show (0 : ℝ) ≤ 1 by norm_num) (by
      intro n
      split_ifs <;> simp [le_of_lt (weight_pos s n)])

lemma coeff_residueProjection (s : ℝ) (j k : ℤ) (u : Space s) (n : ℤ) :
    coeff s (residueProjection s j k u) n =
      if ∃ m : ℤ, n = -j + k * m then coeff s u n else 0 := by
  simp only [residueProjection, multiplierCLM, LinearMap.mkContinuous_apply]
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [coeff_multiplier]
  split_ifs <;> simp

lemma residueProjection_mem (s : ℝ) (j k : ℤ) (u : Space s) :
    residueProjection s j k u ∈ character s j k := by
  rw [mem_character]
  intro n hn
  rw [coeff_residueProjection, ite_eq_right hn]

/-- Every vector supported on `1 + 3ℤ` is the sum of its two parity projections. -/
lemma parity_decomposition (s : ℝ) (u : Space s)
    (hu : u ∈ character s 2 3) :
    residueProjection s (-1) 6 u + residueProjection s 2 6 u = u := by
  apply coeff_injective s
  funext n
  change coeffLinear s n (_ + _) = coeffLinear s n u
  rw [map_add]
  change coeff s (residueProjection s (-1) 6 u) n +
    coeff s (residueProjection s 2 6 u) n = coeff s u n
  rw [coeff_residueProjection, coeff_residueProjection]
  by_cases hp : ∃ m : ℤ, n = -(-1) + 6 * m
  · have hn : ¬ ∃ m : ℤ, n = -2 + 6 * m := by
      obtain ⟨a, ha⟩ := hp
      rintro ⟨b, hb⟩
      omega
    simp only [ite_eq_left hp, ite_eq_right hn, add_zero]
  · by_cases hn : ∃ m : ℤ, n = -2 + 6 * m
    · simp only [ite_eq_right hp, ite_eq_left hn, zero_add]
    · have hz : coeff s u n = 0 := (mem_character s 2 3 u).mp hu n (by
        rintro ⟨m, hm⟩
        have : m % 2 = 0 ∨ m % 2 = 1 := by omega
        rcases this with he | he
        · apply hn; refine ⟨m / 2, ?_⟩; omega
        · apply hp; refine ⟨m / 2, ?_⟩; omega)
      simp only [ite_eq_right hp, ite_eq_right hn, hz, add_zero]

/-- The two parity subspaces have trivial intersection at every real order. -/
lemma parity_characters_disjoint (s : ℝ) :
    Disjoint (character s (-1) 6) (character s 2 6) := by
  rw [Submodule.disjoint_def]
  intro u hp hn
  apply coeff_injective s
  funext n
  have hz : coeff s (0 : Space s) n = 0 := by simp [coeff]
  rw [hz]
  by_cases h : ∃ m : ℤ, n = -(-1) + 6 * m
  · apply (mem_character s 2 6 u).mp hn n
    obtain ⟨a, ha⟩ := h
    rintro ⟨b, hb⟩
    omega
  · exact (mem_character s (-1) 6 u).mp hp n h

/-- The two parity subspaces span the parent character space. Together with
`parity_characters_disjoint`, this gives its internal direct-sum decomposition. -/
lemma parity_characters_sup (s : ℝ) :
    character s (-1) 6 ⊔ character s 2 6 = character s 2 3 := by
  apply le_antisymm
  · apply sup_le
    · intro u hu
      rw [mem_character] at hu ⊢
      intro n hn
      apply hu n
      rintro ⟨a, ha⟩
      apply hn
      exact ⟨2 * a + 1, by omega⟩
    · intro u hu
      rw [mem_character] at hu ⊢
      intro n hn
      apply hu n
      rintro ⟨a, ha⟩
      apply hn
      exact ⟨2 * a, by omega⟩
  · intro u hu
    rw [← parity_decomposition s u hu]
    exact Submodule.add_mem_sup (residueProjection_mem s (-1) 6 u)
      (residueProjection_mem s 2 6 u)

end KsIndex.CircleSobolev
