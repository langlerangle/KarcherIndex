module

public import KsIndexLean.AlphaSignedWindowBudget

@[expose] public section


/-! Index the 2046 signed middle modes in the order used by the optional
arithmetic certificates. No numerical enclosure is assumed to be verified here. -/
namespace KsIndex.AlphaRemarkTrial
open CircleQ AlphaResidual

/-- Certificate row order: +3, -3, +4, -4, ..., +1025, -1025. -/
def middleMode (i : Fin 2046) : ℤ :=
  if i.val % 2 = 0 then (i.val / 2 + 3 : ℕ) else -((i.val / 2 + 3 : ℕ) : ℤ)

theorem middleMode_injective : Function.Injective middleMode := by
  intro i j hij
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  simp only [middleMode] at hij
  split_ifs at hij <;> omega

theorem middleMode_mem (i : Fin 2046) :
    middleMode i ∈ residualWindow 1025 \ residualWindow 2 := by
  rw [mem_middleWindow]
  have hi := i.isLt
  simp only [middleMode]
  split_ifs
  · rw [abs_of_nonneg (by positivity)]
    omega
  · rw [abs_neg, abs_of_nonneg (by positivity)]
    omega

theorem middleMode_image :
    Finset.univ.image middleMode = residualWindow 1025 \ residualWindow 2 := by
  ext n
  constructor
  · intro hn
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
    exact middleMode_mem i
  · intro hn
    rw [mem_middleWindow] at hn
    by_cases hp : 0 ≤ n
    · rw [abs_of_nonneg hp] at hn
      have hidx : 2 * (n.toNat - 3) < 2046 := by omega
      apply Finset.mem_image.mpr
      refine ⟨⟨2 * (n.toNat - 3), hidx⟩, Finset.mem_univ _, ?_⟩
      simp only [middleMode]
      split_ifs <;> omega
    · rw [abs_of_neg (lt_of_not_ge hp)] at hn
      have hidx : 2 * ((-n).toNat - 3) + 1 < 2046 := by omega
      apply Finset.mem_image.mpr
      refine ⟨⟨2 * ((-n).toNat - 3) + 1, hidx⟩, Finset.mem_univ _, ?_⟩
      simp only [middleMode]
      split_ifs <;> omega

theorem middleWindow_sum (f : ℤ → ℝ) :
    (∑ n ∈ residualWindow 1025 \ residualWindow 2, f n) =
      ∑ i : Fin 2046, f (middleMode i) := by
  rw [← middleMode_image]
  exact Finset.sum_image (fun i _ j _ hij => middleMode_injective hij)

/-- Convert indexed signed enclosures and rational arithmetic to an actual
middle-window energy bound. The enclosure hypothesis remains essential. -/
theorem middleWindow_bound_of_indexed (lo hi e : Fin 2046 → ℚ) (B : ℚ)
    (hencloses : ∀ i, (lo i : ℝ) ≤ realResidual AlphaRemark.spectralUpper (middleMode i) ∧
      realResidual AlphaRemark.spectralUpper (middleMode i) ≤ (hi i : ℝ))
    (hrow : ∀ i, signedIntervalRadius (lo i) (hi i)^2 /
      residualWeightRat (middleMode i) ≤ e i)
    (hsum : ∑ i, e i ≤ B) :
    (∑ n ∈ residualWindow 1025 \ residualWindow 2,
      realResidual AlphaRemark.spectralUpper n ^ 2 / residualWeight n) ≤ (B : ℝ) := by
  rw [middleWindow_sum]
  have hpoint (i : Fin 2046) :
      realResidual AlphaRemark.spectralUpper (middleMode i)^2 /
        residualWeight (middleMode i) ≤ (e i : ℝ) := by
    have habs := signedIntervalRadius_bounds (lo i) (hi i) _
      (hencloses i).1 (hencloses i).2
    have hnonneg : (0 : ℝ) ≤ signedIntervalRadius (lo i) (hi i) :=
      (abs_nonneg _).trans habs
    have hs := (sq_le_sq₀ (abs_nonneg _) hnonneg).mpr habs
    rw [sq_abs] at hs
    have hr : (signedIntervalRadius (lo i) (hi i) : ℝ)^2 /
        residualWeight (middleMode i) ≤ (e i : ℝ) := by
      rw [← residualWeightRat_cast]
      exact_mod_cast hrow i
    exact (div_le_div_of_nonneg_right hs (residualWeight_pos _).le).trans hr
  exact (Finset.sum_le_sum (fun i _ => hpoint i)).trans (by exact_mod_cast hsum)

/-- The existing certificates use 63 blocks of 32 rows and a final block of 30. -/
def middleBlockLength (b : Fin 64) : ℕ := if b.val = 63 then 30 else 32

abbrev MiddleBlockRow := (b : Fin 64) × Fin (middleBlockLength b)

def middleBlockIndex (r : MiddleBlockRow) : Fin 2046 :=
  ⟨32 * r.1.val + r.2.val, by
    have hb := r.1.isLt
    have hi := r.2.isLt
    simp only [middleBlockLength] at hi
    split_ifs at hi <;> omega⟩

theorem middleBlockIndex_bijective : Function.Bijective middleBlockIndex := by
  constructor
  · intro r s h
    have hr := r.2.isLt
    have hs := s.2.isLt
    have he := congrArg Fin.val h
    simp only [middleBlockIndex] at he
    have hr32 : r.2.val < 32 := by
      simp only [middleBlockLength] at hr
      split_ifs at hr <;> omega
    have hs32 : s.2.val < 32 := by
      simp only [middleBlockLength] at hs
      split_ifs at hs <;> omega
    have hb : r.1 = s.1 := Fin.ext (by omega)
    cases r with
    | mk b i =>
      cases s with
      | mk c j =>
        dsimp at hb
        subst c
        have hij : i = j := Fin.ext (by dsimp at he; omega)
        subst j
        rfl
  · intro i
    let b : Fin 64 := ⟨i.val / 32, by have hi := i.isLt; omega⟩
    have hj : i.val % 32 < middleBlockLength b := by
      have hi := i.isLt
      simp only [middleBlockLength, b]
      split_ifs <;> omega
    refine ⟨⟨b, ⟨i.val % 32, hj⟩⟩, ?_⟩
    apply Fin.ext
    simp only [middleBlockIndex, b]
    omega

/-- Exact block partition; no row is omitted or counted twice. -/
theorem middleBlock_sum (f : Fin 2046 → ℝ) :
    (∑ i, f i) = ∑ b : Fin 64, ∑ j : Fin (middleBlockLength b),
      f (middleBlockIndex ⟨b, j⟩) := by
  let e := Equiv.ofBijective middleBlockIndex middleBlockIndex_bijective
  calc
    _ = ∑ r : MiddleBlockRow, f (middleBlockIndex r) :=
      (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
    _ = _ := Fintype.sum_sigma _

end KsIndex.AlphaRemarkTrial

#print axioms KsIndex.AlphaRemarkTrial.middleMode_image
#print axioms KsIndex.AlphaRemarkTrial.middleWindow_bound_of_indexed
