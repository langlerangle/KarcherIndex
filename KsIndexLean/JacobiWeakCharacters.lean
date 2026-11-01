module

public import KsIndexLean.HorizontalWeakGreen

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.JacobiFields KsIndex.FormIndex

lemma horizontal_rotation (k : ℕ) (θ : ℝ) (w : ℂ) :
    nu1 k (planeRotation θ w) + Complex.I * nu2 k (planeRotation θ w) =
      Complex.exp (θ * Complex.I) ^ (k - 1) * (nu1 k w + Complex.I * nu2 k w) := by
  rw [horizontal_formula, horizontal_formula, (planeRotation θ).norm_map,
    planeRotation_apply, mul_pow]
  ring

lemma negative_rotation_eq_xi (k : ℕ) :
    Complex.exp (((-(2 * Real.pi) / k : ℝ) : ℂ) * Complex.I) = xi k := by
  unfold xi zeta
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp only [map_div₀, map_mul, map_ofNat, map_natCast, Complex.conj_ofReal, Complex.conj_I]
  ring

lemma xi_pow_pred (k : ℕ) (hk : 0 < k) : xi k ^ (k - 1) = zeta k := by
  calc
    xi k ^ (k - 1) = (zeta k * xi k) * xi k ^ (k - 1) := by
      rw [zeta_mul_xi hk, one_mul]
    _ = zeta k * xi k ^ k := by
      rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k)]
    _ = zeta k := by rw [xi_pow_N hk, mul_one]

/-- Positive horizontal frequency k-1 is paper character one under negative rotation. -/
lemma horizontalH1_character_one (k : ℕ) (hk : 2 ≤ k) :
    horizontalH1 k hk ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ 1) := by
  apply weakCharacter_of_value_eq _ _ _ (globalSmoothH1_value _ _)
  intro w
  rw [horizontal_rotation, negative_rotation_eq_xi, xi_pow_pred k (by omega), pow_one]

lemma verticalThree_rotation (θ : ℝ) (w : ℂ) :
    nu3 3 (planeRotation θ w) = nu3 3 w := by
  simp only [nu3, (planeRotation θ).norm_map]

lemma horizontalThree_rotation (θ : ℝ) (w : ℂ) :
    nu1 3 (planeRotation θ w) + Complex.I * nu2 3 (planeRotation θ w) =
      Complex.exp (θ * Complex.I) ^ 2 * (nu1 3 w + Complex.I * nu2 3 w) := by
  rw [horizontal_three_formula, horizontal_three_formula, (planeRotation θ).norm_map,
    planeRotation_apply, mul_pow]
  ring

lemma third_negative_rotation_eq_xi :
    Complex.exp (((-(2 * Real.pi) / 3 : ℝ) : ℂ) * Complex.I) = xi 3 := by
  unfold xi zeta
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  change (-(2 * (Real.pi : ℂ)) / 3 * Complex.I) =
    (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I / (3 : ℂ))
  apply Complex.ext <;> simp [map_ofNat (starRingEnd ℂ) 2,
    map_ofNat (starRingEnd ℂ) 3]

lemma xi_three_sq : xi 3 ^ 2 = zeta 3 := by
  have h := zeta_mul_xi (N := 3) (by decide)
  have h3 := xi_pow_N (N := 3) (by decide)
  calc
    xi 3 ^ 2 = (zeta 3 * xi 3) * xi 3 ^ 2 := by rw [h, one_mul]
    _ = zeta 3 * xi 3 ^ 3 := by ring
    _ = zeta 3 := by rw [h3, mul_one]

lemma conj_zeta_three : (starRingEnd ℂ) (zeta 3) = zeta 3 ^ 2 := by
  have h := zeta_mul_xi (N := 3) (by decide)
  have h3 := zeta_pow_N (N := 3) (by decide)
  change xi 3 = zeta 3 ^ 2
  calc
    xi 3 = zeta 3 ^ 3 * xi 3 := by rw [h3, one_mul]
    _ = zeta 3 ^ 2 * (zeta 3 * xi 3) := by ring
    _ = zeta 3 ^ 2 := by rw [h, mul_one]

lemma verticalThreeH1_character_zero :
    verticalThreeH1 ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (zeta 3 ^ 0) := by
  apply weakCharacter_of_value_eq _ _ _ verticalThreeH1_value
  intro w
  rw [pow_zero, one_mul]
  exact verticalThree_rotation _ _

lemma horizontalThreeH1_character_one :
    horizontalThreeH1 ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (zeta 3 ^ 1) := by
  apply weakCharacter_of_value_eq _ _ _ (globalSmoothH1_value _ _)
  intro w
  rw [horizontalThree_rotation, third_negative_rotation_eq_xi, xi_three_sq, pow_one]

lemma horizontalThreeConjH1_character_two :
    horizontalThreeConjH1 ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (zeta 3 ^ 2) := by
  apply weakCharacter_of_value_eq _ _ _ (globalSmoothH1_value _ _)
  intro w
  rw [horizontalThree_rotation, third_negative_rotation_eq_xi, xi_three_sq, map_mul,
    conj_zeta_three]

/-- The antisymmetric vertical pair belongs to the actual Dirichlet character-zero domain. -/
lemma verticalThree_pair_Dirichlet_character :
    (verticalThreeH1, -verticalThreeH1) ∈
      KsIndex.Spectral.paperSlitDirichletCharacterDomain 0 := by
  constructor
  · exact ⟨⟨mem_transmission_of_zero 1 (verticalThreeH1_zeroTrace _)
        ((zeroTraceDomain _).neg_mem (verticalThreeH1_zeroTrace _)),
      verticalThreeH1_zeroTrace _⟩,
      (zeroTraceDomain _).neg_mem (verticalThreeH1_zeroTrace _)⟩
  · apply (KsIndex.Spectral.mem_pairCharacterDomain_iff _ _ _).mpr
    exact ⟨verticalThreeH1_character_zero,
      (weakCharacterDomain _ _).neg_mem verticalThreeH1_character_zero⟩

lemma horizontalThree_pair_Neumann_character :
    (horizontalThreeH1, horizontalThreeH1) ∈
      KsIndex.Spectral.paperSlitNeumannCharacterDomain 1 := by
  constructor
  · apply (mem_transmissionDomain _ _ _).mpr
    exact (one_smul ℂ _).symm
  · apply (KsIndex.Spectral.mem_pairCharacterDomain_iff _ _ _).mpr
    exact ⟨horizontalThreeH1_character_one, horizontalThreeH1_character_one⟩

lemma horizontalThreeConj_pair_Neumann_character :
    (horizontalThreeConjH1, horizontalThreeConjH1) ∈
      KsIndex.Spectral.paperSlitNeumannCharacterDomain 2 := by
  constructor
  · apply (mem_transmissionDomain _ _ _).mpr
    exact (one_smul ℂ _).symm
  · apply (KsIndex.Spectral.mem_pairCharacterDomain_iff _ _ _).mpr
    exact ⟨horizontalThreeConjH1_character_two, horizontalThreeConjH1_character_two⟩

end KsIndex.Trace
