module

public import KsIndexLean.PureRadicalChainLift
public import KsIndexLean.NullityRadical

@[expose] public section


/-! Period and symmetry identities for normalized reflected chain fields. -/
noncomputable section
open Set
namespace KsIndex.JacobiFamily
open KsIndex.Surface KsIndex.SurfaceSym KsIndex.SurfaceForm KsIndex.Trace KsIndex.WeakH1 KsIndex.FormIndex

lemma normalized_symFam_period {k m : ℕ} (ε : ℂ) (f : ℂ → ℂ)
    (n : ZMod (2 * m)) (w : ℂ) :
    punc0 k (symFam m ε f) (n + 2) w = punc0 k (symFam m ε f) n w := by
  have hp : parity m (n + 2) = parity m n := by
    rw [show (2 : ZMod (2 * m)) = 1 + 1 from by ring, map_add, map_add, map_one]
    rw [show (1 : ZMod 2) + 1 = 0 from by decide, add_zero]
  by_cases hw : w ∈ punctures k
  · simp only [punc0_of_mem k _ _ hw]
  · simp only [punc0_of_notMem k _ _ hw, symFam, hp]

lemma normalized_symFam_reflection {k m : ℕ} {ε : ℂ} (hε : ε = 1 ∨ ε = -1)
    (f : ℂ → ℂ) (c : ZMod (2 * m)) (hc : parity m c = 1)
    (n : ZMod (2 * m)) (w : ℂ) :
    punc0 k (symFam m ε f) (c - n) w = ε * punc0 k (symFam m ε f) n w := by
  have hp : (parity m (c - n)).val = 1 - (parity m n).val := by
    rw [map_sub, hc]
    generalize parity m n = x
    revert x
    decide
  have he : ε ^ (1 - (parity m n).val) = ε * ε ^ (parity m n).val := by
    have hh := parity_val_lt_two m n
    generalize (parity m n).val = v at *
    interval_cases v <;> rcases hε with rfl | rfl <;> norm_num
  by_cases hw : w ∈ punctures k
  · simp only [punc0_of_mem k _ _ hw, mul_zero]
  · simp only [punc0_of_notMem k _ _ hw, symFam, hp, he, mul_assoc]

lemma normalized_symFam_rotation {k m : ℕ} (ε : ℂ) (f : ℂ → ℂ) {a d : ℂ}
    (ha : ‖a‖ = 1) (hak : a ^ (2 * k) = 1)
    (hf : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, f (a * w) = d * f w)
    (n : ZMod (2 * m)) (w : ℂ) :
    punc0 k (symFam m ε f) n (a * w) = d * punc0 k (symFam m ε f) n w := by
  have hp : a * w ∈ punctures k ↔ w ∈ punctures k := by
    simp only [punctures, Set.mem_ofPred_eq, mul_pow, hak, one_mul]
  have hn : ‖a * w‖ = ‖w‖ := by rw [norm_mul, ha, one_mul]
  by_cases hw : w ∈ punctures k
  · simp only [punc0_of_mem k _ _ hw, punc0_of_mem k _ _ (hp.mpr hw), mul_zero]
  · rw [punc0_of_notMem k _ _ hw, punc0_of_notMem k _ _ (fun h => hw (hp.mp h))]
    by_cases hle : ‖w‖ ≤ 1
    · rw [symFam_of_le n hle, symFam_of_le n (hn ▸ hle),
        hf w (by simpa only [Metric.mem_closedBall, dist_zero_right] using hle)]
      ring
    · simp only [symFam, cutD, hn, ite_eq_right hle, mul_zero]

/-- The constructed field has exactly the prescribed joint rotation/reflection character. -/
theorem localReflectedJacobi_sector {k r s : ℕ} (hk : 2 ≤ k) (hs : s < 2)
    (f : ℂ → ℂ) (hsm : ContDiffOn ℝ (⊤ : ℕ∞) f (Metric.ball 0 2))
    (hf : ∀ w ∈ seamDomain Set.univ isOpen_univ, f (Bracket.σ w) = zeta 2 ^ s * f w)
    (hb : ∃ C : ℝ, ∀ w ∈ Metric.closedBall (0 : ℂ) 1, ‖f w‖ ≤ C)
    (hP : ∀ w ∈ (Surface.disk : Set ℂ), laplacian f w + (potV k w : ℂ) * f w = 0)
    (hr : ∀ w ∈ Metric.closedBall (0 : ℂ) 1,
      f (planeRotation (-(2 * Real.pi) / k) w) = (zeta k ^ r) * f w) :
    let hε : zeta 2 ^ s = 1 ∨ zeta 2 ^ s = -1 := by
      interval_cases s <;> simp [Bracket.zeta_two]
    uncurryE 2 (localReflectedJacobi hk 2 (zeta 2 ^ s) hε f hsm hf hb hP).val ∈
      NullityDecomp.boundedJacobiSector k r s s := by
  dsimp only
  let hε : zeta 2 ^ s = 1 ∨ zeta 2 ^ s = -1 := by
    interval_cases s <;> simp [Bracket.zeta_two]
  let W := localReflectedJacobi hk 2 (zeta 2 ^ s) hε f hsm hf hb hP
  change uncurryE 2 W.val ∈ NullityDecomp.boundedJacobiSector k r s s
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact ⟨W.val, W.property, rfl⟩
  · apply Module.End.mem_eigenspace_iff.mpr
    funext p
    change punc0 k (symFam 2 (zeta 2 ^ s) f) p.1 ((rotUnit k : ℂ) * p.2) =
      (zeta k ^ r) * punc0 k (symFam 2 (zeta 2 ^ s) f) p.1 p.2
    apply normalized_symFam_rotation _ _ (Circle.norm_coe _) ?_ ?_
    · rw [show 2 * k = k * 2 from by omega, pow_mul, rotUnit_pow (by omega), one_pow]
    · intro w hw
      simpa only [planeRotation_apply, rotUnit, Circle.coe_exp] using hr w hw
  · apply Module.End.mem_eigenspace_iff.mpr
    funext p
    exact normalized_symFam_reflection hε f 1 (by simp) p.1 p.2
  · apply Module.End.mem_eigenspace_iff.mpr
    funext p
    exact normalized_symFam_reflection hε f (-1) (by rw [map_neg, map_one]; decide) p.1 p.2

end KsIndex.JacobiFamily
