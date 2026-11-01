module

public import KsIndexLean.LocalReflectedJacobi

@[expose] public section


/-! Pure-boundary weak kernel vectors lift to actual bounded Jacobi chain
fields. Their copy-zero values recover the original Sobolev representative. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Surface KsIndex.JacobiFamily KsIndex.JacobiFields KsIndex.FormIndex

/-- The local reflected-field constructor preserves copy zero on the open disk. -/
lemma localReflectedJacobi_copy_zero {k : ℕ} (hk : 2 ≤ k) (m : ℕ) (ε : ℂ)
    (hε : ε = 1 ∨ ε = -1) (f : ℂ → ℂ)
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) f (Metric.ball 0 2))
    (hf : ∀ w ∈ seamDomain Set.univ isOpen_univ, f (Bracket.σ w) = ε * f w)
    (hb : ∃ C : ℝ, ∀ w ∈ Metric.closedBall (0 : ℂ) 1, ‖f w‖ ≤ C)
    (hP : ∀ w ∈ (Surface.disk : Set ℂ), laplacian f w + (potV k w : ℂ) * f w = 0) :
    EqOn ((localReflectedJacobi hk m ε hε f hsm hf hb hP).val 0) f (WeakH1.disk : Set ℂ) := by
  intro w hw
  change punc0 k (symFam m ε f) 0 w = f w
  rw [punc0_of_notMem k _ 0 (punctures_notMem_disk (by omega) hw)]
  exact symFam_zero_copy (le_of_lt (by simpa only [dist_zero_right] using Metric.mem_ball.mp hw))

/-- Every pure Dirichlet weak kernel vector is represented by a bounded
Jacobi field on every finite cyclic chain. -/
theorem dirichlet_radical_bounded_chain {k : ℕ} (hk : 2 ≤ k) (j m : ℕ)
    (u : ComplexH1) (hzero : u ∈ zeroTraceDomain Set.univ)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ ⊓
      weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) →
      weakJacobi (surfacePotential k) u v = 0) :
    ∃ W : BoundedJacobi k m,
      valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] W.val 0 := by
  obtain ⟨f, hsm, ha, hP, hb, hf, _⟩ := dirichlet_radical_reflected_disk hk j u hzero hu hQ
  have hr : ∀ w ∈ seamDomain Set.univ isOpen_univ, f (Bracket.σ w) = (-1 : ℂ) * f w := by
    simpa only [neg_one_mul] using hf
  have hp : ∀ w ∈ (Surface.disk : Set ℂ), laplacian f w + (potV k w : ℂ) * f w = 0 :=
    fun w hw => hP w (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hw)
  refine ⟨localReflectedJacobi hk m (-1) (Or.inr rfl) f hsm hr hb hp, ?_⟩
  filter_upwards [ha, ae_restrict_mem WeakH1.disk.isOpen.measurableSet] with w hw hd
  exact hw.trans (localReflectedJacobi_copy_zero hk m (-1) (Or.inr rfl) f hsm hr hb hp hd).symm

/-- Every pure Neumann weak kernel vector is represented by a bounded
Jacobi field on every finite cyclic chain. -/
theorem neumann_radical_bounded_chain {k : ℕ} (hk : 2 ≤ k) (j m : ℕ)
    (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v : ComplexH1, v ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) →
      weakJacobi (surfacePotential k) u v = 0) :
    ∃ W : BoundedJacobi k m,
      valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] W.val 0 := by
  obtain ⟨f, hsm, ha, hP, hb, hf, _⟩ := neumann_radical_reflected_disk hk j u hu hQ
  have hr : ∀ w ∈ seamDomain Set.univ isOpen_univ, f (Bracket.σ w) = (1 : ℂ) * f w := by
    simpa only [one_mul] using hf
  have hp : ∀ w ∈ (Surface.disk : Set ℂ), laplacian f w + (potV k w : ℂ) * f w = 0 :=
    fun w hw => hP w (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hw)
  refine ⟨localReflectedJacobi hk m 1 (Or.inl rfl) f hsm hr hb hp, ?_⟩
  filter_upwards [ha, ae_restrict_mem WeakH1.disk.isOpen.measurableSet] with w hw hd
  exact hw.trans (localReflectedJacobi_copy_zero hk m 1 (Or.inl rfl) f hsm hr hb hp hd).symm

end KsIndex.Trace
