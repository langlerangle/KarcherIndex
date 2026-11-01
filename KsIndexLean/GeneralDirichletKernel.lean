module

public import KsIndexLean.GeneralCharacterTestExtension
public import KsIndexLean.ExplicitModeJacobi
public import KsIndexLean.GroundStateWeakKernel

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.ModeDiag KsIndex.WeakH1 KsIndex.Radial KsIndex.JacobiMode KsIndex.FormIndex

def radialDirichletH1 {k : ℕ} (hk : 2 ≤ k) : ComplexH1 :=
  globalSmoothH1 (modeU k 0) (modeU_contDiff (by omega) 0)

lemma radialDirichletH1_trace {k : ℕ} (hk : 2 ≤ k) :
    diskTraceCLM (radialDirichletH1 hk) = 0 := by
  apply Lp.ext
  filter_upwards [globalSmoothH1_trace (modeU k 0) (modeU_contDiff (by omega) 0),
    Lp.coeFn_zero ℂ 2 circleMeasure] with w hw hz
  change diskTraceCLM (globalSmoothH1 _ _) w = _
  have hw1 : ‖(w : ℂ)‖ = 1 := by simpa only [Circle₁, Metric.mem_sphere, dist_zero_right] using w.property
  rw [hw, hz, modeU, hw1, gRad_zero_one hk]
  simp

lemma radialDirichletH1_rotation {k : ℕ} (hk : 2 ≤ k) (θ : ℝ) :
    diskRotation θ (radialDirichletH1 hk) = radialDirichletH1 hk := by
  have h : radialDirichletH1 hk ∈ weakCharacterDomain θ 1 := by
    apply weakCharacter_of_value_eq _ _ _ (globalSmoothH1_value _ _)
    intro z
    simp only [modeU, pow_zero, mul_one, (planeRotation θ).norm_map, one_mul]
  simpa only [one_smul] using (mem_weakCharacterDomain _ _ _).mp h

lemma radialDirichletH1_weak {k : ℕ} (hk : 2 ≤ k)
    (v : ComplexH1) (hv : v ∈ zeroTraceDomain Set.univ) :
    weakJacobi (surfacePotential k) (radialDirichletH1 hk) v = 0 := by
  let a : ℂ := -((kap k : ℝ) ^ 2 : ℝ)
  have hF : ((a • circleOneL2 : Lp ℂ 2 circleMeasure) : Circle₁ → ℂ) =ᵐ[circleMeasure]
      fun w => fderiv ℝ (modeU k 0) w w := by
    filter_upwards [Lp.coeFn_smul a circleOneL2,
      (MemLp.coeFn_toLp (memLp_const (1 : ℂ)))] with w hw ho
    rw [hw]
    change a * circleOneL2 w = _
    change circleOneL2 w = 1 at ho
    have hw1 : ‖(w : ℂ)‖ = 1 := by simpa only [Circle₁, Metric.mem_sphere, dist_zero_right] using w.property
    rw [ho, mul_one, modeU_normal hk 0 hw1]
    simp [a]
  rw [show weakJacobi (surfacePotential k) (radialDirichletH1 hk) v =
      inner ℂ (a • circleOneL2) (diskTraceCLM v) from
    smooth_weak_green_of_flux _ _ (modeU_contDiff (by omega) 0)
      (fun w _ => modeU_jacobi hk 0 w) _ hF v,
    (mem_fullZeroTrace_iff v).mp hv, inner_zero_right]

lemma radialDirichletH1_ne_zero {k : ℕ} (hk : 2 ≤ k) :
    radialDirichletH1 hk ≠ 0 := by
  intro hz
  have he := globalSmoothH1_value (modeU k 0) (modeU_contDiff (by omega) 0)
  change valueCLM (radialDirichletH1 hk) =ᵐ[volume.restrict (disk : Set ℂ)] modeU k 0 at he
  rw [hz, map_zero] at he
  have ha : modeU k 0 =ᵐ[volume.restrict (disk : Set ℂ)] (fun _ => 0) :=
    he.symm.trans (Lp.coeFn_zero ℂ 2 _)
  have hp := Measure.eqOn_open_of_ae_eq ha Metric.isOpen_ball
    (modeU_contDiff (by omega) 0).continuous.continuousOn continuousOn_const
    (by simp [disk] : (0 : ℂ) ∈ (disk : Set ℂ))
  have hpow : 2 * k - 2 ≠ 0 := by omega
  simp [modeU, gRad, kap, hpow] at hp
  have hkreal : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hpR := congrArg Complex.re hp
  simp at hpR
  linarith

/-- General-k full Dirichlet weak kernel classification by an explicit radial field. -/
lemma generalDirichlet_kernel_span {k : ℕ} (hk : 2 ≤ k) (u : ComplexH1)
    (hu : u ∈ zeroTraceDomain Set.univ)
    (hQ : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v = 0) :
    ∃ c : ℂ, u = c • radialDirichletH1 hk := by
  simpa only [radialDirichletH1] using
    KsIndex.GroundState.fullDirichlet_kernel_span_ground_state hk u hu hQ

lemma generalDirichlet_character_kernel_zero {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (hj : zeta k ^ j ≠ 1) (u : ComplexH1)
    (hu : u ∈ zeroTraceDomain Set.univ ⊓ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v ∈ zeroTraceDomain Set.univ ⊓ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j),
      weakJacobi (surfacePotential k) u v = 0) : u = 0 := by
  obtain ⟨c, hc⟩ := generalDirichlet_kernel_span hk u hu.1
    (generalDirichlet_character_tests_extend (by omega) j u hu.2 hQ)
  have he := (mem_weakCharacterDomain _ _ u).mp hu.2
  have hrot : diskRotation (-(2 * Real.pi) / k) u = u := by
    rw [hc, map_smul, radialDirichletH1_rotation]
  rw [hrot] at he
  have hz : (1 - zeta k ^ j) • u = 0 := by
    rw [sub_smul, one_smul, ← he, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm hj))

end KsIndex.Trace
