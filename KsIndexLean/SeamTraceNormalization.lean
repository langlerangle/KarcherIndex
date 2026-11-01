module

public import KsIndexLean.WeakEquation

@[expose] public section


/-! The trace representative normalizes redundant receiving-seam values while
preserving smoothness and support of the original model test functions. -/
noncomputable section
open Set Topology
open scoped ContDiff
namespace KsIndex.FaithfulInjection
open Surface SeamNormal
variable {k m : ℕ}

lemma testTrace_seamVal (u : ZMod (2*m) → ℂ → ℂ) : SeamVal k (testTrace k m u) := by
  intro n w hw
  rw [testTrace_giving u hw]
  have he : (n+1-1 : ZMod (2*m)) = n := by ring
  have hr := testTrace_receiving u (n := n+1) (w := w) (by rwa [he])
  simpa only [he] using hr

lemma testTrace_exterior (u : ZMod (2*m) → ℂ → ℂ) (n : ZMod (2*m))
    {w : ℂ} (hw : 1 < ‖w‖) : testTrace k m u n w = 0 := by
  have ha : ∀ i : ZMod (2*m), w ∉ seamArc k m i := by
    intro i hi
    exact (ne_of_gt hw) (norm_eq_one_of_mem_seamArc hi)
  simp only [testTrace, ite_eq_right (not_lt.mpr hw.le), ite_eq_right (ha _)]

lemma testTrace_glue_germ (u : ZMod (2*m) → ℂ → ℂ) (n : ZMod (2*m))
    {w : ℂ} (hw : w ∈ seamArc k m n) :
    glue (testTrace k m u) n =ᶠ[𝓝 w] glue u n := by
  obtain ⟨ε, hε, hnear⟩ := seamArc_openness hw
  filter_upwards [Metric.ball_mem_nhds w hε] with z hz
  by_cases hn : ‖z‖ ≤ 1
  · simp only [glue, ite_eq_left hn]
    rcases lt_or_eq_of_le hn with hl | he
    · exact testTrace_eqOn_disk u n (by simpa [disk, Metric.mem_ball, dist_zero_right] using hl)
    · apply testTrace_giving u
      exact hnear z he (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
  · simp only [glue, ite_eq_right hn]
    apply testTrace_eqOn_disk u (n+1)
    have hl : 1 < ‖z‖ := lt_of_not_ge hn
    have hi : ‖(1:ℂ) / (starRingEnd ℂ) z‖ < 1 := by
      simp only [one_div, norm_inv, Complex.norm_conj]
      exact (inv_lt_one₀ (lt_trans zero_lt_one hl)).mpr hl
    simpa [disk, Metric.mem_ball, dist_zero_right] using hi

lemma testTrace_isSmooth {u : ZMod (2*m) → ℂ → ℂ} (hu : IsSmooth k m u) :
    IsSmooth k m (testTrace k m u) := by
  refine ⟨?_, ?_, fun n w hw => testTrace_exterior u n hw⟩
  · intro n
    exact (hu.1 n).congr (fun w hw => testTrace_eqOn_disk u n hw)
  · intro n w hw
    exact (hu.2.1 n w hw).congr_of_eventuallyEq (testTrace_glue_germ u n hw)

lemma testTrace_suppAwayP {u : ZMod (2*m) → ℂ → ℂ} (hu : SuppAwayP k m u) :
    SuppAwayP k m (testTrace k m u) := by
  obtain ⟨ε, hε, hu⟩ := hu
  refine ⟨ε, hε, ?_⟩
  intro n w hw
  unfold testTrace
  split_ifs <;> first | exact hu _ w hw | rfl

lemma testTrace_mem_CcSmooth {u : ZMod (2*m) → ℂ → ℂ} (hu : u ∈ CcSmooth k m) :
    testTrace k m u ∈ CcSmooth k m :=
  ⟨testTrace_isSmooth hu.1, testTrace_suppAwayP hu.2⟩

/-- Normalization is a linear operation on total-function representatives. -/
def testTraceLinear (k m : ℕ) :
    (ZMod (2*m) → ℂ → ℂ) →ₗ[ℂ] (ZMod (2*m) → ℂ → ℂ) where
  toFun := testTrace k m
  map_add' := by
    intro u v
    funext n w
    simp only [testTrace, Pi.add_apply]
    split_ifs <;> simp
  map_smul' := by
    intro c u
    funext n w
    simp only [testTrace, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

lemma testTrace_fderiv_on_disk (u : ZMod (2*m) → ℂ → ℂ) (n : ZMod (2*m))
    {w : ℂ} (hw : w ∈ disk) :
    fderiv ℝ (testTrace k m u n) w = fderiv ℝ (u n) w := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [Metric.isOpen_ball.mem_nhds hw] with z hz
  exact testTrace_eqOn_disk u n hz

/-- The original model quadratic form ignores the redundant boundary values. -/
lemma testTrace_jacobiQ [NeZero m] (u : ZMod (2*m) → ℂ → ℂ) :
    jacobiQ k m (testTrace k m u) = jacobiQ k m u := by
  unfold jacobiQ
  apply Finset.sum_congr rfl
  intro n hn
  have hd : dirichletG k (testTrace k m u n) = dirichletG k (u n) := by
    apply MeasureTheory.setIntegral_congr_fun Metric.isOpen_ball.measurableSet
    intro w hw
    simp only [gradSq, testTrace_fderiv_on_disk u n hw]
  have hp : potentialG k (testTrace k m u n) = potentialG k (u n) := by
    apply MeasureTheory.setIntegral_congr_fun Metric.isOpen_ball.measurableSet
    intro w hw
    dsimp only
    rw [testTrace_eqOn_disk (k := k) u n hw]
  rw [hd, hp]

/-- A seam-compatible, puncture-normalized representative with zero exterior
is fixed by trace normalization. No smoothness is needed. -/
lemma testTrace_eq_self (u : ZMod (2*m) → ℂ → ℂ) (hs : SeamVal k u)
    (hp : PunctureZero k u) (he : ∀ n w, 1 < ‖w‖ → u n w = 0) :
    testTrace k m u = u := by
  funext n w
  rcases lt_trichotomy ‖w‖ 1 with hw | hw | hw
  · exact testTrace_eqOn_disk u n (by simpa [disk, Metric.mem_ball, dist_zero_right] using hw)
  · by_cases hwp : w ∈ punctures k
    · rw [testTrace_puncture u n hw hwp, hp n w hwp]
    · have harc := SurfaceForm.mem_arc_of_not_puncture hw hwp
      have hpv := SurfaceForm.parity_succ_val m n
      have hlt2 := ZMod.val_lt (parity m n)
      have ha : w ∈ seamArc k m n ∨ w ∈ seamArc k m (n-1) := by
        rw [SurfaceForm.seamArc_pred]
        unfold seamArc
        rw [hpv]
        rcases (by omega : (parity m n).val = 0 ∨ (parity m n).val = 1) with h | h <;>
          rcases harc with h0 | h1 <;> rw [h]
        · exact Or.inr h0
        · exact Or.inl h1
        · exact Or.inl h0
        · exact Or.inr h1
      rcases ha with ha | ha
      · exact testTrace_giving u ha
      · rw [testTrace_receiving u ha]
        have hh := hs (n-1) w ha
        have hi : (n-1+1 : ZMod (2*m)) = n := by ring
        rw [hi] at hh
        exact hh.symm
  · rw [testTrace_exterior u n hw, he n w hw]

end KsIndex.FaithfulInjection
