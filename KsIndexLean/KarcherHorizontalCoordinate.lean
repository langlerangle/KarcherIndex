module

public import KsIndexLean.KarcherRealDifferential

@[expose] public section


/-! The horizontal EW coordinate as a real differentiable function on the
finite parameter plane away from its punctures. -/
noncomputable section
namespace KsIndex.KarcherData
open Complex

/-- The second coordinate of the descended integral, extended by zero at the
punctures solely to give a function on the ambient parameter plane. -/
def horizontalY {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k) (z : ℂ) : ℝ := by
  classical
  exact if hz : z ∉ Surface.punctures k then (descendedIntegral hk b ⟨z, hz⟩).2.1 else 0

lemma horizontalY_eq {k : ℕ} (hk : 2 ≤ k) (b w : PuncturedPlane k) :
    horizontalY hk b w.val = (descendedIntegral hk b w).2.1 := by
  rcases w with ⟨w, hw⟩
  simp [horizontalY, hw]

lemma hasFDerivAt_horizontalY {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k)
    {w : ℂ} (hw : w ∉ Surface.punctures k) :
    HasFDerivAt (horizontalY hk b) (realCoeffLinear (coeff2 k w)) w := by
  obtain ⟨r, hr, F₁, F₂, F₃, _, _, _, _, h₂, _, hrepr⟩ :=
    exists_local_primitives hk b ⟨w, hw⟩
  have hd := (Complex.reCLM.hasFDerivAt.comp w
    ((h₂ w (Metric.mem_ball_self hr)).hasFDerivAt.restrictScalars ℝ)).const_add
      (descendedIntegral hk b ⟨w, hw⟩).2.1
  apply hd.congr_of_eventuallyEq
  have hclosed : IsClosed (Surface.punctures k) :=
    isClosed_eq (continuous_id.pow (2 * k)) continuous_const
  have hn : ∀ᶠ z in nhds w, z ∉ Surface.punctures k := hclosed.isOpen_compl.mem_nhds hw
  filter_upwards [hn, Metric.ball_mem_nhds w hr] with z hz hzr
  have he := congrArg (fun p => p.2.1) (hrepr ⟨z, hz⟩ hzr)
  simpa [horizontalY, hz, projectPeriod] using he

end KsIndex.KarcherData
