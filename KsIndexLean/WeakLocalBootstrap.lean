module

public import KsIndexLean.WeakSmoothMultiplier

@[expose] public section


/-! Interior Sobolev bootstrap for a smooth-potential distributional equation.

This proves local membership in every nonnegative integer-order Sobolev space.
Construction of a classical smooth representative is a separate result. The initial local H¹ membership and
localized distributional equation are explicit inputs; their chartwise weak-solution
adapters are separate obligations. The potential here is globally smooth on the
coordinate plane, although the equation itself is only imposed inside `Ω`.
-/
noncomputable section
open scoped SchwartzMap LineDeriv Laplacian
namespace KsIndex.Weq
open TemperedDistribution

/-- Local regularity tested by arbitrary compact smooth multipliers inside the domain. -/
def LocalMemSobolev (Ω : Set ℂ) (s : ℝ) (f : 𝓢'(ℂ, ℂ)) : Prop :=
  ∀ χ : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
    tsupport χ ⊆ Ω → MemSobolev s 2 (smulLeftCLM ℂ χ f)

lemma LocalMemSobolev.mono {Ω : Set ℂ} {s t : ℝ} {f : 𝓢'(ℂ, ℂ)}
    (h : LocalMemSobolev Ω s f) (ht : t ≤ s) : LocalMemSobolev Ω t f := by
  intro χ hχ hc hs
  exact MemSobolev.mono ht (h χ hχ hc hs)

lemma LocalMemSobolev.lineDeriv {Ω : Set ℂ} {s : ℝ} {f : 𝓢'(ℂ, ℂ)}
    (h : LocalMemSobolev Ω (s + 1) f) (d : ℂ) : LocalMemSobolev Ω s (∂_{d} f) := by
  intro χ hχ hc hs
  have hfirst := (h χ hχ hc hs).lineDerivOp (m := d)
  have hd := (h.mono (by linarith)) (fun z => fderiv ℝ χ z d)
    ((contDiff_infty_iff_fderiv.mp hχ).2.clm_apply contDiff_const)
    (hc.fderiv_apply (𝕜 := ℝ) d) ((tsupport_fderiv_apply_subset ℝ d).trans hs)
  have he : smulLeftCLM ℂ χ (∂_{d} f) =
      ∂_{d} (smulLeftCLM ℂ χ f) - smulLeftCLM ℂ (fun z => fderiv ℝ χ z d) f := by
    rw [distribution_lineDeriv_smulLeft hχ hc]; abel
  rw [he]
  have ha : s + 1 - 1 = s := by ring
  rw [ha] at hfirst
  exact hfirst.sub hd

/-- The equation is imposed only after multiplication by tests supported inside `Ω`.
No boundary condition is imposed at the edge of the coordinate domain. -/
def LocalPotentialEquation (Ω : Set ℂ) (V : ℂ → ℂ) (f : 𝓢'(ℂ, ℂ)) : Prop :=
  ∀ χ : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ Ω →
    smulLeftCLM ℂ χ (Δ f) = -smulLeftCLM ℂ (fun z => χ z * V z) f

/-- One interior bootstrap step for a globally smooth coordinate potential. -/
theorem LocalMemSobolev.gain_of_potential {Ω : Set ℂ} {s : ℝ}
    {V : ℂ → ℂ} {f : 𝓢'(ℂ, ℂ)}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (heq : LocalPotentialEquation Ω V f)
    (h : LocalMemSobolev Ω (s + 1) f) : LocalMemSobolev Ω (s + 2) f := by
  intro χ hχ hc hs
  have hlow : LocalMemSobolev Ω s f := h.mono (by linarith)
  have hd (d : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ χ z d) :=
    (contDiff_infty_iff_fderiv.mp hχ).2.clm_apply contDiff_const
  have hds (d : ℂ) : tsupport (fun z => fderiv ℝ χ z d) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ d).trans hs
  have hm (d : ℂ) := (h.lineDeriv d) _ (hd d) (hc.fderiv_apply (𝕜 := ℝ) d) (hds d)
  have hdd (d : ℂ) := hlow (fun z => fderiv ℝ (fun w => fderiv ℝ χ w d) z d)
    ((contDiff_infty_iff_fderiv.mp (hd d)).2.clm_apply contDiff_const)
    ((hc.fderiv_apply (𝕜 := ℝ) d).fderiv_apply (𝕜 := ℝ) d)
    ((tsupport_fderiv_apply_subset ℝ d).trans (hds d))
  have hv := hlow (fun z => χ z * V z) (hχ.mul hV) (hc.mul_right)
    ((tsupport_mul_subset_left (f := χ) (g := V)).trans hs)
  apply memSobolev_add_two_of_laplacian (hlow χ hχ hc hs)
  rw [distribution_laplacian_smulLeft hχ hc, heq χ hχ hc hs]
  exact (((hv.neg.add ((hm 1).add (hm 1))).add
    ((hm Complex.I).add (hm Complex.I))).add (hdd 1)).add (hdd Complex.I)

/-- A local H¹ solution has every nonnegative integer Sobolev order. -/
theorem localMemSobolev_all_nat_of_potential {Ω : Set ℂ} {V : ℂ → ℂ} {f : 𝓢'(ℂ, ℂ)}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (heq : LocalPotentialEquation Ω V f)
    (h : LocalMemSobolev Ω 1 f) (n : ℕ) : LocalMemSobolev Ω n f := by
  have hall : ∀ j : ℕ, LocalMemSobolev Ω ((j : ℝ) + 1) f := by
    intro j
    induction j with
    | zero => simpa using h
    | succ j ih =>
      have hh := ih.gain_of_potential hV heq
      convert hh using 1
      push_cast
      ring
  exact (hall n).mono (by linarith)

end KsIndex.Weq
