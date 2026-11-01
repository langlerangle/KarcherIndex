module

/-
KsIndexLean — LapRealBridge: the real/imaginary bridge between the
real div-grad Laplacian `lapReal` (on ℂ→ℝ) and `Surface.laplacian` (on ℂ→ℂ).

A continuous ℝ-linear functional commutes with the second-derivative operator:
for `L : ℂ →L[ℝ] ℝ` and `G` twice differentiable near `x`,

  `lapReal (fun z => L (G z)) x = L (laplacian G x)`.

Specialized to `Complex.reCLM` / `Complex.imCLM` this turns the complex end-chart
Jacobi equation `ΔF + V·F = 0` into the real-part equations `lapReal (Re F) + V·Re F = 0`
and `lapReal (Im F) + V·Im F = 0` consumed by `bounded_near_complex_of_smooth_punctured`.
-/
public import KsIndexLean.GammaRemovability
public import KsIndexLean.Surface

@[expose] public section


noncomputable section
open KsIndex.Surface KsIndex.PunctureRemoval Complex Filter Topology
open scoped ContDiff

namespace KsIndex.PunctureRemoval

/-- **A continuous ℝ-linear functional commutes with the Laplacian.**  For `L`
continuous linear and `G` twice differentiable near `x`,
`lapReal (L ∘ G) x = L (laplacian G x)`. -/
lemma lapReal_clm_comp {L : ℂ →L[ℝ] ℝ} {G : ℂ → ℂ} {x : ℂ}
    (hG : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 G y) :
    lapReal (fun z => L (G z)) x = L (laplacian G x) := by
  have hdiff : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ G z := by
    filter_upwards [hG] with z hz; exact hz.differentiableAt (by norm_num)
  -- first-derivative transport: `∂(L∘G) z v = L (∂G z v)` near x
  have htrans : ∀ v : ℂ, (fun z => fderiv ℝ (fun y => L (G y)) z v) =ᶠ[𝓝 x]
      (fun z => L (fderiv ℝ G z v)) := by
    intro v
    filter_upwards [hdiff] with z hz
    have hcomp : HasFDerivAt (fun y => L (G y)) (L.comp (fderiv ℝ G z)) z :=
      L.hasFDerivAt.comp z hz.hasFDerivAt
    rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]
  -- the directional first-derivative functions are differentiable at x
  have hGdd : ∀ v : ℂ, DifferentiableAt ℝ (fun z => fderiv ℝ G z v) x := by
    intro v
    exact ((hG.self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).clm_apply (differentiableAt_const v)
  -- the second-derivative transport in each coordinate direction
  have hL : ∀ v : ℂ, fderiv ℝ (fun z => L (fderiv ℝ G z v)) x v
      = L (fderiv ℝ (fun z => fderiv ℝ G z v) x v) := by
    intro v
    have hcomp : HasFDerivAt (fun z => L (fderiv ℝ G z v))
        (L.comp (fderiv ℝ (fun z => fderiv ℝ G z v) x)) x :=
      L.hasFDerivAt.comp x (hGdd v).hasFDerivAt
    rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]
  unfold lapReal
  rw [(htrans 1).fderiv_eq, (htrans Complex.I).fderiv_eq, hL 1, hL Complex.I, ← map_add]
  rfl

/-- The real part of a complex field solving `ΔG = …` — the bridge at `Complex.reCLM`. -/
lemma lapReal_re {G : ℂ → ℂ} {x : ℂ} (hG : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 G y) :
    lapReal (fun z => (G z).re) x = (laplacian G x).re := by
  simpa using lapReal_clm_comp (L := Complex.reCLM) hG

/-- The imaginary part of a complex field — the bridge at `Complex.imCLM`. -/
lemma lapReal_im {G : ℂ → ℂ} {x : ℂ} (hG : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 G y) :
    lapReal (fun z => (G z).im) x = (laplacian G x).im := by
  simpa using lapReal_clm_comp (L := Complex.imCLM) hG

end KsIndex.PunctureRemoval
