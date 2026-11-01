module

public import KsIndexLean.CcSmoothWeakChain
public import KsIndexLean.ChainChartForms

@[expose] public section


noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- The direct smooth realization preserves the full polarized Jacobi form. -/
lemma ccSmoothToChainChart_jacobi (k m : ℕ) [NeZero m]
    (u v : Surface.CcSmooth k m) :
    chainChartJacobi k m (surfacePotential k)
      (ccSmoothToChainChart k m u) (ccSmoothToChainChart k m v) =
      SurfaceForm.jacobiB k m u.val v.val := by
  simp only [chainChartJacobi, ccSmoothToChainChart_coordinates]
  unfold SurfaceForm.jacobiB
  apply Finset.sum_congr rfl
  intro n _
  exact smooth_weakJacobi_eq_classical (surfacePotential k)
    (ccSmoothCopyData u n) (ccSmoothCopyData v n)

/-- Uncurrying is only a coordinate change on the original smooth test domain. -/
def domCcSmoothEquiv (k m : ℕ) : SurfaceForm.Dom k m ≃ₗ[ℂ] Surface.CcSmooth k m where
  toFun u := ⟨(Surface.uncurryE m).symm u.val, SurfaceForm.mem_Dom.mp u.property⟩
  invFun u := ⟨Surface.uncurryE m u.val, SurfaceForm.mem_Dom.mpr
    (by rw [LinearEquiv.symm_apply_apply]; exact u.property)⟩
  left_inv u := Subtype.ext ((Surface.uncurryE m).apply_symm_apply u.val)
  right_inv u := Subtype.ext ((Surface.uncurryE m).symm_apply_apply u.val)
  map_add' u v := Subtype.ext ((Surface.uncurryE m).symm.map_add u.val v.val)
  map_smul' c u := Subtype.ext ((Surface.uncurryE m).symm.map_smul c u.val)

def domToChainChart (k m : ℕ) [NeZero m] :
    SurfaceForm.Dom k m →ₗ[ℂ] ChainChartSpace k m :=
  (ccSmoothToChainChart k m).comp (domCcSmoothEquiv k m).toLinearMap

lemma domToChainChart_jacobi (k m : ℕ) [NeZero m] (u v : SurfaceForm.Dom k m) :
    chainChartJacobi k m (surfacePotential k)
      (domToChainChart k m u) (domToChainChart k m v) =
      SurfaceForm.Bs k m u.val v.val :=
  ccSmoothToChainChart_jacobi k m (domCcSmoothEquiv k m u) (domCcSmoothEquiv k m v)

lemma domToChainChart_form {k m : ℕ} [NeZero m] (hk : 2 ≤ k)
    (u : SurfaceForm.Dom k m) :
    (chainChartJacobi k m (surfacePotential k)
      (domToChainChart k m u) (domToChainChart k m u)).re =
      SurfaceForm.Qs k m u.val := by
  rw [domToChainChart_jacobi]
  exact congrArg Complex.re (SurfaceForm.jacobiB_self hk _)

end KsIndex.Trace
