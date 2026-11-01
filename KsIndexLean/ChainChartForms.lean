module

public import KsIndexLean.ChainChartNormed
public import KsIndexLean.NaturalCoreForm

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Finite ordered-copy Dirichlet form on the genuine chart quotient. -/
def chainChartDirichlet (k m : ℕ) [NeZero m] (q r : ChainChartSpace k m) : ℂ :=
  ∑ n : ZMod (2 * m), dirichlet (chainChartCoordinatesCLM k m q n)
    (chainChartCoordinatesCLM k m r n)

def chainChartJacobi (k m : ℕ) [NeZero m] (V : BoundedRealPotential)
    (q r : ChainChartSpace k m) : ℂ :=
  ∑ n : ZMod (2 * m), weakJacobi V (chainChartCoordinatesCLM k m q n)
    (chainChartCoordinatesCLM k m r n)

lemma continuous_copyForm_pullback {E : Type*} [TopologicalSpace E]
    {ι : Type*} [Fintype ι] (T : E → ι → ComplexH1) (hT : Continuous T)
    (B : ComplexH1 → ComplexH1 → ℂ)
    (hB : Continuous (fun p : ComplexH1 × ComplexH1 => B p.1 p.2)) :
    Continuous (fun p : E × E => ∑ n, B (T p.1 n) (T p.2 n)) := by
  apply continuous_finsetSum
  intro n _
  exact hB.comp (((continuous_apply n |>.comp hT).comp continuous_fst).prodMk
    ((continuous_apply n |>.comp hT).comp continuous_snd))

lemma continuous_chainChartDirichlet (k m : ℕ) [NeZero m] :
    Continuous (fun p : ChainChartSpace k m × ChainChartSpace k m =>
      chainChartDirichlet k m p.1 p.2) :=
  continuous_copyForm_pullback _ (chainChartCoordinatesCLM k m).continuous
    dirichlet continuous_dirichlet

lemma continuous_chainChartJacobi (k m : ℕ) [NeZero m] (V : BoundedRealPotential) :
    Continuous (fun p : ChainChartSpace k m × ChainChartSpace k m =>
      chainChartJacobi k m V p.1 p.2) :=
  continuous_copyForm_pullback _ (chainChartCoordinatesCLM k m).continuous
    (weakJacobi V) (continuous_weakJacobi V)

lemma chainChartDirichlet_class (k m : ℕ) [NeZero m] (u v : weakDiskChain k m) :
    chainChartDirichlet k m (weakChainClass k m u) (weakChainClass k m v) =
      ∑ n, dirichlet (u.val n) (v.val n) := by
  simp only [chainChartDirichlet, chainChartCoordinates_class]

lemma chainChartJacobi_class (k m : ℕ) [NeZero m] (V : BoundedRealPotential)
    (u v : weakDiskChain k m) :
    chainChartJacobi k m V (weakChainClass k m u) (weakChainClass k m v) =
      ∑ n, weakJacobi V (u.val n) (v.val n) := by
  simp only [chainChartJacobi, chainChartCoordinates_class]

/-- Agreement with the paper-side polarized form through the original smooth encoding. -/
lemma energySmoothToChainChart_jacobi (k m : ℕ) [NeZero m]
    (u v : FaithfulInjection.EnergySmooth k m) :
    chainChartJacobi k m (surfacePotential k)
      (energySmoothToChainChart k m u) (energySmoothToChainChart k m v) =
      SurfaceForm.jacobiB k m u.val v.val := by
  rw [chainChartJacobi, energySmoothToChainChart_coordinates, energySmoothToChainChart_coordinates]
  exact energySmoothToWeakChain_form u v

lemma energySmoothToChainChart_jacobi_self (k m : ℕ) [NeZero m] (hk : 2 ≤ k)
    (u : FaithfulInjection.EnergySmooth k m) :
    chainChartJacobi k m (surfacePotential k)
      (energySmoothToChainChart k m u) (energySmoothToChainChart k m u) =
      (Surface.jacobiQ k m u.val : ℂ) := by
  rw [energySmoothToChainChart_jacobi, SurfaceForm.jacobiB_self hk]

lemma chainChartDirichlet_add_left (k m : ℕ) [NeZero m]
    (q r t : ChainChartSpace k m) :
    chainChartDirichlet k m (q + r) t =
      chainChartDirichlet k m q t + chainChartDirichlet k m r t := by
  simp only [chainChartDirichlet, map_add, Pi.add_apply, dirichlet_add_left, Finset.sum_add_distrib]

lemma chainChartDirichlet_add_right (k m : ℕ) [NeZero m]
    (q r t : ChainChartSpace k m) :
    chainChartDirichlet k m q (r + t) =
      chainChartDirichlet k m q r + chainChartDirichlet k m q t := by
  simp only [chainChartDirichlet, map_add, Pi.add_apply, dirichlet_add_right,
    Finset.sum_add_distrib]

lemma chainChartDirichlet_smul_left (k m : ℕ) [NeZero m]
    (c : ℂ) (q r : ChainChartSpace k m) :
    chainChartDirichlet k m (c • q) r = (starRingEnd ℂ) c * chainChartDirichlet k m q r := by
  simp only [chainChartDirichlet, map_smul, Pi.smul_apply, dirichlet_smul_left, Finset.mul_sum]

lemma chainChartDirichlet_smul_right (k m : ℕ) [NeZero m]
    (c : ℂ) (q r : ChainChartSpace k m) :
    chainChartDirichlet k m q (c • r) = c * chainChartDirichlet k m q r := by
  simp only [chainChartDirichlet, map_smul, Pi.smul_apply, dirichlet_smul_right, Finset.mul_sum]

lemma chainChartDirichlet_conj (k m : ℕ) [NeZero m]
    (q r : ChainChartSpace k m) :
    (starRingEnd ℂ) (chainChartDirichlet k m r q) = chainChartDirichlet k m q r := by
  simp only [chainChartDirichlet, map_sum, dirichlet_conj]

lemma chainChartJacobi_add_left (k m : ℕ) [NeZero m] (V : BoundedRealPotential)
    (q r t : ChainChartSpace k m) :
    chainChartJacobi k m V (q + r) t = chainChartJacobi k m V q t + chainChartJacobi k m V r t := by
  simp only [chainChartJacobi, map_add, Pi.add_apply, weakJacobi_add_left, Finset.sum_add_distrib]

lemma chainChartJacobi_add_right (k m : ℕ) [NeZero m] (V : BoundedRealPotential)
    (q r t : ChainChartSpace k m) :
    chainChartJacobi k m V q (r + t) = chainChartJacobi k m V q r + chainChartJacobi k m V q t := by
  simp only [chainChartJacobi, map_add, Pi.add_apply, weakJacobi_add_right, Finset.sum_add_distrib]

lemma chainChartJacobi_smul_left (k m : ℕ) [NeZero m] (V : BoundedRealPotential)
    (c : ℂ) (q r : ChainChartSpace k m) :
    chainChartJacobi k m V (c • q) r = (starRingEnd ℂ) c * chainChartJacobi k m V q r := by
  simp only [chainChartJacobi, map_smul, Pi.smul_apply, weakJacobi_smul_left, Finset.mul_sum]

lemma chainChartJacobi_smul_right (k m : ℕ) [NeZero m] (V : BoundedRealPotential)
    (c : ℂ) (q r : ChainChartSpace k m) :
    chainChartJacobi k m V q (c • r) = c * chainChartJacobi k m V q r := by
  simp only [chainChartJacobi, map_smul, Pi.smul_apply, weakJacobi_smul_right, Finset.mul_sum]

lemma chainChartJacobi_conj (k m : ℕ) [NeZero m] (V : BoundedRealPotential)
    (q r : ChainChartSpace k m) :
    (starRingEnd ℂ) (chainChartJacobi k m V r q) = chainChartJacobi k m V q r := by
  simp only [chainChartJacobi, map_sum, weakJacobi_conj]

end KsIndex.Trace
