module

/-
Mixed Jacobi pairing on the smooth core and sampled phase-character sectors.

A bounded smooth Jacobi field in the finite-energy domain pairs to zero
against compactly supported smooth tests away from the punctures. The
identity `weakEq_of_boundedJacobi` supplies the classical weak equation;
copywise form transport identifies it with `chainChartJacobi`.

For a fixed field, the chain pairing is continuous in its test argument.
Density of the smooth sector tests then extends the vanishing identity to
all of `PaperChainSector m n j`. This module proves that sector-relative
pairing identity; the identification with Jacobi-field fibers is separate.
-/
public import KsIndexLean.WeakEquation
public import KsIndexLean.CcSmoothChainForms
public import KsIndexLean.ChainChartForms
public import KsIndexLean.PaperSectorParameters
public import KsIndexLean.PaperSmoothJointApproximation

@[expose] public section


noncomputable section
namespace KsIndex.Trace

open KsIndex.Surface KsIndex.FaithfulInjection KsIndex.WeakH1

/-- **The mixed form transport**: the chain-carrier pairing of an
`EnergySmooth` field against a smooth core test IS the classical surface
form `jacobiB` — the two realizations agree copy-by-copy. -/
lemma chainChartJacobi_energySmooth_ccSmooth {m : ℕ} [NeZero m]
    (u : EnergySmooth 3 m) (φ : CcSmooth 3 m) :
    chainChartJacobi 3 m (surfacePotential 3)
      (energySmoothToChainChart 3 m u) (ccSmoothToChainChart 3 m φ)
      = SurfaceForm.jacobiB 3 m u.val φ.val := by
  simp only [chainChartJacobi, energySmoothToChainChart_coordinates,
    ccSmoothToChainChart_coordinates]
  unfold SurfaceForm.jacobiB
  apply Finset.sum_congr rfl
  intro n _
  exact smooth_weakJacobi_eq_classical (surfacePotential 3)
    (energySmoothData u n) (ccSmoothCopyData φ n)

/-- A bounded smooth Jacobi field in the finite-energy domain is orthogonal
to every smooth core test under the chain Jacobi pairing. -/
theorem chainChart_pairing_ccSmooth {m : ℕ} [NeZero m]
    (u : EnergySmooth 3 m) (hu : u.val ∈ BoundedJacobi 3 m)
    (φ : CcSmooth 3 m) :
    chainChartJacobi 3 m (surfacePotential 3)
      (energySmoothToChainChart 3 m u) (ccSmoothToChainChart 3 m φ) = 0 := by
  rw [chainChartJacobi_energySmooth_ccSmooth]
  exact weakEq_of_boundedJacobi (by norm_num) hu φ.property

/-- For a fixed field, the chain Jacobi pairing is continuous in its test slot. -/
lemma continuous_chainChartJacobi_fixed_left {m : ℕ} [NeZero m]
    (q : ChainChartSpace 3 m) :
    Continuous fun v : ChainChartSpace 3 m =>
      chainChartJacobi 3 m (surfacePotential 3) q v := by
  simp only [chainChartJacobi]
  refine continuous_finsetSum _ fun n _ => ?_
  have h1 : Continuous fun v : ChainChartSpace 3 m =>
      chainChartCoordinatesCLM 3 m v n :=
    (continuous_apply n).comp (chainChartCoordinatesCLM 3 m).continuous
  exact (continuous_weakJacobi_fixed_left (surfacePotential 3)
    (chainChartCoordinatesCLM 3 m q n)).comp h1

/-- The chain Jacobi pairing with a bounded smooth finite-energy Jacobi field
vanishes on the sampled phase-character sector. Continuity extends the
identity from the dense range of smooth sector tests. -/
theorem chainChart_sector_pairing_zero {m : ℕ} [NeZero m] (n j : ℕ)
    (u : EnergySmooth 3 m) (hu : u.val ∈ BoundedJacobi 3 m)
    (v : KsIndex.Spherical.PaperChainSector m n j) :
    chainChartJacobi 3 m (surfacePotential 3)
      (energySmoothToChainChart 3 m u) v.val.val = 0 := by
  have hLc : Continuous fun w : KsIndex.Spherical.PaperChainSector m n j =>
      chainChartJacobi 3 m (surfacePotential 3)
        (energySmoothToChainChart 3 m u) w.val.val :=
    (continuous_chainChartJacobi_fixed_left _).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  have hzero : ∀ q, chainChartJacobi 3 m (surfacePotential 3)
      (energySmoothToChainChart 3 m u)
      (KsIndex.Spectral.paperSmoothToChainSector m n j q).val.val = 0 := by
    intro q
    have hval : (KsIndex.Spectral.paperSmoothToChainSector m n j q).val.val
        = ccSmoothToChainChart 3 m
            (domCcSmoothEquiv 3 m (KsIndex.Spectral.paperSmoothUnderlying m n j q)) :=
      rfl
    rw [hval]
    exact chainChart_pairing_ccSmooth u hu _
  have hall : (fun w : KsIndex.Spherical.PaperChainSector m n j =>
      chainChartJacobi 3 m (surfacePotential 3)
        (energySmoothToChainChart 3 m u) w.val.val) = fun _ => 0 :=
    (KsIndex.Spectral.paperSmoothToChainSector_denseRange m n j).equalizer
      hLc continuous_const (funext hzero)
  exact congrFun hall v

end KsIndex.Trace
