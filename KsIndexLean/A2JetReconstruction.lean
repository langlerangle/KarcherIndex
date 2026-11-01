module

public import KsIndexLean.FiniteWeakPartition

@[expose] public section


/-!
# Weak-derivative reconstruction from almost-everywhere value agreement

Finite sums preserve weak derivatives on any open subset of the complex plane.
For a function with a whole-plane weak derivative that agrees almost everywhere
with `valueCLM u` on the disk, restriction and weak-derivative uniqueness identify
its derivative with `Dxy (dxLp u) (dyLp u)` almost everywhere on the disk.

`finite_weak_partition_jet_sum` applies this to an interior piece and finitely many
joined boundary pieces. It assumes weak derivatives for those pieces and their
value reconstruction identity; it does not construct the cutoffs or prove that
identity. The conclusion follows from `TauCeti.HasWeakFDerivOn.ae_eq`, without
expanding derivatives of the individual cutoff functions.
-/

open Set Filter Topology TopologicalSpace MeasureTheory BigOperators
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- On an open set `Ω`, a finite sum of functions with weak derivatives has their sum as its weak derivative. -/
theorem hasWeakFDerivOn_finset_sum {ι : Type*} {Ω : Opens ℂ} (t : Finset ι)
    {f : ι → ℂ → ℂ} {U : ι → ℂ → ℂ →L[ℝ] ℂ}
    (h : ∀ i ∈ t, TauCeti.HasWeakFDerivOn volume Ω (f i) (U i)) :
    TauCeti.HasWeakFDerivOn volume Ω (fun z => ∑ i ∈ t, f i z)
      (fun z => ∑ i ∈ t, U i z) := by
  classical
  induction t using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact TauCeti.hasWeakFDerivOn_zero
  | @insert a t ha ih =>
    have hstep := (h a (Finset.mem_insert_self a t)).add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
    refine hstep.congr_ae ?_ |>.congr_ae_deriv ?_
    · filter_upwards with z
      simp [Finset.sum_insert ha]
    · filter_upwards with z
      ext d
      simp [Finset.sum_insert ha]

/-- A whole-plane weak derivative of a function agreeing with `valueCLM u` almost
 everywhere on the disk agrees there with the carrier's weak derivative. -/
theorem finite_weak_partition_jet {u : ComplexH1} {S : ℂ → ℂ}
    {Jsum : ℂ → ℂ →L[ℝ] ℂ}
    (hSjet : TauCeti.HasWeakFDerivOn volume ⊤ S Jsum)
    (hSval : S =ᵐ[volume.restrict disk] (valueCLM u : ℂ → ℂ)) :
    Jsum =ᵐ[volume.restrict disk] Dxy (dxLp u) (dyLp u) := by
  have hS_disk : TauCeti.HasWeakFDerivOn volume disk S Jsum := hSjet.mono le_top
  have hu_disk : TauCeti.HasWeakFDerivOn volume disk (valueCLM u)
      (Dxy (dxLp u) (dyLp u)) := carrier_hasJet u
  exact hS_disk.ae_eq (hu_disk.congr_ae hSval.symm)

/-- Given whole-plane weak derivatives for the interior and finitely many boundary
pieces, and their almost-everywhere value reconstruction on the disk, the sum of
their weak derivatives equals the carrier's weak derivative almost everywhere there. -/
theorem finite_weak_partition_jet_sum {ι : Type*} (t : Finset ι) (u : ComplexH1)
    (χ : ℂ → ℝ) (ρ : ι → ℂ → ℝ) (s : ι → ℂ)
    {Jint : ℂ → ℂ →L[ℝ] ℂ} {Jbnd : ι → ℂ → ℂ →L[ℝ] ℂ}
    (hint : TauCeti.HasWeakFDerivOn volume ⊤ (fun z => χ z • valueCLM u z) Jint)
    (hbnd : ∀ i ∈ t, TauCeti.HasWeakFDerivOn volume ⊤
      (fun z => ρ i z • joinedDiskValue u u (s i) z) (Jbnd i))
    (hval : (fun z => χ z • valueCLM u z +
        ∑ i ∈ t, ρ i z • joinedDiskValue u u (s i) z)
        =ᵐ[volume.restrict disk] (valueCLM u : ℂ → ℂ)) :
    (fun z => Jint z + ∑ i ∈ t, Jbnd i z)
      =ᵐ[volume.restrict disk] Dxy (dxLp u) (dyLp u) :=
  finite_weak_partition_jet (hint.add (hasWeakFDerivOn_finset_sum t hbnd)) hval

end KsIndex.Trace
