module

public import KsIndexLean.TwistedCoreTrace

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Twisted

/-- The sum of the two adopted disk Jacobi forms on an ordered weak pair. -/
def slitJacobi (k : ℕ) (u v : DiskPairH1) : ℂ :=
  weakJacobi (surfacePotential k) u.1 v.1 + weakJacobi (surfacePotential k) u.2 v.2

/-- The ordered slit map preserves the original twisted pair's polarized Jacobi form. -/
theorem twistedCoreToSlit_form {k : ℕ} (hk : 1 ≤ k) {ζ : ℂ} (hζ : ζ ≠ 0)
    (u v : TwistedCc k ζ) :
    slitJacobi k (twistedCoreToSlit hk hζ u).val (twistedCoreToSlit hk hζ v).val =
      SurfaceForm.jacobiB k 1 u.val v.val := by
  have hi (n : ZMod (2 * 1)) := smooth_weakJacobi_eq_classical (surfacePotential k)
    (naturalCoreData hk (twistedCopyNatural hζ u n))
    (naturalCoreData hk (twistedCopyNatural hζ v n))
  change weakJacobi (surfacePotential k) (twistedCcCoreH1 hk hζ u 1) (twistedCcCoreH1 hk hζ v 1) +
    weakJacobi (surfacePotential k) (twistedCcCoreH1 hk hζ u 0) (twistedCcCoreH1 hk hζ v 0) = _
  change ∀ n, weakJacobi (surfacePotential k) (twistedCcCoreH1 hk hζ u n)
    (twistedCcCoreH1 hk hζ v n) = _ at hi
  rw [hi 1, hi 0]
  have hsum : (Finset.univ : Finset (ZMod (2 * 1))) = {0, 1} := by decide
  simp [SurfaceForm.jacobiB, hsum, KsIndex.GradOrtho.gradInner,
    naturalCoreData, twistedCopyNatural, surfacePotential, disk, Surface.disk]
  ring

lemma twistedCoreToSlit_self_form {k : ℕ} (hk : 2 ≤ k) {ζ : ℂ} (hζ : ζ ≠ 0)
    (u : TwistedCc k ζ) :
    slitJacobi k (twistedCoreToSlit (by omega) hζ u).val
      (twistedCoreToSlit (by omega) hζ u).val = (Surface.jacobiQ k 1 u.val : ℂ) := by
  rw [twistedCoreToSlit_form, SurfaceForm.jacobiB_self hk]

end KsIndex.Trace
