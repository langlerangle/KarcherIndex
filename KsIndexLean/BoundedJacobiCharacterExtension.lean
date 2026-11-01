module

public import KsIndexLean.NullityInjection
public import KsIndexLean.PaperRadicalBoundedField

@[expose] public section


/-! Interior character identities extend to the normalized global fields.
The extension uses uniqueness from disk values, including seam continuity. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.PaperSlitTransport
open KsIndex.Surface KsIndex.SurfaceSym KsIndex.WeakH1 KsIndex.Trace

/-- A rotation preserving the chain geometry has the same eigen-character on
the whole normalized field as on all its open disks. -/
theorem boundedJacobi_character_of_disk {k m : ℕ} {U : ZMod (2 * m) → ℂ → ℂ}
    (hU : U ∈ BoundedJacobi k m) {a d : ℂ} (ha : ‖a‖ = 1) (hak : a ^ k = 1)
    (hd : ∀ n z, z ∈ Surface.disk → U n (a * z) = d * U n z) :
    ∀ n z, U n (a * z) = d * U n z := by
  have hm : rotF a U - d • U ∈ BoundedJacobi k m :=
    (BoundedJacobi k m).sub_mem (NullityDecomp.rotF_mem_boundedJacobi ha hak hU)
      ((BoundedJacobi k m).smul_mem d hU)
  have hz : rotF a U - d • U = 0 :=
    NullityDecomp.boundedJacobi_zero_of_disk_zero hm (by
      intro n z hz
      change U n (a * z) - d * U n z = 0
      exact sub_eq_zero.mpr (hd n z hz))
  intro n z
  have he := congrFun (congrFun hz n) z
  exact sub_eq_zero.mp he

/-- The disk identity in the precise paper convention extends across both
seam families, punctures, and the zero exterior. -/
theorem boundedJacobi_paper_character_of_disk {m j : ℕ}
    {U : ZMod (2 * m) → ℂ → ℂ} (hU : U ∈ BoundedJacobi 3 m)
    (hd : ∀ n z, z ∈ (WeakH1.disk : Set ℂ) →
      U n (planeRotation (-(2 * Real.pi) / 3) z) = FormIndex.zeta 3 ^ j * U n z) :
    ∀ n z, U n (planeRotation (-(2 * Real.pi) / 3) z) = FormIndex.zeta 3 ^ j * U n z := by
  have he := boundedJacobi_character_of_disk hU
    (Complex.norm_exp_ofReal_mul_I (-(2 * Real.pi) / 3))
    (paperRotation_root 3 (by decide))
    (by
      intro n z hz
      simpa only [planeRotation_apply] using hd n z hz)
  simpa only [planeRotation_apply] using he

end KsIndex.PaperSlitTransport
