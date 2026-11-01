module

public import KsIndexLean.ContourPartialFractions
public import KsIndexLean.KarcherPartialFractions

@[expose] public section


/-! The actual normalized Karcher loop formulas, with integrability derived from avoidance. -/
noncomputable section
namespace KsIndex.KarcherData
open Piecewise

lemma avoids_punctureFinset {k : ℕ} (hk : 2 ≤ k) (C : Chain)
    (hA : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    ∀ z ∈ punctureFinset k, C.Avoids z :=
  fun z hz => hA z ((mem_punctureFinset hk).mp hz)

lemma image_not_puncture {k : ℕ} (C : Chain)
    (hA : ∀ z ∈ Surface.punctures k, C.Avoids z) {w : ℂ} (hw : w ∈ C.image) :
    w ∉ Surface.punctures k := by
  intro hp
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hw
  obtain ⟨t, ht, rfl⟩ := hi
  exact hA _ hp i t ht rfl

lemma coeff1_chain_integrable {k : ℕ} (hk : 2 ≤ k) (C : Chain)
    (hA : ∀ z ∈ Surface.punctures k, C.Avoids z) : C.Integrable (coeff1 k) := by
  apply C.integrable_of_partial_fractions (punctureFinset k) (fun z => -(z.re : ℂ))
    (avoids_punctureFinset hk C hA)
  intro w hw
  exact coeff1_partial_fractions hk (image_not_puncture C hA hw)
lemma coeff2_chain_integrable {k : ℕ} (hk : 2 ≤ k) (C : Chain)
    (hA : ∀ z ∈ Surface.punctures k, C.Avoids z) : C.Integrable (coeff2 k) := by
  apply C.integrable_of_partial_fractions (punctureFinset k) (fun z => (z.im : ℂ))
    (avoids_punctureFinset hk C hA)
  intro w hw
  exact coeff2_partial_fractions hk (image_not_puncture C hA hw)
lemma coeff3_chain_integrable {k : ℕ} (hk : 2 ≤ k) (C : Chain)
    (hA : ∀ z ∈ Surface.punctures k, C.Avoids z) : C.Integrable (coeff3 k) := by
  apply C.integrable_of_partial_fractions (punctureFinset k) (fun z => 1 / z ^ k)
    (avoids_punctureFinset hk C hA)
  intro w hw
  exact coeff3_partial_fractions hk (image_not_puncture C hA hw)

/-- Finite proof-carrying winding sum, using the actual puncture set. -/
def karcherWindingSum {k : ℕ} (hk : 2 ≤ k) (C : Chain) (hc : C.IsClosed)
    (hA : ∀ z ∈ Surface.punctures k, C.Avoids z) (R : ℂ → ℂ) : ℂ :=
  C.residueWindingSum hc (punctureFinset k) R (avoids_punctureFinset hk C hA)

theorem coeff1_loop_formula {k : ℕ} (hk : 2 ≤ k) (C : Chain) (hc : C.IsClosed)
    (hA : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    C.contour (coeff1 k) = (2 * Real.pi * Complex.I) *
      karcherWindingSum hk C hc hA (fun z => -(z.re : ℂ)) := by
  apply C.contour_of_partial_fractions hc (punctureFinset k) (fun z => -(z.re : ℂ))
    (avoids_punctureFinset hk C hA)
  intro w hw
  exact coeff1_partial_fractions hk (image_not_puncture C hA hw)
theorem coeff2_loop_formula {k : ℕ} (hk : 2 ≤ k) (C : Chain) (hc : C.IsClosed)
    (hA : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    C.contour (coeff2 k) = (2 * Real.pi * Complex.I) *
      karcherWindingSum hk C hc hA (fun z => (z.im : ℂ)) := by
  apply C.contour_of_partial_fractions hc (punctureFinset k) (fun z => (z.im : ℂ))
    (avoids_punctureFinset hk C hA)
  intro w hw
  exact coeff2_partial_fractions hk (image_not_puncture C hA hw)
theorem coeff3_loop_formula {k : ℕ} (hk : 2 ≤ k) (C : Chain) (hc : C.IsClosed)
    (hA : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    C.contour (coeff3 k) = (2 * Real.pi * Complex.I) *
      karcherWindingSum hk C hc hA (fun z => 1 / z ^ k) := by
  apply C.contour_of_partial_fractions hc (punctureFinset k) (fun z => 1 / z ^ k)
    (avoids_punctureFinset hk C hA)
  intro w hw
  exact coeff3_partial_fractions hk (image_not_puncture C hA hw)

end KsIndex.KarcherData
