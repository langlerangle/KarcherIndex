module

public import KsIndexLean.KarcherParameterRoot
public import KsIndexLean.KarcherEndCoordinateChart

@[expose] public section


/-! Transfer of the normalized base end coordinate through the finite
parameter chart and the actual period quotient projection. -/
noncomputable section
namespace KsIndex.KarcherData

/-- The signed normalized end coordinate on the parameter sphere. -/
def parameterEndCoordinate {k : ℕ} (b : PuncturedPlane k) (w : ℂ)
    (p : ParameterSphere k) : ℂ :=
  (if w ^ k = Complex.I then parameterCayley p else (parameterCayley p)⁻¹) /
    endCoordinate k w b.val

@[simp] theorem parameterEndCoordinate_finite {k : ℕ} (b z : PuncturedPlane k) (w : ℂ) :
    parameterEndCoordinate b w (finiteParameter z) =
      endCoordinate k w z.val / endCoordinate k w b.val := by
  rw [parameterEndCoordinate, parameterCayley_finite, endCoordinate_eq_heightCayley k w z.val]

/-- The actual finite parameter image of the inverse-function source. -/
def endParameterRegion {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : w ∈ Surface.punctures k) : Set (ParameterSphere k) :=
  finiteParameter '' {z : PuncturedPlane k | z.val ∈ (endCoordinateChart hk hw).source}

theorem parameterEndCoordinate_isLocalHomeomorphOn {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : w ∈ Surface.punctures k) (b : PuncturedPlane k) :
    IsLocalHomeomorphOn (parameterEndCoordinate b w) (endParameterRegion hk hw) := by
  have he : parameterEndCoordinate b w ∘ finiteParameter =
      fun z : PuncturedPlane k => endCoordinate k w z.val / endCoordinate k w b.val :=
    funext (fun z => parameterEndCoordinate_finite b z w)
  have hc : IsLocalHomeomorphOn (parameterEndCoordinate b w ∘ finiteParameter)
      {z : PuncturedPlane k | z.val ∈ (endCoordinateChart hk hw).source} := by
    rw [he]
    exact normalizedEndCoordinate_isLocalHomeomorphOn_punctured hk hw b
  exact hc.of_comp_right ((isOpenEmbedding_finiteParameter k).isLocalHomeomorph.isLocalHomeomorphOn.mono (Set.subset_univ _))

/-- Pullback through the actual quotient projection preserves the local
base-coordinate topology over the end region. -/
theorem quotient_endCoordinate_isLocalHomeomorphOn {k m : ℕ} (hk : 2 ≤ k)
    {w : ℂ} (hw : w ∈ Surface.punctures k) (b : PuncturedPlane k) (C : PeriodTarget)
    (hF : Continuous (extendedEWMap hk b C)) :
    IsLocalHomeomorphOn
      (parameterEndCoordinate b w ∘ HeightLift.quotientProjection
        (F := extendedEWMap hk b C) m)
      (HeightLift.quotientProjection m ⁻¹' endParameterRegion hk hw) := by
  exact (parameterEndCoordinate_isLocalHomeomorphOn hk hw b).comp
    ((HeightLift.quotientProjection_isLocalHomeomorph hF m).isLocalHomeomorphOn.mono
      (Set.subset_univ _)) (fun _ hx => hx)

end KsIndex.KarcherData
