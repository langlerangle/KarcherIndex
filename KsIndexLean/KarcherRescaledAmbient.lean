module

public import KsIndexLean.KarcherPeriodQuotientCharts

@[expose] public section


/-! Homothetic realization of each period quotient in the fixed 2π ambient quotient. -/
noncomputable section
namespace KsIndex.KarcherData.HeightLift
variable {P : Type*} {F : P → PeriodTarget} (m : ℕ) [NeZero m]

/-- The actual ambient map after homothety by the reciprocal period count. -/
def rescaledAmbient (q : HeightLift F) : AmbientTriple := (m : ℝ)⁻¹ • ambient q

lemma rescaledAmbient_deck (n : ℤ) (q : HeightLift F) :
    rescaledAmbient m (deck (n * (m : ℤ)) q) =
      rescaledAmbient m q + (0,0,(n : ℝ) * (2 * Real.pi)) := by
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  rw [rescaledAmbient, ambient_deck, smul_add]
  congr 1
  ext <;> simp [smul_eq_mul]
  field_simp

lemma rescaledAmbient_projects_deck (n : ℤ) (q : HeightLift F) :
    projectPeriod (rescaledAmbient m (deck (n * (m : ℤ)) q)) =
      projectPeriod (rescaledAmbient m q) := by
  apply projectPeriod_eq_of_sub_lattice (n := n)
  rw [rescaledAmbient_deck]
  ext <;> simp
  ring

/-- The m-period carrier mapped into the fixed ambient quotient after scaling. -/
def rescaledPeriodMap : PeriodQuotient F m → PeriodTarget :=
  Quotient.lift (fun q => projectPeriod (rescaledAmbient m q)) (by
    rintro q r ⟨n,rfl⟩
    exact (rescaledAmbient_projects_deck m n q).symm)

@[simp] lemma rescaledPeriodMap_mk (q : HeightLift F) :
    rescaledPeriodMap m (periodQuotientMap m q) = projectPeriod (rescaledAmbient m q) := rfl

lemma continuous_rescaledPeriodMap [TopologicalSpace P] (hF : Continuous F) :
    Continuous (rescaledPeriodMap (F := F) m) := by
  apply (periodQuotientMap_isQuotientMap (F := F) m).continuous_iff.mpr
  exact continuous_projectPeriod.comp ((continuous_ambient hF).const_smul (m : ℝ)⁻¹)

end KsIndex.KarcherData.HeightLift
#print axioms KsIndex.KarcherData.HeightLift.rescaledAmbient_deck
#print axioms KsIndex.KarcherData.HeightLift.rescaledPeriodMap
#print axioms KsIndex.KarcherData.HeightLift.continuous_rescaledPeriodMap
