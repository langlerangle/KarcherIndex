module

public import KsIndexLean.InteriorModeCompatibility

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- A single mode on the punctured closed disk, patched from the annular
representatives. The assigned value outside (0,1] asserts no centre regularity. -/
def puncturedDiskMode (u : ComplexH1) (n : ℤ) (r : ℝ) : ℂ :=
  if hr : r ∈ Ioc (0 : ℝ) 1 then
    interiorDiskMode (show r / 2 < 1 by obtain ⟨_, _⟩ := hr; linarith) u n r
  else 0

def puncturedDiskModeDerivative (k : ℕ) (u : ComplexH1) (n : ℤ) (r : ℝ) : ℂ :=
  if hr : r ∈ Ioc (0 : ℝ) 1 then
    interiorDiskClassicalDerivative (show r / 2 < 1 by obtain ⟨_, _⟩ := hr; linarith) k u n r
  else 0

lemma puncturedDiskMode_eq_interior {a b r : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (u : ComplexH1) (n : ℤ)
    (hr : r ∈ Icc a b) : puncturedDiskMode u n r = interiorDiskMode hab u n r := by
  have hr0 := ha.trans_le hr.1
  have hr1 := hr.2.trans hb
  rw [puncturedDiskMode, dite_eq_left (show r ∈ Ioc (0 : ℝ) 1 from ⟨hr0, hr1⟩)]
  apply interiorDiskMode_overlap (half_pos hr0) _ le_rfl ha hab hb u n _ hr
  exact ⟨by linarith, hr1⟩

lemma puncturedDiskModeDerivative_eq_interior {a b r : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (k : ℕ) (u : ComplexH1) (n : ℤ)
    (hu : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ →
      weakJacobi (surfacePotential k) u v = 0)
    (hr : r ∈ Icc a b) :
    puncturedDiskModeDerivative k u n r = interiorDiskClassicalDerivative hab k u n r := by
  have hr0 := ha.trans_le hr.1
  have hr1 := hr.2.trans hb
  rw [puncturedDiskModeDerivative, dite_eq_left (show r ∈ Ioc (0 : ℝ) 1 from ⟨hr0, hr1⟩)]
  apply interiorDiskClassicalDerivative_overlap (half_pos hr0) _ le_rfl ha hab hb k u n hu _ hr
  exact ⟨by linarith, hr1⟩

lemma puncturedDiskMode_hasDerivAt (k : ℕ) (u : ComplexH1) (n : ℤ)
    (hu : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ →
      weakJacobi (surfacePotential k) u v = 0)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (puncturedDiskMode u n) (puncturedDiskModeDerivative k u n r) r := by
  have ha : 0 < r / 2 := half_pos hr.1
  have hab : r / 2 < 1 := by linarith [hr.1, hr.2]
  have hri : r ∈ Ioo (r / 2) 1 := ⟨by linarith [hr.1], hr.2⟩
  rw [puncturedDiskModeDerivative_eq_interior ha hab le_rfl k u n hu (Ioo_subset_Icc_self hri)]
  apply (interiorDiskMode_hasDerivAt ha hab le_rfl k u n hu hri).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hri.1 hri.2] with t ht
  exact puncturedDiskMode_eq_interior ha hab le_rfl u n (Ioo_subset_Icc_self ht)

lemma puncturedDiskMode_flux_hasDerivAt (k : ℕ) (u : ComplexH1) (n : ℤ)
    (hu : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ →
      weakJacobi (surfacePotential k) u v = 0)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => t • puncturedDiskModeDerivative k u n t)
      (((n : ℝ)^2 / r - r * KsIndex.Radial.Vrad k r) • puncturedDiskMode u n r) r := by
  have ha : 0 < r / 2 := half_pos hr.1
  have hab : r / 2 < 1 := by linarith [hr.1, hr.2]
  have hri : r ∈ Ioo (r / 2) 1 := ⟨by linarith [hr.1], hr.2⟩
  rw [puncturedDiskMode_eq_interior ha hab le_rfl u n (Ioo_subset_Icc_self hri)]
  apply (interiorDiskMode_classical_flux_hasDerivAt ha hab le_rfl k u n hri).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hri.1 hri.2] with t ht
  rw [puncturedDiskModeDerivative_eq_interior ha hab le_rfl k u n hu (Ioo_subset_Icc_self ht)]

lemma puncturedDiskMode_continuousOn_annulus {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (u : ComplexH1) (n : ℤ) :
    ContinuousOn (puncturedDiskMode u n) (Icc a b) :=
  (interiorDiskMode_continuousOn ha hab hb u n).congr
    (fun _ hr => puncturedDiskMode_eq_interior ha hab hb u n hr)

lemma puncturedDiskModeDerivative_continuousOn_annulus {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (k : ℕ) (u : ComplexH1) (n : ℤ)
    (hu : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ →
      weakJacobi (surfacePotential k) u v = 0) :
    ContinuousOn (puncturedDiskModeDerivative k u n) (Icc a b) :=
  (interiorDiskClassicalDerivative_continuousOn ha hab hb k u n).congr
    (fun _ hr => puncturedDiskModeDerivative_eq_interior ha hab hb k u n hu hr)

/-- At radius one, the patched mode equals the Fourier coefficient of the disk trace. -/
lemma puncturedDiskMode_one (u : ComplexH1) (n : ℤ) :
    puncturedDiskMode u n 1 = circleFourierCoeff (diskTraceCLM u) n := by
  rw [puncturedDiskMode_eq_interior (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) le_rfl u n (by norm_num), interiorDiskMode_collar]
  exact diskMode_one u n

end KsIndex.Trace
