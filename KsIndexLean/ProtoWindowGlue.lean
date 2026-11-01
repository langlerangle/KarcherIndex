module

public import KsIndexLean.ProtoEnergyP0
public import KsIndexLean.ProtoEnergyP1
public import KsIndexLean.ProtoEnergyP2
public import KsIndexLean.ProtoEnergyMm0
public import KsIndexLean.ProtoEnergyMm1
public import KsIndexLean.ProtoEnergyMm2
public import KsIndexLean.ProtoValid
public import KsIndexLean.NegSignRationalTails
public import KsIndexLean.AlphaRemarkEndpoints

@[expose] public section

set_option maxHeartbeats 1000000
/-! Window aggregation and the finite-window bound at s = spectralLower. -/
namespace KsIndex.NegSignProto
open KsIndex.AlphaRemarkTrial CircleQ
def window : Finset ℤ := Finset.Icc (-64 : ℤ) 64
lemma window_Ioc : window = Finset.Ioc (-65 : ℤ) 64 := by
  ext x; simp [window, Finset.mem_Icc, Finset.mem_Ioc]; omega
theorem window_P_c : tableEnergyNumerator t window 1 0 = (-1892063952102470389662940210555491769439735462491038379264873863440658529520092544632224433767713779958 : ℤ) := by
  have h0 := eP0_c
  have h1 := eP1_c
  have h2 := eP2_c
  simp only [tableEnergyNumerator, wP0, wP1, wP2] at h0 h1 h2 ⊢
  rw [window_Ioc]
  rw [show Finset.Ioc (-65 : ℤ) (64 : ℤ) = Finset.Ioc (-65 : ℤ) (-1 : ℤ) ∪ Finset.Ioc (-1 : ℤ) (64 : ℤ) from (Finset.Ioc_union_Ioc_eq_Ioc (by norm_num) (by norm_num)).symm, Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le (le_refl _))]
  rw [show Finset.Ioc (-1 : ℤ) (64 : ℤ) = Finset.Ioc (-1 : ℤ) (63 : ℤ) ∪ Finset.Ioc (63 : ℤ) (64 : ℤ) from (Finset.Ioc_union_Ioc_eq_Ioc (by norm_num) (by norm_num)).symm, Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le (le_refl _))]
  rw [h0, h1, h2]
  norm_num
theorem window_P_r : tableEnergyRadius t window 1 0 = (37142564311434154649387627888815197917129711516912590588122896078055584192123854744901599891224 : ℤ) := by
  have h0 := eP0_r
  have h1 := eP1_r
  have h2 := eP2_r
  simp only [tableEnergyRadius, wP0, wP1, wP2] at h0 h1 h2 ⊢
  rw [window_Ioc]
  rw [show Finset.Ioc (-65 : ℤ) (64 : ℤ) = Finset.Ioc (-65 : ℤ) (-1 : ℤ) ∪ Finset.Ioc (-1 : ℤ) (64 : ℤ) from (Finset.Ioc_union_Ioc_eq_Ioc (by norm_num) (by norm_num)).symm, Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le (le_refl _))]
  rw [show Finset.Ioc (-1 : ℤ) (64 : ℤ) = Finset.Ioc (-1 : ℤ) (63 : ℤ) ∪ Finset.Ioc (63 : ℤ) (64 : ℤ) from (Finset.Ioc_union_Ioc_eq_Ioc (by norm_num) (by norm_num)).symm, Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le (le_refl _))]
  rw [h0, h1, h2]
  norm_num

theorem window_Mm_c : tableEnergyNumerator t window 4 1 = (1224421683869448175689301987007822130639368628017285242891352401979581077021412011343061966365547221687 : ℤ) := by
  have h0 := eMm0_c
  have h1 := eMm1_c
  have h2 := eMm2_c
  simp only [tableEnergyNumerator, wMm0, wMm1, wMm2] at h0 h1 h2 ⊢
  rw [window_Ioc]
  rw [show Finset.Ioc (-65 : ℤ) (64 : ℤ) = Finset.Ioc (-65 : ℤ) (-1 : ℤ) ∪ Finset.Ioc (-1 : ℤ) (64 : ℤ) from (Finset.Ioc_union_Ioc_eq_Ioc (by norm_num) (by norm_num)).symm, Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le (le_refl _))]
  rw [show Finset.Ioc (-1 : ℤ) (64 : ℤ) = Finset.Ioc (-1 : ℤ) (63 : ℤ) ∪ Finset.Ioc (63 : ℤ) (64 : ℤ) from (Finset.Ioc_union_Ioc_eq_Ioc (by norm_num) (by norm_num)).symm, Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le (le_refl _))]
  rw [h0, h1, h2]
  norm_num
theorem window_Mm_r : tableEnergyRadius t window 4 1 = (8391464919202858958126004862907201832039493869111608060979804547450658594264793643388510259133 : ℤ) := by
  have h0 := eMm0_r
  have h1 := eMm1_r
  have h2 := eMm2_r
  simp only [tableEnergyRadius, wMm0, wMm1, wMm2] at h0 h1 h2 ⊢
  rw [window_Ioc]
  rw [show Finset.Ioc (-65 : ℤ) (64 : ℤ) = Finset.Ioc (-65 : ℤ) (-1 : ℤ) ∪ Finset.Ioc (-1 : ℤ) (64 : ℤ) from (Finset.Ioc_union_Ioc_eq_Ioc (by norm_num) (by norm_num)).symm, Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le (le_refl _))]
  rw [show Finset.Ioc (-1 : ℤ) (64 : ℤ) = Finset.Ioc (-1 : ℤ) (63 : ℤ) ∪ Finset.Ioc (63 : ℤ) (64 : ℤ) from (Finset.Ioc_union_Ioc_eq_Ioc (by norm_num) (by norm_num)).symm, Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le (le_refl _))]
  rw [h0, h1, h2]
  norm_num

theorem window_covered_P : ∀ n ∈ window, SampleCovered 68 (2 * n + 0) := by
  intro n hn
  have hb := Finset.mem_Icc.mp hn
  apply sampleCovered_of_bound
  omega
theorem window_covered_M : ∀ n ∈ window, SampleCovered 68 (2 * n + 1) := by
  intro n hn
  have hb := Finset.mem_Icc.mp hn
  apply sampleCovered_of_bound
  omega
theorem window_bound :
    (∑ n ∈ window, CircleQ.sigP n * ‖trial n‖ ^ 2) +
      KsIndex.AlphaRemark.spectralLower ^ 2 *
        ∑ m ∈ window, CircleQ.sigM m * ‖CircleQ.convS trial m‖ ^ 2 ≤
      ((-16455583780620473902026269186934053812416507089644783642273512289915069780094443862819369300268555622424272037871 / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  have h := finite_trial_energy_le_table valid window window
    KsIndex.AlphaRemark.spectralLower (by simpa using window_covered_P) window_covered_M
  refine h.trans ?_
  rw [window_P_c, window_P_r, window_Mm_c, window_Mm_r, KsIndex.AlphaRemark.spectralLower]
  push_cast
  norm_num
end KsIndex.NegSignProto
