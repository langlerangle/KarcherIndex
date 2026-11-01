module

public import KsIndexLean.SphericalNormedCarrier

@[expose] public section


open Set
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

/-- Integral H1 squared quantity evaluated on the canonically recovered matching pair. -/
def sphereChartH1Squared {A : Set Circle₁} (hA : IsOpen A) (q : SphereChartSpace A hA) : ℝ :=
  sphereJoinedH1Squared (chartDiskPair hA q).val.1 (chartDiskPair hA q).val.2

lemma sphereChartH1Squared_matchingPair {A : Set Circle₁} (hA : IsOpen A)
    (p : MatchingDiskPair A) :
    sphereChartH1Squared hA (matchingPairClass hA p) = sphereJoinedH1Squared p.val.1 p.val.2 := by
  rw [sphereChartH1Squared, chartDiskPair_join]

/-- The complete transported norm and the integral H1 quantity are quantitatively equivalent. -/
theorem sphereChartH1Squared_norm_comparison {A : Set Circle₁} (hA : IsOpen A)
    (q : SphereChartSpace A hA) :
    ‖q‖ ^ 2 ≤ sphereChartH1Squared hA q ∧ sphereChartH1Squared hA q ≤ 8 * ‖q‖ ^ 2 := by
  obtain ⟨p, rfl⟩ := matchingPairClass_surjective hA q
  rw [sphereChartH1Squared_matchingPair, sphereChart_norm_matchingPair]
  have h := sphereJoinedH1Squared_comparison p.val.1 p.val.2
  have hu := norm_nonneg p.val.1
  have hv := norm_nonneg p.val.2
  rcases le_total ‖p.val.1‖ ‖p.val.2‖ with hh | hh
  · rw [max_eq_right hh]
    constructor
    · nlinarith [h.1, sq_nonneg ‖p.val.1‖]
    · nlinarith [h.2]
  · rw [max_eq_left hh]
    constructor
    · nlinarith [h.1, sq_nonneg ‖p.val.2‖]
    · nlinarith [h.2]

end KsIndex.Spherical
