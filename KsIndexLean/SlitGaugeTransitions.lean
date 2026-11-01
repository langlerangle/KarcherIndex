module

public import KsIndexLean.SlitSeamGauges

@[expose] public section


noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma joinedDiskJet_inner_transition (u v : ComplexH1) (c : ℂ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    joinedDiskJet u v c z = joinedDiskJet u v 1 z := by
  simp [joinedDiskJet, reconstructedJet, reconstructedX, reconstructedY,
    joinedDiskRadial, joinedDiskAngular, radialJoin, hz]

lemma joinedDiskJet_outer_transition (u v : ComplexH1) (c : ℂ) {z : ℂ} (hz : 1 < ‖z‖) :
    joinedDiskJet u v c z = c • joinedDiskJet u v 1 z := by
  ext d
  simp [joinedDiskJet, reconstructedJet, reconstructedX, reconstructedY,
    joinedDiskRadial, joinedDiskAngular, radialJoin, not_le.mpr hz,
    smul_add, smul_sub]
  ring

end KsIndex.Trace
