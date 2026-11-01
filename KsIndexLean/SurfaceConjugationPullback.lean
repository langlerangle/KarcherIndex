module

public import KsIndexLean.SurfaceSym

@[expose] public section


/-! Coordinate conjugation preserves the disk-chain compact smooth domain.
This is complex-linear pullback, not conjugation of function values. -/
noncomputable section
open scoped ContDiff
namespace KsIndex.SurfaceSym
open KsIndex.Surface KsIndex.SurfaceForm
variable {k m : ℕ}

lemma coordinateConjugation_mem_CcSmooth
    {u : ZMod (2*m) → ℂ → ℂ} (hu : u ∈ CcSmooth k m) :
    (fun n w => u n (starRingEnd ℂ w)) ∈ CcSmooth k m := by
  obtain ⟨⟨hsm1,hsm2,hsm3⟩,⟨ε,hε,hz⟩⟩ := hu
  have hc : ContDiff ℝ ∞ (fun w : ℂ => starRingEnd ℂ w) := Complex.conjCLE.contDiff
  refine ⟨⟨fun n => ?_, fun n w hw => ?_, fun n w hw => ?_⟩,
    ⟨ε,hε,fun n w hw => ?_⟩⟩
  · exact (hsm1 n).comp hc.contDiffOn (fun w hw => by simpa [mem_disk_iff] using hw)
  · have hg : glue (fun n w => u n (starRingEnd ℂ w)) n =
        fun w => glue u n (starRingEnd ℂ w) := by
      funext w
      simp only [glue, map_div₀, map_one, Complex.norm_conj]
    rw [hg]
    have hm : starRingEnd ℂ w ∈ seamArc k m n := by
      obtain ⟨hw1,hw2⟩ := hw
      refine ⟨by simpa using hw1, ?_⟩
      simpa only [← map_pow, Complex.conj_re] using hw2
    exact (hsm2 n _ hm).comp w hc.contDiffAt
  · exact hsm3 n _ (by simpa using hw)
  · obtain ⟨p,hp,hwp⟩ := hw
    refine hz n (starRingEnd ℂ w) ⟨starRingEnd ℂ p, ?_, ?_⟩
    · change (starRingEnd ℂ p) ^ (2*k) = -1
      rw [← map_pow, hp, map_neg, map_one]
    · simpa only [← map_sub, Complex.norm_conj] using hwp

end KsIndex.SurfaceSym
