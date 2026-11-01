module

public import KsIndexLean.AlphaMomentPrefixSeed

@[expose] public section

noncomputable section
namespace KsIndex.AlphaRemarkTrial
open PowerArc
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem trialMomentPrefix_affine : trialMomentPrefix =
    (1264941916427363125896987350338948262880601149909912732041771858335366113690139244883909316395901/2468712525512156170083542832856920629742685859411946285523113896328122341007498101095000000000000 : ℝ) +
    (g (2161809/5000000 : ℝ) 1/g (2161809/5000000 : ℝ) 0) * (-2817768567608603628593371725399553207661390516021/562951317591842185676440998451642755460648833000000 : ℝ) +
    (g (2838191/5000000 : ℝ) 1/g (2838191/5000000 : ℝ) 0) * (383670628334104116816364834302219499422868626219484029047253/2413926796319856920368781722915897564519007549840000000000000 : ℝ) := by
  rw [trialMomentPrefix_eq_seeded]
  norm_num [seededMomentPrefix, seededTrialValue, Finset.sum_range_succ,
    Fin.sum_univ_succ, coefficient, exponent, shift, integerSeedValue, normalizedCoefficient]
  ring

end KsIndex.AlphaRemarkTrial
#print axioms KsIndex.AlphaRemarkTrial.trialMomentPrefix_affine
