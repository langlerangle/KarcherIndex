module

public import KsIndexLean.AlphaTrialInnerEndpointBounds

public import KsIndexLean.AlphaQTailSamples

@[expose] public section


/-! Concrete bounds for the inner truncation endpoints at T=16385. -/

noncomputable section

namespace KsIndex.AlphaRemarkTrial

open PowerArc

set_option maxRecDepth 10000

set_option maxHeartbeats 2000000

lemma inner_abs_b_32777 : |g (2161809/5000000 : ℝ) 32777/g (2161809/5000000 : ℝ) 0| ≤ (1901382701/10000000000000000 : ℝ) := by
  have hh := qsample_b_32777
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

lemma inner_abs_b_32776 : |g (2161809/5000000 : ℝ) 32776/g (2161809/5000000 : ℝ) 0| ≤ (767488973/5000000000000000 : ℝ) := by
  have hh := qsample_b_32776
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

lemma inner_abs_b_32775 : |g (2161809/5000000 : ℝ) 32775/g (2161809/5000000 : ℝ) 0| ≤ (380309779/2000000000000000 : ℝ) := by
  have hh := qsample_b_32775
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

lemma inner_abs_b_32774 : |g (2161809/5000000 : ℝ) 32774/g (2161809/5000000 : ℝ) 0| ≤ (1535112117/10000000000000000 : ℝ) := by
  have hh := qsample_b_32774
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

lemma inner_abs_b_32773 : |g (2161809/5000000 : ℝ) 32773/g (2161809/5000000 : ℝ) 0| ≤ (950857557/5000000000000000 : ℝ) := by
  have hh := qsample_b_32773
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

lemma inner_abs_b_32772 : |g (2161809/5000000 : ℝ) 32772/g (2161809/5000000 : ℝ) 0| ≤ (1535246309/10000000000000000 : ℝ) := by
  have hh := qsample_b_32772
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

lemma inner_abs_b_32770 : |g (2161809/5000000 : ℝ) 32770/g (2161809/5000000 : ℝ) 0| ≤ (1535380521/10000000000000000 : ℝ) := by
  have hh := qsample_b_32770
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

lemma inner_abs_b_32769 : |g (2161809/5000000 : ℝ) 32769/g (2161809/5000000 : ℝ) 0| ≤ (15216381/80000000000000 : ℝ) := by
  have hh := qsample_b_32769
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

lemma inner_abs_b_32768 : |g (2161809/5000000 : ℝ) 32768/g (2161809/5000000 : ℝ) 0| ≤ (11996209/78125000000000 : ℝ) := by
  have hh := qsample_b_32768
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

lemma inner_abs_b_32767 : |g (2161809/5000000 : ℝ) 32767/g (2161809/5000000 : ℝ) 0| ≤ (951106959/5000000000000000 : ℝ) := by
  have hh := qsample_b_32767
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

lemma inner_abs_b_32766 : |g (2161809/5000000 : ℝ) 32766/g (2161809/5000000 : ℝ) 0| ≤ (383912251/2500000000000000 : ℝ) := by
  have hh := qsample_b_32766
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

lemma inner_abs_b_32765 : |g (2161809/5000000 : ℝ) 32765/g (2161809/5000000 : ℝ) 0| ≤ (380476047/2000000000000000 : ℝ) := by
  have hh := qsample_b_32765
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

def innerEndpointBoundsA : Fin 12 → ℝ := ![(1901382701/10000000000000000 : ℝ), (767488973/5000000000000000 : ℝ), (380309779/2000000000000000 : ℝ), (1535112117/10000000000000000 : ℝ), (950857557/5000000000000000 : ℝ), (1535246309/10000000000000000 : ℝ), (1535380521/10000000000000000 : ℝ), (15216381/80000000000000 : ℝ), (11996209/78125000000000 : ℝ), (951106959/5000000000000000 : ℝ), (383912251/2500000000000000 : ℝ), (380476047/2000000000000000 : ℝ)]

lemma innerEndpointsA_bound (i : Fin 12) :
    |g (2161809/5000000 : ℝ) (32771+shift (familyIndexA i))/g (2161809/5000000 : ℝ) 0| ≤ innerEndpointBoundsA i := by
  fin_cases i

  · convert inner_abs_b_32777 using 1 <;> norm_num [familyIndexA, shift, innerEndpointBoundsA]

  · convert inner_abs_b_32776 using 1 <;> norm_num [familyIndexA, shift, innerEndpointBoundsA]

  · convert inner_abs_b_32775 using 1 <;> norm_num [familyIndexA, shift, innerEndpointBoundsA]

  · convert inner_abs_b_32774 using 1 <;> norm_num [familyIndexA, shift, innerEndpointBoundsA]

  · convert inner_abs_b_32773 using 1 <;> norm_num [familyIndexA, shift, innerEndpointBoundsA]

  · convert inner_abs_b_32772 using 1 <;> norm_num [familyIndexA, shift, innerEndpointBoundsA]

  · convert inner_abs_b_32770 using 1 <;> norm_num [familyIndexA, shift, innerEndpointBoundsA]

  · convert inner_abs_b_32769 using 1 <;> norm_num [familyIndexA, shift, innerEndpointBoundsA]

  · convert inner_abs_b_32768 using 1 <;> norm_num [familyIndexA, shift, innerEndpointBoundsA]

  · convert inner_abs_b_32767 using 1 <;> norm_num [familyIndexA, shift, innerEndpointBoundsA]

  · convert inner_abs_b_32766 using 1 <;> norm_num [familyIndexA, shift, innerEndpointBoundsA]

  · convert inner_abs_b_32765 using 1 <;> norm_num [familyIndexA, shift, innerEndpointBoundsA]

theorem trialInnerUA_16385 : trialInnerUA 16385 ≤ (31/1000000000 : ℝ) := by
  have he : trialInnerUA 16385 = ∑ i : Fin 12,
      |(coefficient (familyIndexA i)).re| * ((1+9/(32771:ℝ))/(2*((2161809/5000000)+1))) *
      |g (2161809/5000000 : ℝ) (32771+shift (familyIndexA i))/g (2161809/5000000 : ℝ) 0| := by
    unfold trialInnerUA
    apply Finset.sum_congr rfl
    intro i _
    norm_num only [Nat.cast_ofNat]
    rw [abs_div, abs_div]
    ring_nf
  rw [he]
  calc
    _ ≤ ∑ i : Fin 12, |(coefficient (familyIndexA i)).re| * ((1+9/(32771:ℝ))/(2*((2161809/5000000)+1))) * innerEndpointBoundsA i := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left (innerEndpointsA_bound i)
      fin_cases i <;> norm_num [familyIndexA, coefficient, shift]
    _ ≤ _ := by norm_num [Fin.sum_univ_succ, familyIndexA, coefficient, shift, innerEndpointBoundsA]
#print axioms trialInnerUA_16385

lemma inner_abs_c_32777 : |g (2838191/5000000 : ℝ) 32777/g (2838191/5000000 : ℝ) 0| ≤ (400477229/10000000000000000 : ℝ) := by
  have hh := qsample_c_32777
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

lemma inner_abs_c_32776 : |g (2838191/5000000 : ℝ) 32776/g (2838191/5000000 : ℝ) 0| ≤ (496117973/10000000000000000 : ℝ) := by
  have hh := qsample_c_32776
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

lemma inner_abs_c_32775 : |g (2838191/5000000 : ℝ) 32775/g (2838191/5000000 : ℝ) 0| ≤ (20025777/500000000000000 : ℝ) := by
  have hh := qsample_c_32775
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

lemma inner_abs_c_32774 : |g (2838191/5000000 : ℝ) 32774/g (2838191/5000000 : ℝ) 0| ≤ (248082717/5000000000000000 : ℝ) := by
  have hh := qsample_c_32774
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

lemma inner_abs_c_32773 : |g (2838191/5000000 : ℝ) 32773/g (2838191/5000000 : ℝ) 0| ≤ (400553857/10000000000000000 : ℝ) := by
  have hh := qsample_c_32773
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

lemma inner_abs_c_32772 : |g (2838191/5000000 : ℝ) 32772/g (2838191/5000000 : ℝ) 0| ≤ (496212903/10000000000000000 : ℝ) := by
  have hh := qsample_c_32772
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

lemma inner_abs_c_32771 : |g (2838191/5000000 : ℝ) 32771/g (2838191/5000000 : ℝ) 0| ≤ (400592179/10000000000000000 : ℝ) := by
  have hh := qsample_c_32771
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

lemma inner_abs_c_32770 : |g (2838191/5000000 : ℝ) 32770/g (2838191/5000000 : ℝ) 0| ≤ (496260379/10000000000000000 : ℝ) := by
  have hh := qsample_c_32770
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

lemma inner_abs_c_32769 : |g (2838191/5000000 : ℝ) 32769/g (2838191/5000000 : ℝ) 0| ≤ (100157627/2500000000000000 : ℝ) := by
  have hh := qsample_c_32769
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

lemma inner_abs_c_32768 : |g (2838191/5000000 : ℝ) 32768/g (2838191/5000000 : ℝ) 0| ≤ (248153931/5000000000000000 : ℝ) := by
  have hh := qsample_c_32768
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

lemma inner_abs_c_32767 : |g (2838191/5000000 : ℝ) 32767/g (2838191/5000000 : ℝ) 0| ≤ (200334421/5000000000000000 : ℝ) := by
  have hh := qsample_c_32767
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

lemma inner_abs_c_32766 : |g (2838191/5000000 : ℝ) 32766/g (2838191/5000000 : ℝ) 0| ≤ (496355353/10000000000000000 : ℝ) := by
  have hh := qsample_c_32766
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

lemma inner_abs_c_32765 : |g (2838191/5000000 : ℝ) 32765/g (2838191/5000000 : ℝ) 0| ≤ (400707183/10000000000000000 : ℝ) := by
  have hh := qsample_c_32765
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

def innerEndpointBoundsB : Fin 13 → ℝ := ![(400477229/10000000000000000 : ℝ), (496117973/10000000000000000 : ℝ), (20025777/500000000000000 : ℝ), (248082717/5000000000000000 : ℝ), (400553857/10000000000000000 : ℝ), (496212903/10000000000000000 : ℝ), (400592179/10000000000000000 : ℝ), (496260379/10000000000000000 : ℝ), (100157627/2500000000000000 : ℝ), (248153931/5000000000000000 : ℝ), (200334421/5000000000000000 : ℝ), (496355353/10000000000000000 : ℝ), (400707183/10000000000000000 : ℝ)]

lemma innerEndpointsB_bound (i : Fin 13) :
    |g (2838191/5000000 : ℝ) (32771+shift (familyIndexB i))/g (2838191/5000000 : ℝ) 0| ≤ innerEndpointBoundsB i := by
  fin_cases i

  · convert inner_abs_c_32777 using 1 <;> norm_num [familyIndexB, shift, innerEndpointBoundsB]

  · convert inner_abs_c_32776 using 1 <;> norm_num [familyIndexB, shift, innerEndpointBoundsB]

  · convert inner_abs_c_32775 using 1 <;> norm_num [familyIndexB, shift, innerEndpointBoundsB]

  · convert inner_abs_c_32774 using 1 <;> norm_num [familyIndexB, shift, innerEndpointBoundsB]

  · convert inner_abs_c_32773 using 1 <;> norm_num [familyIndexB, shift, innerEndpointBoundsB]

  · convert inner_abs_c_32772 using 1 <;> norm_num [familyIndexB, shift, innerEndpointBoundsB]

  · convert inner_abs_c_32771 using 1 <;> norm_num [familyIndexB, shift, innerEndpointBoundsB]

  · convert inner_abs_c_32770 using 1 <;> norm_num [familyIndexB, shift, innerEndpointBoundsB]

  · convert inner_abs_c_32769 using 1 <;> norm_num [familyIndexB, shift, innerEndpointBoundsB]

  · convert inner_abs_c_32768 using 1 <;> norm_num [familyIndexB, shift, innerEndpointBoundsB]

  · convert inner_abs_c_32767 using 1 <;> norm_num [familyIndexB, shift, innerEndpointBoundsB]

  · convert inner_abs_c_32766 using 1 <;> norm_num [familyIndexB, shift, innerEndpointBoundsB]

  · convert inner_abs_c_32765 using 1 <;> norm_num [familyIndexB, shift, innerEndpointBoundsB]

theorem trialInnerUB_16385 : trialInnerUB 16385 ≤ (7/10000000000000 : ℝ) := by
  have he : trialInnerUB 16385 = ∑ i : Fin 13,
      |(coefficient (familyIndexB i)).re| * ((1+11/(32771:ℝ))^2/(2*((2838191/5000000)+2)*(32771+shift (familyIndexB i)+(2838191/5000000)+2))) *
      |g (2838191/5000000 : ℝ) (32771+shift (familyIndexB i))/g (2838191/5000000 : ℝ) 0| := by
    unfold trialInnerUB
    apply Finset.sum_congr rfl
    intro i _
    norm_num only [Nat.cast_ofNat]
    rw [abs_div, abs_div]
    ring_nf
  rw [he]
  calc
    _ ≤ ∑ i : Fin 13, |(coefficient (familyIndexB i)).re| * ((1+11/(32771:ℝ))^2/(2*((2838191/5000000)+2)*(32771+shift (familyIndexB i)+(2838191/5000000)+2))) * innerEndpointBoundsB i := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left (innerEndpointsB_bound i)
      fin_cases i <;> norm_num [familyIndexB, coefficient, shift]
    _ ≤ _ := by norm_num [Fin.sum_univ_succ, familyIndexB, coefficient, shift, innerEndpointBoundsB]
#print axioms trialInnerUB_16385

end KsIndex.AlphaRemarkTrial
