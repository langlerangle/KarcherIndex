module

public import KsIndexLean.PowerArcStieltjesAssembly
public import KsIndexLean.AlphaStieltjesSeedPrefixCertificate
public import KsIndexLean.AlphaStieltjesInitialCoefficients
public import KsIndexLean.StieltjesScalarEnclosure

@[expose] public section

/-! Full normalized Stieltjes seed intervals, including the infinite tail. -/
namespace KsIndex.PowerArc
theorem stieltjes_full_b14_interval :
    |powerArcStieltjes (2161809 / 5000000 : ℝ) 14 (2057/2) / g (2161809 / 5000000 : ℝ) 0 - (71426451 / 500000000000 : ℝ)| ≤
      1 / 10000000000 := by
  let T : ℝ := (395886591176361499288670881805922340465452328437360019 / 28548265596016882571798129000000000000000000000000000000 : ℝ)
  let E : ℝ := (11907674965992205103712115410136675213259191980013072237483 / 7647078766479569582341450771277874793214669000000000000000000000000 : ℝ)
  have hp : |normalizedStieltjesPrefix (2161809 / 5000000 : ℝ) 14 (2057/2) 32768 - (13863488943026704403213801411 / 1000000000000000000000000000000 : ℝ)| ≤ (1 / 500000000000000000000000 : ℝ) := by
    convert! stieltjesSeedPrefix_b14_error using 1
    all_goals norm_num only [stieltjesSeedPrefix, normalizedStieltjesPrefix, Int.cast_ofNat]
  have hq : |normalizedCoefficient (2161809 / 5000000 : ℝ) 14 32768 - (1104254595826965287821613 / 200000000000000000000000000000 : ℝ)| ≤ (1 / 30517578125000000000000000 : ℝ) := by
    convert! stieltjesSeedEndpoint_b14_error using 1
    all_goals norm_num
  have hh := normalized_powerArcStieltjes_enclosure (2161809 / 5000000 : ℝ) 14 (82161809 / 10000000 : ℝ) (2057/2) 1
    (13863488943026704403213801411 / 1000000000000000000000000000000 : ℝ) (1104254595826965287821613 / 200000000000000000000000000000 : ℝ) (1 / 500000000000000000000000 : ℝ) (1 / 30517578125000000000000000 : ℝ) 32768
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp hq
  have hH : |powerArcStieltjes (2161809 / 5000000 : ℝ) 14 (2057/2) / g (2161809 / 5000000 : ℝ) 0 -
      (g (2161809 / 5000000 : ℝ) 14 / g (2161809 / 5000000 : ℝ) 0) * T| ≤ |g (2161809 / 5000000 : ℝ) 14 / g (2161809 / 5000000 : ℝ) 0| * E := by
    convert! hh using 1
    all_goals norm_num [T, E]
  exact scalar_enclosure_transfer _ _ (1287680201 / 125000000000 : ℝ) T E (1/10000000000) (71426451 / 500000000000 : ℝ)
    (1/10000000000) hH (by
      convert! stieltjesInitial_b14_error using 1
      all_goals norm_num) (by norm_num [E]) (by norm_num [T, E])

theorem stieltjes_full_b15_interval :
    |powerArcStieltjes (2161809 / 5000000 : ℝ) 15 (2057/2) / g (2161809 / 5000000 : ℝ) 0 - (-85257617 / 500000000000 : ℝ)| ≤
      1 / 10000000000 := by
  let T : ℝ := (140389205515402133014311657866761418515558424956235613 / 9516233699594214992266043000000000000000000000000000000 : ℝ)
  let E : ℝ := (91934679946021544640634508302575701522889392515328884924771 / 53531184535665197210985734113091641422502683000000000000000000000000 : ℝ)
  have hp : |normalizedStieltjesPrefix (2161809 / 5000000 : ℝ) 15 (2057/2) 32768 - (14748424018608785814253409991 / 1000000000000000000000000000000 : ℝ)| ≤ (1 / 500000000000000000000000 : ℝ) := by
    convert! stieltjesSeedPrefix_b15_error using 1
    all_goals norm_num only [stieltjesSeedPrefix, normalizedStieltjesPrefix, Int.cast_ofNat]
  have hq : |normalizedCoefficient (2161809 / 5000000 : ℝ) 15 32768 - (6095643370439698259701659 / 1000000000000000000000000000000 : ℝ)| ≤ (1 / 30517578125000000000000000 : ℝ) := by
    convert! stieltjesSeedEndpoint_b15_error using 1
    all_goals norm_num
  have hh := normalized_powerArcStieltjes_enclosure (2161809 / 5000000 : ℝ) 15 (87161809 / 10000000 : ℝ) (2057/2) 1
    (14748424018608785814253409991 / 1000000000000000000000000000000 : ℝ) (6095643370439698259701659 / 1000000000000000000000000000000 : ℝ) (1 / 500000000000000000000000 : ℝ) (1 / 30517578125000000000000000 : ℝ) 32768
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp hq
  have hH : |powerArcStieltjes (2161809 / 5000000 : ℝ) 15 (2057/2) / g (2161809 / 5000000 : ℝ) 0 -
      (g (2161809 / 5000000 : ℝ) 15 / g (2161809 / 5000000 : ℝ) 0) * T| ≤ |g (2161809 / 5000000 : ℝ) 15 / g (2161809 / 5000000 : ℝ) 0| * E := by
    convert! hh using 1
    all_goals norm_num [T, E]
  exact scalar_enclosure_transfer _ _ (-5779158047 / 500000000000 : ℝ) T E (1/10000000000) (-85257617 / 500000000000 : ℝ)
    (1/10000000000) hH (by
      convert! stieltjesInitial_b15_error using 1
      all_goals norm_num) (by norm_num [E]) (by norm_num [T, E])

theorem stieltjes_full_c14_interval :
    |powerArcStieltjes (2838191 / 5000000 : ℝ) 14 (2057/2) / g (2838191 / 5000000 : ℝ) 0 - (108177701 / 1000000000000 : ℝ)| ≤
      1 / 10000000000 := by
  let T : ℝ := (124975002197110642965348948584107253513954607914968129 / 10994060729896441397733957000000000000000000000000000000 : ℝ)
  let E : ℝ := (1095457936353655786273520350842842562314226746361676526263 / 2295746187429411405975729257586058662946332750000000000000000000000 : ℝ)
  have hp : |normalizedStieltjesPrefix (2838191 / 5000000 : ℝ) 14 (2057/2) 32768 - (11366400885265198921139809997 / 1000000000000000000000000000000 : ℝ)| ≤ (1 / 500000000000000000000000 : ℝ) := by
    convert! stieltjesSeedPrefix_c14_error using 1
    all_goals norm_num only [stieltjesSeedPrefix, normalizedStieltjesPrefix, Int.cast_ofNat]
  have hq : |normalizedCoefficient (2838191 / 5000000 : ℝ) 14 32768 - (879420935706179892587627 / 500000000000000000000000000000 : ℝ)| ≤ (1 / 30517578125000000000000000 : ℝ) := by
    convert! stieltjesSeedEndpoint_c14_error using 1
    all_goals norm_num
  have hh := normalized_powerArcStieltjes_enclosure (2838191 / 5000000 : ℝ) 14 (82838191 / 10000000 : ℝ) (2057/2) 1
    (11366400885265198921139809997 / 1000000000000000000000000000000 : ℝ) (879420935706179892587627 / 500000000000000000000000000000 : ℝ) (1 / 500000000000000000000000 : ℝ) (1 / 30517578125000000000000000 : ℝ) 32768
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp hq
  have hH : |powerArcStieltjes (2838191 / 5000000 : ℝ) 14 (2057/2) / g (2838191 / 5000000 : ℝ) 0 -
      (g (2838191 / 5000000 : ℝ) 14 / g (2838191 / 5000000 : ℝ) 0) * T| ≤ |g (2838191 / 5000000 : ℝ) 14 / g (2838191 / 5000000 : ℝ) 0| * E := by
    convert! hh using 1
    all_goals norm_num [T, E]
  exact scalar_enclosure_transfer _ _ (9516400877 / 1000000000000 : ℝ) T E (1/10000000000) (108177701 / 1000000000000 : ℝ)
    (1/10000000000) hH stieltjesInitial_c14_error (by norm_num [E]) (by norm_num [T, E])

theorem stieltjes_full_c15_interval :
    |powerArcStieltjes (2838191 / 5000000 : ℝ) 15 (2057/2) / g (2838191 / 5000000 : ℝ) 0 - (-83421663 / 1000000000000 : ℝ)| ≤
      1 / 10000000000 := by
  let T : ℝ := (10788400742261878228875344221502153967787768535917751 / 891423927855542881032483000000000000000000000000000000 : ℝ)
  let E : ℝ := (1422939368438761849473518717301158357837832326040415130401 / 2678452268102116563525431463004423351354054875000000000000000000000 : ℝ)
  have hp : |normalizedStieltjesPrefix (2838191 / 5000000 : ℝ) 15 (2057/2) 32768 - (12101209015989524492755234397 / 1000000000000000000000000000000 : ℝ)| ≤ (1 / 500000000000000000000000 : ℝ) := by
    convert! stieltjesSeedPrefix_c15_error using 1
    all_goals norm_num only [stieltjesSeedPrefix, normalizedStieltjesPrefix, Int.cast_ofNat]
  have hq : |normalizedCoefficient (2838191 / 5000000 : ℝ) 15 32768 - (7840733426513692468613 / 4000000000000000000000000000 : ℝ)| ≤ (1 / 30517578125000000000000000 : ℝ) := by
    convert! stieltjesSeedEndpoint_c15_error using 1
    all_goals norm_num
  have hh := normalized_powerArcStieltjes_enclosure (2838191 / 5000000 : ℝ) 15 (87838191 / 10000000 : ℝ) (2057/2) 1
    (12101209015989524492755234397 / 1000000000000000000000000000000 : ℝ) (7840733426513692468613 / 4000000000000000000000000000 : ℝ) (1 / 500000000000000000000000 : ℝ) (1 / 30517578125000000000000000 : ℝ) 32768
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp hq
  have hH : |powerArcStieltjes (2838191 / 5000000 : ℝ) 15 (2057/2) / g (2838191 / 5000000 : ℝ) 0 -
      (g (2838191 / 5000000 : ℝ) 15 / g (2838191 / 5000000 : ℝ) 0) * T| ≤ |g (2838191 / 5000000 : ℝ) 15 / g (2838191 / 5000000 : ℝ) 0| * E := by
    convert! hh using 1
    all_goals norm_num [T, E]
  exact scalar_enclosure_transfer _ _ (-1378592951 / 200000000000 : ℝ) T E (1/10000000000) (-83421663 / 1000000000000 : ℝ)
    (1/10000000000) hH (by
      convert! stieltjesInitial_c15_error using 1
      all_goals norm_num) (by norm_num [E]) (by norm_num [T, E])

end KsIndex.PowerArc
