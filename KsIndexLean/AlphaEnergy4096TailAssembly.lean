module
public import KsIndexLean.AlphaEnergy4096RowTotals
public import KsIndexLean.AlphaEnergy4096Endpoints
public import KsIndexLean.CorrectedTrialTailEnclosure
@[expose] public section
namespace KsIndex.AlphaRemarkTrial.Energy4096Rows
open PowerArc
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.style.longLine false
namespace Pplus
theorem endpoint_intervals (i : Fin 25) :
    |g (exponent i) (point i) / g (exponent i) 0 - center i| ≤ radius i := by
  fin_cases i
  · convert Energy4096Endpoints.Pplus_0 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pplus_1 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pplus_2 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pplus_3 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pplus_4 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pplus_5 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pplus_6 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pplus_7 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pplus_8 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pplus_9 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pplus_10 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pplus_11 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pplus_12 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pplus_13 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pplus_14 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pplus_15 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pplus_16 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pplus_17 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pplus_18 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pplus_19 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pplus_20 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pplus_21 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pplus_22 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pplus_23 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pplus_24 using 1 <;>
      norm_num [point, center, radius]
theorem corrected_interval :
    Summable (fun n : ℕ => ((6*n+24583)-4/(6*n+24583))*
      (∑ i, tailScale i*g (exponent i) (point i+2*n))^2) ∧
    (179241989291030386906351864472924809693574164392806940713903412393628940372654147679108096707049899018849059885158050967149063207961244178348751533233699872814784780881 / 11768682240187284552150523090281843927658967120160436625325000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (∑' n : ℕ, ((6*n+24583)-4/(6*n+24583))*
      (∑ i, tailScale i*g (exponent i) (point i+2*n))^2) ∧
    (∑' n : ℕ, ((6*n+24583)-4/(6*n+24583))*
      (∑ i, tailScale i*g (exponent i) (point i+2*n))^2) ≤ (298865811386807388299910555712411837306944593033938452707330391109498526878718652027805886582200417880263573983248524571987678362509920697600945031181469402679 / 19474130436348321408407078692005577703811353252925000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  have h := corrected_trial_tail_enclosure point center radius 24583
    (by norm_num) (by intro i; fin_cases i <;> norm_num [point])
    (by intro i; fin_cases i <;> norm_num [radius]) endpoint_intervals
  rw [center_total, product_total, radius_total] at h
  convert h using 1 <;> norm_num
#print axioms corrected_interval
end Pplus
namespace Pminus
theorem endpoint_intervals (i : Fin 25) :
    |g (exponent i) (point i) / g (exponent i) 0 - center i| ≤ radius i := by
  fin_cases i
  · convert Energy4096Endpoints.Pminus_0 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pminus_1 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pminus_2 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pminus_3 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pminus_4 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pminus_5 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pminus_6 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pminus_7 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pminus_8 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pminus_9 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pminus_10 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pminus_11 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pminus_12 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pminus_13 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pminus_14 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pminus_15 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pminus_16 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pminus_17 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pminus_18 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pminus_19 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pminus_20 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pminus_21 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pminus_22 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pminus_23 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Pminus_24 using 1 <;>
      norm_num [point, center, radius]
theorem corrected_interval :
    Summable (fun n : ℕ => ((6*n+24581)-4/(6*n+24581))*
      (∑ i, tailScale i*g (exponent i) (point i+2*n))^2) ∧
    (1316462595430924564886410040504990422486858450696245055313128703315428737617514710604844037702972018561496654255165030432620794769226034699543146454144829251839971131 / 11281656172473383791373995435329066541912278770295093975000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (∑' n : ℕ, ((6*n+24581)-4/(6*n+24581))*
      (∑ i, tailScale i*g (exponent i) (point i+2*n))^2) ∧
    (∑' n : ℕ, ((6*n+24581)-4/(6*n+24581))*
      (∑ i, tailScale i*g (exponent i) (point i+2*n))^2) ≤ (2180933061888215525397692524044181002054290408148614548598896058853660203400089649251037351896074193212901278218197915636650795023378395859171108790754276221 / 18671265998416415540179365955901800291286052975000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  have h := corrected_trial_tail_enclosure point center radius 24581
    (by norm_num) (by intro i; fin_cases i <;> norm_num [point])
    (by intro i; fin_cases i <;> norm_num [radius]) endpoint_intervals
  rw [center_total, product_total, radius_total] at h
  convert h using 1 <;> norm_num
#print axioms corrected_interval
end Pminus
namespace Mplus
theorem endpoint_intervals (i : Fin 25) :
    |g (exponent i) (point i) / g (exponent i) 0 - center i| ≤ radius i := by
  fin_cases i
  · convert Energy4096Endpoints.Mplus_0 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mplus_1 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mplus_2 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mplus_3 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mplus_4 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mplus_5 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mplus_6 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mplus_7 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mplus_8 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mplus_9 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mplus_10 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mplus_11 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mplus_12 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mplus_13 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mplus_14 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mplus_15 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mplus_16 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mplus_17 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mplus_18 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mplus_19 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mplus_20 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mplus_21 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mplus_22 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mplus_23 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mplus_24 using 1 <;>
      norm_num [point, center, radius]
theorem corrected_interval :
    Summable (fun n : ℕ => ((6*n+24586)-4/(6*n+24586))*
      (∑ i, tailScale i*g (exponent i) (point i+2*n))^2) ∧
    (153907791849399628110235993254919899602388380149038301554175950096292880942829347500702835120076862982621164653651154654438662824389084499821927012090875379916196706349 / 2024587419196500418044442781476621562197160436268101073425000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (∑' n : ℕ, ((6*n+24586)-4/(6*n+24586))*
      (∑ i, tailScale i*g (exponent i) (point i+2*n))^2) ∧
    (∑' n : ℕ, ((6*n+24586)-4/(6*n+24586))*
      (∑ i, tailScale i*g (exponent i) (point i+2*n))^2) ≤ (2039485913349283848291549337717531726964849493754757145442664616003358799385009239917178818116579989690626500015323669160577095804868614082980521341902673187359 / 26794815206726512075280303671826635941557908705650000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  have h := corrected_trial_tail_enclosure point center radius 24586
    (by norm_num) (by intro i; fin_cases i <;> norm_num [point])
    (by intro i; fin_cases i <;> norm_num [radius]) endpoint_intervals
  rw [center_total, product_total, radius_total] at h
  convert h using 1 <;> norm_num
#print axioms corrected_interval
end Mplus
namespace Mminus
theorem endpoint_intervals (i : Fin 25) :
    |g (exponent i) (point i) / g (exponent i) 0 - center i| ≤ radius i := by
  fin_cases i
  · convert Energy4096Endpoints.Mminus_0 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mminus_1 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mminus_2 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mminus_3 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mminus_4 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mminus_5 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mminus_6 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mminus_7 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mminus_8 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mminus_9 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mminus_10 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mminus_11 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mminus_12 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mminus_13 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mminus_14 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mminus_15 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mminus_16 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mminus_17 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mminus_18 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mminus_19 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mminus_20 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mminus_21 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mminus_22 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mminus_23 using 1 <;>
      norm_num [point, center, radius]
  · convert Energy4096Endpoints.Mminus_24 using 1 <;>
      norm_num [point, center, radius]
theorem corrected_interval :
    Summable (fun n : ℕ => ((6*n+24578)-4/(6*n+24578))*
      (∑ i, tailScale i*g (exponent i) (point i+2*n))^2) ∧
    (10999364043090874779612809816621992899924571309510324075474147674712274910016094210890744014360434075663021225928974705999591924927000785526568971432725575054650600366287 / 1109273169439753352385856109329645136900862467027652410672175000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ (∑' n : ℕ, ((6*n+24578)-4/(6*n+24578))*
      (∑ i, tailScale i*g (exponent i) (point i+2*n))^2) ∧
    (∑' n : ℕ, ((6*n+24578)-4/(6*n+24578))*
      (∑ i, tailScale i*g (exponent i) (point i+2*n))^2) ≤ (49024372722116971049076394419647201022028843367873289833890819064212784773154167153965934051766604099847983470358551820772699058483996853140419515821240737339211 / 4896820234869960298646230903838562419582222826357450000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  have h := corrected_trial_tail_enclosure point center radius 24578
    (by norm_num) (by intro i; fin_cases i <;> norm_num [point])
    (by intro i; fin_cases i <;> norm_num [radius]) endpoint_intervals
  rw [center_total, product_total, radius_total] at h
  convert h using 1 <;> norm_num
#print axioms corrected_interval
end Mminus
end KsIndex.AlphaRemarkTrial.Energy4096Rows
