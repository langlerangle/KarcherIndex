module

public import KsIndexLean.ProtoValid
public import KsIndexLean.NegSignEndpointBridge

@[expose] public section

/-! Tail Mn: K = 129, c = 386, sign -1. -/
set_option maxHeartbeats 2000000
set_option linter.style.longLine false
namespace KsIndex.NegSignProto
open KsIndex.AlphaRemarkTrial PowerArc
def kMn : Fin 25 → ℤ := ![123,124,125,126,127,128,130,131,132,133,134,135,123,124,125,126,127,128,129,130,131,132,133,134,135]
def kqMn : Fin 25 → ℚ := ![123,124,125,126,127,128,130,131,132,133,134,135,123,124,125,126,127,128,129,130,131,132,133,134,135]
noncomputable def rMn : Fin 25 → ℝ := fun i => ((kMn i : ℤ) : ℝ)
def cenMn : Fin 25 → ℚ := ![(-349868100569034174491774274682619833427808819 / 5000000000000000000000000000000000000000000000 : ℚ),(-140719781693533013559856553603914869 / 2500000000000000000000000000000000000 : ℚ),(86854262008187942699123371545550743564989709 / 1250000000000000000000000000000000000000000000 : ℚ),(139741871168835040944469549212168741 / 2500000000000000000000000000000000000 : ℚ),(-172510987287555978775275386890301250271406723 / 2500000000000000000000000000000000000000000000 : ℚ),(-138786118288895948923081326751443057 / 2500000000000000000000000000000000000 : ℚ),(27570336754579999461888457276322073 / 500000000000000000000000000000000000 : ℚ),(-170195665121360973834566179698293876051307611 / 2500000000000000000000000000000000000000000000 : ℚ),(-136937772511820895480946444402761813 / 2500000000000000000000000000000000000 : ℚ),(338151817747738574431237278387522946865718687 / 5000000000000000000000000000000000000000000000 : ℚ),(272087261223323690657568213438714291 / 5000000000000000000000000000000000000 : ℚ),(-13438415456977857736872955310232205689013527 / 200000000000000000000000000000000000000000000 : ℚ),(-15704607520965986267659482116893686844558163 / 500000000000000000000000000000000000000000000 : ℚ),(-48410667674137173255651537965349899 / 1250000000000000000000000000000000000 : ℚ),(19450402001916598056900440855517233071037409 / 625000000000000000000000000000000000000000000 : ℚ),(95938931389865013465766496474542107 / 2500000000000000000000000000000000000 : ℚ),(-3854909582997843504619508951854294300223897 / 125000000000000000000000000000000000000000000 : ℚ),(-95078385943990264189032604801204461 / 2500000000000000000000000000000000000 : ℚ),(152824126865075245579276931717033786693706829 / 5000000000000000000000000000000000000000000000 : ℚ),(301564242986293933661185017364523 / 8000000000000000000000000000000000 : ℚ),(-30297015251613104921845438844171080094673339 / 1000000000000000000000000000000000000000000000 : ℚ),(-93419425992154819567063713500665771 / 2500000000000000000000000000000000000 : ℚ),(150177935426316656902164600576899490756308617 / 5000000000000000000000000000000000000000000000 : ℚ),(92619405179606014938810589086770481 / 2500000000000000000000000000000000000 : ℚ),(-37225369383590337281703034641411048821494671 / 1250000000000000000000000000000000000000000000 : ℚ)]
def radMn : Fin 25 → ℚ := ![(1458412374692641363018282146383973741 / 5000000000000000000000000000000000000000000000 : ℚ),(19287016079 / 2500000000000000000000000000000000000 : ℚ),(362048812971288585758288006312061281 / 1250000000000000000000000000000000000000000000 : ℚ),(39826193967 / 5000000000000000000000000000000000000 : ℚ),(719105737909288790461881246048468627 / 2500000000000000000000000000000000000000000000 : ℚ),(642161809 / 78125000000000000000000000000000000 : ℚ),(8478103517 / 1000000000000000000000000000000000000 : ℚ),(709454402182804931662395903677180119 / 2500000000000000000000000000000000000000000000 : ℚ),(21851339697 / 2500000000000000000000000000000000000 : ℚ),(1409573478479510434454637761021668413 / 5000000000000000000000000000000000000000000000 : ℚ),(45034841203 / 5000000000000000000000000000000000000 : ℚ),(280087715439639659505326554767945861 / 1000000000000000000000000000000000000000000000 : ℚ),(425235093792519447305174720014668283 / 5000000000000000000000000000000000000000000000 : ℚ),(19307983921 / 2500000000000000000000000000000000000 : ℚ),(42132825075928881232420708928868513 / 500000000000000000000000000000000000000000000 : ℚ),(39868806033 / 5000000000000000000000000000000000000 : ℚ),(417518957006558958716814829722607069 / 5000000000000000000000000000000000000000000000 : ℚ),(642838191 / 78125000000000000000000000000000000 : ℚ),(8276065713131923045294215065652847 / 100000000000000000000000000000000000000000000 : ℚ),(8486896483 / 1000000000000000000000000000000000000 : ℚ),(82035505216883250625037091575853177 / 1000000000000000000000000000000000000000000000 : ℚ),(21873660303 / 2500000000000000000000000000000000000 : ℚ),(101659542225619123094793366263931023 / 1250000000000000000000000000000000000000000000 : ℚ),(45080158797 / 5000000000000000000000000000000000000 : ℚ),(403181892197164536848883503714576289 / 5000000000000000000000000000000000000000000000 : ℚ)]
theorem heMn_0 : |tailEndpoint rMn 0 - ((cenMn 0 : ℚ) : ℝ)| ≤ ((radMn 0 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 0 (by decide)
    (A := -787698543788020501618681563) (Z := 719689657) (E := 2363095631364061548757113949)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMn_1 : |tailEndpoint rMn 1 - ((cenMn 1 : ℚ) : ℝ)| ≤ ((radMn 1 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 1 (by decide)
    (A := -452357504616722668555364682) (Z := 1000000000) (E := 62000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMn_2 : |tailEndpoint rMn 2 - ((cenMn 2 : ℚ) : ℝ)| ≤ ((radMn 2 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 2 (by decide)
    (A := 769708460720995164555540372) (Z := 719689657) (E := 2309125382162985538287380036)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMn_3 : |tailEndpoint rMn 3 - ((cenMn 3 : ℚ) : ℝ)| ≤ ((radMn 3 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 3 (by decide)
    (A := 442107919774176174392937898) (Z := 1000000000) (E := 63000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMn_4 : |tailEndpoint rMn 4 - ((cenMn 4 : ℚ) : ℝ)| ≤ ((radMn 4 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 4 (by decide)
    (A := -752405148113419308864320342) (Z := 719689657) (E := 2257215444340257971933409606)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMn_5 : |tailEndpoint rMn 5 - ((cenMn 5 : ℚ) : ℝ)| ≤ ((radMn 5 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 5 (by decide)
    (A := -432246565721556165988318146) (Z := 1000000000) (E := 64000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMn_6 : |tailEndpoint rMn 6 - ((cenMn 6 : ℚ) : ℝ)| ≤ ((radMn 6 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 6 (by decide)
    (A := 422753009668801373523674970) (Z := 1000000000) (E := 65000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMn_7 : |tailEndpoint rMn 7 - ((cenMn 7 : ℚ) : ℝ)| ≤ ((radMn 7 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 7 (by decide)
    (A := -719715593599267235457417094) (Z := 719689657) (E := 2159146780797801753152079182)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMn_8 : |tailEndpoint rMn 8 - ((cenMn 8 : ℚ) : ℝ)| ≤ ((radMn 8 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 8 (by decide)
    (A := -413608186550731425469288714) (Z := 1000000000) (E := 66000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMn_9 : |tailEndpoint rMn 9 - ((cenMn 9 : ℚ) : ℝ)| ≤ ((radMn 9 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 9 (by decide)
    (A := 704263673102182623468471399) (Z := 719689657) (E := 2112791019306547917904931757)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMn_10 : |tailEndpoint rMn 10 - ((cenMn 10 : ℚ) : ℝ)| ≤ ((radMn 10 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 10 (by decide)
    (A := 404794288488538167835072899) (Z := 1000000000) (E := 67000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMn_11 : |tailEndpoint rMn 11 - ((cenMn 11 : ℚ) : ℝ)| ≤ ((radMn 11 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 11 (by decide)
    (A := -689366784809428152926851975) (Z := 719689657) (E := 2068100354428284506999763145)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMn_12 : |tailEndpoint rMn 12 - ((cenMn 12 : ℚ) : ℝ)| ≤ ((radMn 12 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 12 (by decide)
    (A := -344131440874718781723485830) (Z := 738631771) (E := 688262881749437608503509813)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMn_13 : |tailEndpoint rMn 13 - ((cenMn 13 : ℚ) : ℝ)| ≤ ((radMn 13 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 13 (by decide)
    (A := -310903656029257032221079956) (Z := 1000000000) (E := 62000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMn_14 : |tailEndpoint rMn 14 - ((cenMn 14 : ℚ) : ℝ)| ≤ ((radMn 14 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 14 (by decide)
    (A := 335538883106339085043211752) (Z := 738631771) (E := 671077766212678215881593430)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMn_15 : |tailEndpoint rMn 15 - ((cenMn 15 : ℚ) : ℝ)| ≤ ((radMn 15 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 15 (by decide)
    (A := 303202091006119488340950954) (Z := 1000000000) (E := 63000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMn_16 : |tailEndpoint rMn 16 - ((cenMn 16 : ℚ) : ℝ)| ≤ ((radMn 16 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 16 (by decide)
    (A := -327292221520927185305355080) (Z := 738631771) (E := 654584443041854417144511859)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMn_17 : |tailEndpoint rMn 17 - ((cenMn 17 : ℚ) : ℝ)| ≤ ((radMn 17 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 17 (by decide)
    (A := -295808143558136122590863942) (Z := 1000000000) (E := 64000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMn_18 : |tailEndpoint rMn 18 - ((cenMn 18 : ℚ) : ℝ)| ≤ ((radMn 18 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 18 (by decide)
    (A := 319372407651555171775773689) (Z := 738631771) (E := 638744815303110390823980850)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMn_19 : |tailEndpoint rMn 19 - ((cenMn 19 : ℚ) : ℝ)| ≤ ((radMn 19 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 19 (by decide)
    (A := 288705002962110267440283125) (Z := 1000000000) (E := 65000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMn_20 : |tailEndpoint rMn 20 - ((cenMn 20 : ℚ) : ℝ)| ≤ ((radMn 20 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 20 (by decide)
    (A := -311761715643852168459517995) (Z := 738631771) (E := 623523431287704384930101235)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMn_21 : |tailEndpoint rMn 21 - ((cenMn 21 : ℚ) : ℝ)| ≤ ((radMn 21 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 21 (by decide)
    (A := -281877016926910355311930762) (Z := 1000000000) (E := 66000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMn_22 : |tailEndpoint rMn 22 - ((cenMn 22 : ℚ) : ℝ)| ≤ ((radMn 22 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 22 (by decide)
    (A := 304443631992346226739123397) (Z := 738631771) (E := 608887263984692502227943812)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMn_23 : |tailEndpoint rMn 23 - ((cenMn 23 : ℚ) : ℝ)| ≤ ((radMn 23 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 23 (by decide)
    (A := 275309595734900889235672382) (Z := 1000000000) (E := 67000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMn_24 : |tailEndpoint rMn 24 - ((cenMn 24 : ℚ) : ℝ)| ≤ ((radMn 24 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 24 (by decide)
    (A := -297402755960356107541751244) (Z := 738631771) (E := 594805511920712264571831279)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMn : ∀ i, |tailEndpoint rMn i - ((cenMn i : ℚ) : ℝ)| ≤ ((radMn i : ℚ) : ℝ) := by
  intro i
  fin_cases i
  · exact heMn_0
  · exact heMn_1
  · exact heMn_2
  · exact heMn_3
  · exact heMn_4
  · exact heMn_5
  · exact heMn_6
  · exact heMn_7
  · exact heMn_8
  · exact heMn_9
  · exact heMn_10
  · exact heMn_11
  · exact heMn_12
  · exact heMn_13
  · exact heMn_14
  · exact heMn_15
  · exact heMn_16
  · exact heMn_17
  · exact heMn_18
  · exact heMn_19
  · exact heMn_20
  · exact heMn_21
  · exact heMn_22
  · exact heMn_23
  · exact heMn_24
theorem leadMn : tailLeading rMn ≤ ((tailLeadingUpperQ cenMn radMn : ℚ) : ℝ) :=
  tailLeading_le_Q rMn cenMn radMn (by decide +kernel) heMn
theorem errMn : tailError rMn ((386 : ℚ) : ℝ) ≤
    ((tailErrorUpperQ kqMn 386 cenMn radMn : ℚ) : ℝ) :=
  tailError_le_Q rMn kqMn 386 cenMn radMn
    (fun i => by fin_cases i <;> norm_num [rMn, kMn, kqMn])
    (by decide +kernel) (by decide +kernel) heMn
theorem leadValMn : tailLeadingUpperQ cenMn radMn = (1401782296210441620249020541266030159124626389445536163222288991878460897700806844634102630496392966213721026714239426128491 / 25565111864662500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by decide +kernel
theorem errValMn : tailErrorUpperQ kqMn 386 cenMn radMn = (13238489389314937717455894044511991894719650483621260422310299661130909071587744749147467932135721705950378520468336214663071203092721509849 / 17089018202167024108712560593750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by decide +kernel
end KsIndex.NegSignProto
