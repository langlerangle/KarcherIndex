module

public import KsIndexLean.ProtoValid
public import KsIndexLean.NegSignEndpointBridge

@[expose] public section

/-! Tail Pp: K = 130, c = 391, sign +1. -/
set_option maxHeartbeats 2000000
set_option linter.style.longLine false
namespace KsIndex.NegSignProto
open KsIndex.AlphaRemarkTrial PowerArc
def kPp : Fin 25 → ℤ := ![136,135,134,133,132,131,129,128,127,126,125,124,136,135,134,133,132,131,130,129,128,127,126,125,124]
def kqPp : Fin 25 → ℚ := ![136,135,134,133,132,131,129,128,127,126,125,124,136,135,134,133,132,131,130,129,128,127,126,125,124]
noncomputable def rPp : Fin 25 → ℝ := fun i => ((kPp i : ℤ) : ℝ)
def cenPp : Fin 25 → ℚ := ![(-270337085351317454241429471327116309 / 5000000000000000000000000000000000000 : ℚ),(-13438415456977857736872955310232205689013527 / 200000000000000000000000000000000000000000000 : ℚ),(272087261223323690657568213438714291 / 5000000000000000000000000000000000000 : ℚ),(338151817747738574431237278387522946865718687 / 5000000000000000000000000000000000000000000000 : ℚ),(-136937772511820895480946444402761813 / 2500000000000000000000000000000000000 : ℚ),(-170195665121360973834566179698293876051307611 / 2500000000000000000000000000000000000000000000 : ℚ),(342680743197779835606498729419955353437541367 / 5000000000000000000000000000000000000000000000 : ℚ),(-138786118288895948923081326751443057 / 2500000000000000000000000000000000000 : ℚ),(-172510987287555978775275386890301250271406723 / 2500000000000000000000000000000000000000000000 : ℚ),(139741871168835040944469549212168741 / 2500000000000000000000000000000000000 : ℚ),(86854262008187942699123371545550743564989709 / 1250000000000000000000000000000000000000000000 : ℚ),(-140719781693533013559856553603914869 / 2500000000000000000000000000000000000 : ℚ),(-91838023962777580849089907126485061 / 2500000000000000000000000000000000000 : ℚ),(-37225369383590337281703034641411048821494671 / 1250000000000000000000000000000000000000000000 : ℚ),(92619405179606014938810589086770481 / 2500000000000000000000000000000000000 : ℚ),(150177935426316656902164600576899490756308617 / 5000000000000000000000000000000000000000000000 : ℚ),(-93419425992154819567063713500665771 / 2500000000000000000000000000000000000 : ℚ),(-30297015251613104921845438844171080094673339 / 1000000000000000000000000000000000000000000000 : ℚ),(301564242986293933661185017364523 / 8000000000000000000000000000000000 : ℚ),(152824126865075245579276931717033786693706829 / 5000000000000000000000000000000000000000000000 : ℚ),(-95078385943990264189032604801204461 / 2500000000000000000000000000000000000 : ℚ),(-3854909582997843504619508951854294300223897 / 125000000000000000000000000000000000000000000 : ℚ),(95938931389865013465766496474542107 / 2500000000000000000000000000000000000 : ℚ),(19450402001916598056900440855517233071037409 / 625000000000000000000000000000000000000000000 : ℚ),(-48410667674137173255651537965349899 / 1250000000000000000000000000000000000 : ℚ)]
def radPp : Fin 25 → ℚ := ![(11596750753 / 1250000000000000000000000000000000000 : ℚ),(280087715439639659505326554767945861 / 1000000000000000000000000000000000000000000000 : ℚ),(45034841203 / 5000000000000000000000000000000000000 : ℚ),(1409573478479510434454637761021668413 / 5000000000000000000000000000000000000000000000 : ℚ),(21851339697 / 2500000000000000000000000000000000000 : ℚ),(709454402182804931662395903677180119 / 2500000000000000000000000000000000000000000000 : ℚ),(1428452138493550044546862634302874253 / 5000000000000000000000000000000000000000000000 : ℚ),(642161809 / 78125000000000000000000000000000000 : ℚ),(719105737909288790461881246048468627 / 2500000000000000000000000000000000000000000000 : ℚ),(39826193967 / 5000000000000000000000000000000000000 : ℚ),(362048812971288585758288006312061281 / 1250000000000000000000000000000000000000000000 : ℚ),(19287016079 / 2500000000000000000000000000000000000 : ℚ),(11608249247 / 1250000000000000000000000000000000000 : ℚ),(403181892197164536848883503714576289 / 5000000000000000000000000000000000000000000000 : ℚ),(45080158797 / 5000000000000000000000000000000000000 : ℚ),(101659542225619123094793366263931023 / 1250000000000000000000000000000000000000000000 : ℚ),(21873660303 / 2500000000000000000000000000000000000 : ℚ),(82035505216883250625037091575853177 / 1000000000000000000000000000000000000000000000 : ℚ),(8486896483 / 1000000000000000000000000000000000000 : ℚ),(8276065713131923045294215065652847 / 100000000000000000000000000000000000000000000 : ℚ),(642838191 / 78125000000000000000000000000000000 : ℚ),(417518957006558958716814829722607069 / 5000000000000000000000000000000000000000000000 : ℚ),(39868806033 / 5000000000000000000000000000000000000 : ℚ),(42132825075928881232420708928868513 / 500000000000000000000000000000000000000000000 : ℚ),(19307983921 / 2500000000000000000000000000000000000 : ℚ)]
theorem hePp_0 : |tailEndpoint rPp 0 - ((cenPp 0 : ℚ) : ℝ)| ≤ ((radPp 0 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 0 (by decide)
    (A := -396294664674371200750450501) (Z := 1000000000) (E := 68000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePp_1 : |tailEndpoint rPp 1 - ((cenPp 1 : ℚ) : ℝ)| ≤ ((radPp 1 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 1 (by decide)
    (A := -689366784809428152926851975) (Z := 719689657) (E := 2068100354428284506999763145)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePp_2 : |tailEndpoint rPp 2 - ((cenPp 2 : ℚ) : ℝ)| ≤ ((radPp 2 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 2 (by decide)
    (A := 404794288488538167835072899) (Z := 1000000000) (E := 67000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePp_3 : |tailEndpoint rPp 3 - ((cenPp 3 : ℚ) : ℝ)| ≤ ((radPp 3 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 3 (by decide)
    (A := 704263673102182623468471399) (Z := 719689657) (E := 2112791019306547917904931757)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePp_4 : |tailEndpoint rPp 4 - ((cenPp 4 : ℚ) : ℝ)| ≤ ((radPp 4 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 4 (by decide)
    (A := -413608186550731425469288714) (Z := 1000000000) (E := 66000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePp_5 : |tailEndpoint rPp 5 - ((cenPp 5 : ℚ) : ℝ)| ≤ ((radPp 5 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 5 (by decide)
    (A := -719715593599267235457417094) (Z := 719689657) (E := 2159146780797801753152079182)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePp_6 : |tailEndpoint rPp 6 - ((cenPp 6 : ℚ) : ℝ)| ≤ ((radPp 6 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 6 (by decide)
    (A := 735752181617353965716117759) (Z := 719689657) (E := 2207256544852061943208491517)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePp_7 : |tailEndpoint rPp 7 - ((cenPp 7 : ℚ) : ℝ)| ≤ ((radPp 7 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 7 (by decide)
    (A := -432246565721556165988318146) (Z := 1000000000) (E := 64000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePp_8 : |tailEndpoint rPp 8 - ((cenPp 8 : ℚ) : ℝ)| ≤ ((radPp 8 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 8 (by decide)
    (A := -752405148113419308864320342) (Z := 719689657) (E := 2257215444340257971933409606)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePp_9 : |tailEndpoint rPp 9 - ((cenPp 9 : ℚ) : ℝ)| ≤ ((radPp 9 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 9 (by decide)
    (A := 442107919774176174392937898) (Z := 1000000000) (E := 63000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePp_10 : |tailEndpoint rPp 10 - ((cenPp 10 : ℚ) : ℝ)| ≤ ((radPp 10 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 10 (by decide)
    (A := 769708460720995164555540372) (Z := 719689657) (E := 2309125382162985538287380036)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePp_11 : |tailEndpoint rPp 11 - ((cenPp 11 : ℚ) : ℝ)| ≤ ((radPp 11 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 11 (by decide)
    (A := -452357504616722668555364682) (Z := 1000000000) (E := 62000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePp_12 : |tailEndpoint rPp 12 - ((cenPp 12 : ℚ) : ℝ)| ≤ ((radPp 12 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 12 (by decide)
    (A := -268989125603191637677717142) (Z := 1000000000) (E := 68000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePp_13 : |tailEndpoint rPp 13 - ((cenPp 13 : ℚ) : ℝ)| ≤ ((radPp 13 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 13 (by decide)
    (A := -297402755960356107541751244) (Z := 738631771) (E := 594805511920712264571831279)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePp_14 : |tailEndpoint rPp 14 - ((cenPp 14 : ℚ) : ℝ)| ≤ ((radPp 14 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 14 (by decide)
    (A := 275309595734900889235672382) (Z := 1000000000) (E := 67000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePp_15 : |tailEndpoint rPp 15 - ((cenPp 15 : ℚ) : ℝ)| ≤ ((radPp 15 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 15 (by decide)
    (A := 304443631992346226739123397) (Z := 738631771) (E := 608887263984692502227943812)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePp_16 : |tailEndpoint rPp 16 - ((cenPp 16 : ℚ) : ℝ)| ≤ ((radPp 16 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 16 (by decide)
    (A := -281877016926910355311930762) (Z := 1000000000) (E := 66000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePp_17 : |tailEndpoint rPp 17 - ((cenPp 17 : ℚ) : ℝ)| ≤ ((radPp 17 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 17 (by decide)
    (A := -311761715643852168459517995) (Z := 738631771) (E := 623523431287704384930101235)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePp_18 : |tailEndpoint rPp 18 - ((cenPp 18 : ℚ) : ℝ)| ≤ ((radPp 18 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 18 (by decide)
    (A := 288705002962110267440283125) (Z := 1000000000) (E := 65000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePp_19 : |tailEndpoint rPp 19 - ((cenPp 19 : ℚ) : ℝ)| ≤ ((radPp 19 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 19 (by decide)
    (A := 319372407651555171775773689) (Z := 738631771) (E := 638744815303110390823980850)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePp_20 : |tailEndpoint rPp 20 - ((cenPp 20 : ℚ) : ℝ)| ≤ ((radPp 20 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 20 (by decide)
    (A := -295808143558136122590863942) (Z := 1000000000) (E := 64000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePp_21 : |tailEndpoint rPp 21 - ((cenPp 21 : ℚ) : ℝ)| ≤ ((radPp 21 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 21 (by decide)
    (A := -327292221520927185305355080) (Z := 738631771) (E := 654584443041854417144511859)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePp_22 : |tailEndpoint rPp 22 - ((cenPp 22 : ℚ) : ℝ)| ≤ ((radPp 22 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 22 (by decide)
    (A := 303202091006119488340950954) (Z := 1000000000) (E := 63000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePp_23 : |tailEndpoint rPp 23 - ((cenPp 23 : ℚ) : ℝ)| ≤ ((radPp 23 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 23 (by decide)
    (A := 335538883106339085043211752) (Z := 738631771) (E := 671077766212678215881593430)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePp_24 : |tailEndpoint rPp 24 - ((cenPp 24 : ℚ) : ℝ)| ≤ ((radPp 24 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 24 (by decide)
    (A := -310903656029257032221079956) (Z := 1000000000) (E := 62000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePp : ∀ i, |tailEndpoint rPp i - ((cenPp i : ℚ) : ℝ)| ≤ ((radPp i : ℚ) : ℝ) := by
  intro i
  fin_cases i
  · exact hePp_0
  · exact hePp_1
  · exact hePp_2
  · exact hePp_3
  · exact hePp_4
  · exact hePp_5
  · exact hePp_6
  · exact hePp_7
  · exact hePp_8
  · exact hePp_9
  · exact hePp_10
  · exact hePp_11
  · exact hePp_12
  · exact hePp_13
  · exact hePp_14
  · exact hePp_15
  · exact hePp_16
  · exact hePp_17
  · exact hePp_18
  · exact hePp_19
  · exact hePp_20
  · exact hePp_21
  · exact hePp_22
  · exact hePp_23
  · exact hePp_24
theorem leadPp : tailLeading rPp ≤ ((tailLeadingUpperQ cenPp radPp : ℚ) : ℝ) :=
  tailLeading_le_Q rPp cenPp radPp (by decide +kernel) hePp
theorem errPp : tailError rPp ((391 : ℚ) : ℝ) ≤
    ((tailErrorUpperQ kqPp 391 cenPp radPp : ℚ) : ℝ) :=
  tailError_le_Q rPp kqPp 391 cenPp radPp
    (fun i => by fin_cases i <;> norm_num [rPp, kPp, kqPp])
    (by decide +kernel) (by decide +kernel) hePp
theorem leadValPp : tailLeadingUpperQ cenPp radPp = (2141214303378295332417463682108507272686954085169938453218093839345052304629825914980333118243948738782900323045565192833143 / 25565111864662500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by decide +kernel
theorem errValPp : tailErrorUpperQ kqPp 391 cenPp radPp = (89169165737694626838771252901682553734209869308228489351797128295336616164485862184990531396548159572645382166781492618709944630899245847 / 113371047585108062379751621500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by decide +kernel
end KsIndex.NegSignProto
