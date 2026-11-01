module

public import KsIndexLean.ProtoValid
public import KsIndexLean.NegSignEndpointBridge

@[expose] public section

/-! Tail Mp: K = 131, c = 394, sign +1. -/
set_option maxHeartbeats 2000000
set_option linter.style.longLine false
namespace KsIndex.NegSignProto
open KsIndex.AlphaRemarkTrial PowerArc
def kMp : Fin 25 → ℤ := ![137,136,135,134,133,132,130,129,128,127,126,125,137,136,135,134,133,132,131,130,129,128,127,126,125]
def kqMp : Fin 25 → ℚ := ![137,136,135,134,133,132,130,129,128,127,126,125,137,136,135,134,133,132,131,130,129,128,127,126,125]
noncomputable def rMp : Fin 25 → ℝ := fun i => ((kMp i : ℤ) : ℝ)
def cenMp : Fin 25 → ℚ := ![(166907654599792634767685068099027743964446103 / 2500000000000000000000000000000000000000000000 : ℚ),(-270337085351317454241429471327116309 / 5000000000000000000000000000000000000 : ℚ),(-13438415456977857736872955310232205689013527 / 200000000000000000000000000000000000000000000 : ℚ),(272087261223323690657568213438714291 / 5000000000000000000000000000000000000 : ℚ),(338151817747738574431237278387522946865718687 / 5000000000000000000000000000000000000000000000 : ℚ),(-136937772511820895480946444402761813 / 2500000000000000000000000000000000000 : ℚ),(27570336754579999461888457276322073 / 500000000000000000000000000000000000 : ℚ),(342680743197779835606498729419955353437541367 / 5000000000000000000000000000000000000000000000 : ℚ),(-138786118288895948923081326751443057 / 2500000000000000000000000000000000000 : ℚ),(-172510987287555978775275386890301250271406723 / 2500000000000000000000000000000000000000000000 : ℚ),(139741871168835040944469549212168741 / 2500000000000000000000000000000000000 : ℚ),(86854262008187942699123371545550743564989709 / 1250000000000000000000000000000000000000000000 : ℚ),(147654540318264811503898601210368878922292517 / 5000000000000000000000000000000000000000000000 : ℚ),(-91838023962777580849089907126485061 / 2500000000000000000000000000000000000 : ℚ),(-37225369383590337281703034641411048821494671 / 1250000000000000000000000000000000000000000000 : ℚ),(92619405179606014938810589086770481 / 2500000000000000000000000000000000000 : ℚ),(150177935426316656902164600576899490756308617 / 5000000000000000000000000000000000000000000000 : ℚ),(-93419425992154819567063713500665771 / 2500000000000000000000000000000000000 : ℚ),(-30297015251613104921845438844171080094673339 / 1000000000000000000000000000000000000000000000 : ℚ),(301564242986293933661185017364523 / 8000000000000000000000000000000000 : ℚ),(152824126865075245579276931717033786693706829 / 5000000000000000000000000000000000000000000000 : ℚ),(-95078385943990264189032604801204461 / 2500000000000000000000000000000000000 : ℚ),(-3854909582997843504619508951854294300223897 / 125000000000000000000000000000000000000000000 : ℚ),(95938931389865013465766496474542107 / 2500000000000000000000000000000000000 : ℚ),(19450402001916598056900440855517233071037409 / 625000000000000000000000000000000000000000000 : ℚ)]
def radMp : Fin 25 → ℚ := ![(695748450639992894054132111671680997 / 2500000000000000000000000000000000000000000000 : ℚ),(11596750753 / 1250000000000000000000000000000000000 : ℚ),(280087715439639659505326554767945861 / 1000000000000000000000000000000000000000000000 : ℚ),(45034841203 / 5000000000000000000000000000000000000 : ℚ),(1409573478479510434454637761021668413 / 5000000000000000000000000000000000000000000000 : ℚ),(21851339697 / 2500000000000000000000000000000000000 : ℚ),(8478103517 / 1000000000000000000000000000000000000 : ℚ),(1428452138493550044546862634302874253 / 5000000000000000000000000000000000000000000000 : ℚ),(642161809 / 78125000000000000000000000000000000 : ℚ),(719105737909288790461881246048468627 / 2500000000000000000000000000000000000000000000 : ℚ),(39826193967 / 5000000000000000000000000000000000000 : ℚ),(362048812971288585758288006312061281 / 1250000000000000000000000000000000000000000000 : ℚ),(199902774447898510803472905741395589 / 2500000000000000000000000000000000000000000000 : ℚ),(11608249247 / 1250000000000000000000000000000000000 : ℚ),(403181892197164536848883503714576289 / 5000000000000000000000000000000000000000000000 : ℚ),(45080158797 / 5000000000000000000000000000000000000 : ℚ),(101659542225619123094793366263931023 / 1250000000000000000000000000000000000000000000 : ℚ),(21873660303 / 2500000000000000000000000000000000000 : ℚ),(82035505216883250625037091575853177 / 1000000000000000000000000000000000000000000000 : ℚ),(8486896483 / 1000000000000000000000000000000000000 : ℚ),(8276065713131923045294215065652847 / 100000000000000000000000000000000000000000000 : ℚ),(642838191 / 78125000000000000000000000000000000 : ℚ),(417518957006558958716814829722607069 / 5000000000000000000000000000000000000000000000 : ℚ),(39868806033 / 5000000000000000000000000000000000000 : ℚ),(42132825075928881232420708928868513 / 500000000000000000000000000000000000000000000 : ℚ)]
theorem heMp_0 : |tailEndpoint rMp 0 - ((cenMp 0 : ℚ) : ℝ)| ≤ ((radMp 0 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 0 (by decide)
    (A := 674997204954767674173484862) (Z := 719689657) (E := 2024991614864303071459351466)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMp_1 : |tailEndpoint rMp 1 - ((cenMp 1 : ℚ) : ℝ)| ≤ ((radMp 1 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 1 (by decide)
    (A := -396294664674371200750450501) (Z := 1000000000) (E := 68000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMp_2 : |tailEndpoint rMp 2 - ((cenMp 2 : ℚ) : ℝ)| ≤ ((radMp 2 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 2 (by decide)
    (A := -689366784809428152926851975) (Z := 719689657) (E := 2068100354428284506999763145)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMp_3 : |tailEndpoint rMp 3 - ((cenMp 3 : ℚ) : ℝ)| ≤ ((radMp 3 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 3 (by decide)
    (A := 404794288488538167835072899) (Z := 1000000000) (E := 67000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMp_4 : |tailEndpoint rMp 4 - ((cenMp 4 : ℚ) : ℝ)| ≤ ((radMp 4 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 4 (by decide)
    (A := 704263673102182623468471399) (Z := 719689657) (E := 2112791019306547917904931757)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMp_5 : |tailEndpoint rMp 5 - ((cenMp 5 : ℚ) : ℝ)| ≤ ((radMp 5 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 5 (by decide)
    (A := -413608186550731425469288714) (Z := 1000000000) (E := 66000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMp_6 : |tailEndpoint rMp 6 - ((cenMp 6 : ℚ) : ℝ)| ≤ ((radMp 6 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 6 (by decide)
    (A := 422753009668801373523674970) (Z := 1000000000) (E := 65000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMp_7 : |tailEndpoint rMp 7 - ((cenMp 7 : ℚ) : ℝ)| ≤ ((radMp 7 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 7 (by decide)
    (A := 735752181617353965716117759) (Z := 719689657) (E := 2207256544852061943208491517)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMp_8 : |tailEndpoint rMp 8 - ((cenMp 8 : ℚ) : ℝ)| ≤ ((radMp 8 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 8 (by decide)
    (A := -432246565721556165988318146) (Z := 1000000000) (E := 64000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMp_9 : |tailEndpoint rMp 9 - ((cenMp 9 : ℚ) : ℝ)| ≤ ((radMp 9 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 9 (by decide)
    (A := -752405148113419308864320342) (Z := 719689657) (E := 2257215444340257971933409606)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMp_10 : |tailEndpoint rMp 10 - ((cenMp 10 : ℚ) : ℝ)| ≤ ((radMp 10 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 10 (by decide)
    (A := 442107919774176174392937898) (Z := 1000000000) (E := 63000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMp_11 : |tailEndpoint rMp 11 - ((cenMp 11 : ℚ) : ℝ)| ≤ ((radMp 11 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 11 (by decide)
    (A := 769708460720995164555540372) (Z := 719689657) (E := 2309125382162985538287380036)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMp_12 : |tailEndpoint rMp 12 - ((cenMp 12 : ℚ) : ℝ)| ≤ ((radMp 12 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 12 (by decide)
    (A := 290624709508022205079133297) (Z := 738631771) (E := 581249419016044460385227158)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMp_13 : |tailEndpoint rMp 13 - ((cenMp 13 : ℚ) : ℝ)| ≤ ((radMp 13 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 13 (by decide)
    (A := -268989125603191637677717142) (Z := 1000000000) (E := 68000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMp_14 : |tailEndpoint rMp 14 - ((cenMp 14 : ℚ) : ℝ)| ≤ ((radMp 14 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 14 (by decide)
    (A := -297402755960356107541751244) (Z := 738631771) (E := 594805511920712264571831279)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMp_15 : |tailEndpoint rMp 15 - ((cenMp 15 : ℚ) : ℝ)| ≤ ((radMp 15 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 15 (by decide)
    (A := 275309595734900889235672382) (Z := 1000000000) (E := 67000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMp_16 : |tailEndpoint rMp 16 - ((cenMp 16 : ℚ) : ℝ)| ≤ ((radMp 16 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 16 (by decide)
    (A := 304443631992346226739123397) (Z := 738631771) (E := 608887263984692502227943812)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMp_17 : |tailEndpoint rMp 17 - ((cenMp 17 : ℚ) : ℝ)| ≤ ((radMp 17 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 17 (by decide)
    (A := -281877016926910355311930762) (Z := 1000000000) (E := 66000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMp_18 : |tailEndpoint rMp 18 - ((cenMp 18 : ℚ) : ℝ)| ≤ ((radMp 18 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 18 (by decide)
    (A := -311761715643852168459517995) (Z := 738631771) (E := 623523431287704384930101235)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMp_19 : |tailEndpoint rMp 19 - ((cenMp 19 : ℚ) : ℝ)| ≤ ((radMp 19 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 19 (by decide)
    (A := 288705002962110267440283125) (Z := 1000000000) (E := 65000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMp_20 : |tailEndpoint rMp 20 - ((cenMp 20 : ℚ) : ℝ)| ≤ ((radMp 20 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 20 (by decide)
    (A := 319372407651555171775773689) (Z := 738631771) (E := 638744815303110390823980850)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMp_21 : |tailEndpoint rMp 21 - ((cenMp 21 : ℚ) : ℝ)| ≤ ((radMp 21 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 21 (by decide)
    (A := -295808143558136122590863942) (Z := 1000000000) (E := 64000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMp_22 : |tailEndpoint rMp 22 - ((cenMp 22 : ℚ) : ℝ)| ≤ ((radMp 22 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 22 (by decide)
    (A := -327292221520927185305355080) (Z := 738631771) (E := 654584443041854417144511859)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMp_23 : |tailEndpoint rMp 23 - ((cenMp 23 : ℚ) : ℝ)| ≤ ((radMp 23 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 23 (by decide)
    (A := 303202091006119488340950954) (Z := 1000000000) (E := 63000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMp_24 : |tailEndpoint rMp 24 - ((cenMp 24 : ℚ) : ℝ)| ≤ ((radMp 24 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 24 (by decide)
    (A := 335538883106339085043211752) (Z := 738631771) (E := 671077766212678215881593430)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem heMp : ∀ i, |tailEndpoint rMp i - ((cenMp i : ℚ) : ℝ)| ≤ ((radMp i : ℚ) : ℝ) := by
  intro i
  fin_cases i
  · exact heMp_0
  · exact heMp_1
  · exact heMp_2
  · exact heMp_3
  · exact heMp_4
  · exact heMp_5
  · exact heMp_6
  · exact heMp_7
  · exact heMp_8
  · exact heMp_9
  · exact heMp_10
  · exact heMp_11
  · exact heMp_12
  · exact heMp_13
  · exact heMp_14
  · exact heMp_15
  · exact heMp_16
  · exact heMp_17
  · exact heMp_18
  · exact heMp_19
  · exact heMp_20
  · exact heMp_21
  · exact heMp_22
  · exact heMp_23
  · exact heMp_24
theorem leadMp : tailLeading rMp ≤ ((tailLeadingUpperQ cenMp radMp : ℚ) : ℝ) :=
  tailLeading_le_Q rMp cenMp radMp (by decide +kernel) heMp
theorem errMp : tailError rMp ((394 : ℚ) : ℝ) ≤
    ((tailErrorUpperQ kqMp 394 cenMp radMp : ℚ) : ℝ) :=
  tailError_le_Q rMp kqMp 394 cenMp radMp
    (fun i => by fin_cases i <;> norm_num [rMp, kMp, kqMp])
    (by decide +kernel) (by decide +kernel) heMp
theorem leadValMp : tailLeadingUpperQ cenMp radMp = (10760217318570846344163686929095085916542174556956853402557714526768521063218167918311333501114305187608913236890866301552639 / 2556511186466250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by decide +kernel
theorem errValMp : tailErrorUpperQ kqMp 394 cenMp radMp = (4704789211594323445803668606698824728701322666212246371450871710864956978158975505189919970876516454101489518523347158639205928456946169611923 / 6262836096435405058881440381250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by decide +kernel
end KsIndex.NegSignProto
