module

public import KsIndexLean.ProdValid
public import KsIndexLean.NegSignEndpointBridge

@[expose] public section

/-! Tail Mp: K = 16387, c = 49162, sign +1. -/
set_option maxHeartbeats 2000000
set_option linter.style.longLine false
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial PowerArc
def kMp : Fin 25 → ℤ := ![16393,16392,16391,16390,16389,16388,16386,16385,16384,16383,16382,16381,16393,16392,16391,16390,16389,16388,16387,16386,16385,16384,16383,16382,16381]
def kqMp : Fin 25 → ℚ := ![16393,16392,16391,16390,16389,16388,16386,16385,16384,16383,16382,16381,16393,16392,16391,16390,16389,16388,16387,16386,16385,16384,16383,16382,16381]
noncomputable def rMp : Fin 25 → ℝ := fun i => ((kMp i : ℤ) : ℝ)
def cenMp : Fin 25 → ℚ := ![(42045787806942787098805616342256272772608139 / 5000000000000000000000000000000000000000000000 : ℚ),(-16971396168607032292431095083769589 / 2500000000000000000000000000000000000 : ℚ),(-42048006033046959320069975101676964304112417 / 5000000000000000000000000000000000000000000000 : ℚ),(8486145794917850443510061380165651 / 1250000000000000000000000000000000000 : ℚ),(4205022464689732212032762721894842161640613 / 500000000000000000000000000000000000000000000 : ℚ),(-33946374335187318776918170188366657 / 5000000000000000000000000000000000000 : ℚ),(33948165803854759792624625839491681 / 5000000000000000000000000000000000000 : ℚ),(21027331519148556313991420253931099021519477 / 2500000000000000000000000000000000000000000000 : ℚ),(-33949957585766707963957526502788997 / 5000000000000000000000000000000000000 : ℚ),(-42056882816076907518370710855224822161165293 / 5000000000000000000000000000000000000000000000 : ℚ),(339517496810161853984577827422351 / 50000000000000000000000000000000000 : ℚ),(2102955149103181370297182679185168419724733 / 250000000000000000000000000000000000000000000 : ℚ),(9726137518720583990176068589746611667253049 / 5000000000000000000000000000000000000000000000 : ℚ),(-602437271293242929413252879127957 / 250000000000000000000000000000000000 : ℚ),(-1945362239108558952615680645739739041511893 / 1000000000000000000000000000000000000000000000 : ℚ),(1204958002806642562530555748623609 / 500000000000000000000000000000000000 : ℚ),(2431871250311585142514051358872000271966919 / 1250000000000000000000000000000000000000000000 : ℚ),(-241008295798915168307585407598241 / 100000000000000000000000000000000000 : ℚ),(-9728158935871611000715747646016518678208903 / 5000000000000000000000000000000000000000000000 : ℚ),(6025624855776450384187900151340089 / 2500000000000000000000000000000000000 : ℚ),(1216104124932376654246811036535475753357449 / 625000000000000000000000000000000000000000000 : ℚ),(-12052084792937918289154996893963217 / 5000000000000000000000000000000000000 : ℚ),(-2432376798012243011967515237165552669884473 / 1250000000000000000000000000000000000000000000 : ℚ),(6026460017075449194850348898522301 / 2500000000000000000000000000000000000 : ℚ),(1946036302736385965874917615540235265191781 / 1000000000000000000000000000000000000000000000 : ℚ)]
def radMp : Fin 25 → ℚ := ![(175266327915528628667844909179952921 / 5000000000000000000000000000000000000000000000 : ℚ),(167940469546641 / 1250000000000000000000000000000000000 : ℚ),(175275574509873434935324499015359343 / 5000000000000000000000000000000000000000000000 : ℚ),(134319593204951 / 1000000000000000000000000000000000000 : ℚ),(17528482272052404806441213911706163 / 500000000000000000000000000000000000000000000 : ℚ),(335717036931473 / 2500000000000000000000000000000000000 : ℚ),(671270201701137 / 5000000000000000000000000000000000000 : ℚ),(87651661996331121918326225577176023 / 2500000000000000000000000000000000000000000000 : ℚ),(81922161809 / 610351562500000000000000000000000 : ℚ),(175312577055110103652401654551779587 / 5000000000000000000000000000000000000000000000 : ℚ),(670942517377519 / 5000000000000000000000000000000000000 : ℚ),(8766091586789216244629614193281737 / 250000000000000000000000000000000000000000000 : ℚ),(13167775745329868244988463272822433 / 2500000000000000000000000000000000000000000000 : ℚ),(167941855453359 / 1250000000000000000000000000000000000 : ℚ),(5267475122310172936767573514515843 / 1000000000000000000000000000000000000000000000 : ℚ),(134320701795049 / 1000000000000000000000000000000000000 : ℚ),(13169600040707581093940332569501927 / 2500000000000000000000000000000000000000000000 : ℚ),(335719808068527 / 2500000000000000000000000000000000000 : ℚ),(5268204980072398452636708895154937 / 1000000000000000000000000000000000000000000000 : ℚ),(671275743298863 / 5000000000000000000000000000000000000 : ℚ),(329285625856259572469543207676207 / 62500000000000000000000000000000000000000000 : ℚ),(81922838191 / 610351562500000000000000000000000 : ℚ),(26344675585940941332135967985168517 / 5000000000000000000000000000000000000000000000 : ℚ),(670948057622481 / 5000000000000000000000000000000000000 : ℚ),(329331268159900313598619593583241 / 62500000000000000000000000000000000000000000 : ℚ)]
theorem heMp_0 : |tailEndpoint rMp 0 - ((cenMp 0 : ℚ) : ℝ)| ≤ ((radMp 0 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 0 (by decide)
    (A := 712750179653046065929203) (Z := 719689657) (E := 2138250538965036774240969)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMp, kMp, exponentQ]) (by norm_num [radMp, kMp, exponentQ])
theorem heMp_1 : |tailEndpoint rMp 1 - ((cenMp 1 : ℚ) : ℝ)| ≤ ((radMp 1 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 1 (by decide)
    (A := -414127587511813485344842) (Z := 1000000000) (E := 8196000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMp, kMp, exponentQ]) (by norm_num [radMp, kMp, exponentQ])
theorem heMp_2 : |tailEndpoint rMp 2 - ((cenMp 2 : ℚ) : ℝ)| ≤ ((radMp 2 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 2 (by decide)
    (A := -712874753267921831963609) (Z := 719689657) (E := 2138624259809663352654527)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMp, kMp, exponentQ]) (by norm_num [radMp, kMp, exponentQ])
theorem heMp_3 : |tailEndpoint rMp 3 - ((cenMp 3 : ℚ) : ℝ)| ≤ ((radMp 3 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 3 (by decide)
    (A := 414199972647257268815756) (Z := 1000000000) (E := 8195000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMp, kMp, exponentQ]) (by norm_num [radMp, kMp, exponentQ])
theorem heMp_4 : |tailEndpoint rMp 4 - ((cenMp 4 : ℚ) : ℝ)| ≤ ((radMp 4 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 4 (by decide)
    (A := 712999363860782349447010) (Z := 719689657) (E := 2138998091588244185415070)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMp, kMp, exponentQ]) (by norm_num [radMp, kMp, exponentQ])
theorem heMp_5 : |tailEndpoint rMp 5 - ((cenMp 5 : ℚ) : ℝ)| ≤ ((radMp 5 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 5 (by decide)
    (A := -414272379270556019959473) (Z := 1000000000) (E := 8194000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMp, kMp, exponentQ]) (by norm_num [radMp, kMp, exponentQ])
theorem heMp_6 : |tailEndpoint rMp 6 - ((cenMp 6 : ℚ) : ℝ)| ≤ ((radMp 6 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 6 (by decide)
    (A := 414344807390712062550609) (Z := 1000000000) (E := 8193000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMp, kMp, exponentQ]) (by norm_num [radMp, kMp, exponentQ])
theorem heMp_7 : |tailEndpoint rMp 7 - ((cenMp 7 : ℚ) : ℝ)| ≤ ((radMp 7 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 7 (by decide)
    (A := 713248696042429855314458) (Z := 719689657) (E := 2139746088133185263638094)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMp, kMp, exponentQ]) (by norm_num [radMp, kMp, exponentQ])
theorem heMp_8 : |tailEndpoint rMp 8 - ((cenMp 8 : ℚ) : ℝ)| ≤ ((radMp 8 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 8 (by decide)
    (A := -414417257016732591287733) (Z := 1000000000) (E := 8192000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMp, kMp, exponentQ]) (by norm_num [radMp, kMp, exponentQ])
theorem heMp_9 : |tailEndpoint rMp 9 - ((cenMp 9 : ℚ) : ℝ)| ≤ ((radMp 9 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 9 (by decide)
    (A := -713373417662223910645061) (Z := 719689657) (E := 2140120252992566709940243)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMp, kMp, exponentQ]) (by norm_num [radMp, kMp, exponentQ])
theorem heMp_10 : |tailEndpoint rMp 10 - ((cenMp 10 : ℚ) : ℝ)| ≤ ((radMp 10 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 10 (by decide)
    (A := 414489728157629675023900) (Z := 1000000000) (E := 8191000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMp, kMp, exponentQ]) (by norm_num [radMp, kMp, exponentQ])
theorem heMp_11 : |tailEndpoint rMp 11 - ((cenMp 11 : ℚ) : ℝ)| ≤ ((radMp 11 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 11 (by decide)
    (A := 713498176322016862438820) (Z := 719689657) (E := 2140494528971944845631860)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMp, kMp, exponentQ]) (by norm_num [radMp, kMp, exponentQ])
theorem heMp_12 : |tailEndpoint rMp 12 - ((cenMp 12 : ℚ) : ℝ)| ≤ ((radMp 12 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 12 (by decide)
    (A := 160645639017567374134709) (Z := 738631771) (E := 321291278041188574280926)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMp, kMp, exponentQ]) (by norm_num [radMp, kMp, exponentQ])
theorem heMp_13 : |tailEndpoint rMp 13 - ((cenMp 13 : ℚ) : ℝ)| ≤ ((radMp 13 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 13 (by decide)
    (A := -147002540319399059696540) (Z := 1000000000) (E := 8196000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMp, kMp, exponentQ]) (by norm_num [radMp, kMp, exponentQ])
theorem heMp_14 : |tailEndpoint rMp 14 - ((cenMp 14 : ℚ) : ℝ)| ≤ ((radMp 14 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 14 (by decide)
    (A := -160676368437612971102565) (Z := 738631771) (E := 321352736881279029584865)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMp, kMp, exponentQ]) (by norm_num [radMp, kMp, exponentQ])
theorem heMp_15 : |tailEndpoint rMp 15 - ((cenMp 15 : ℚ) : ℝ)| ≤ ((radMp 15 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 15 (by decide)
    (A := 147030661707939500997990) (Z := 1000000000) (E := 8195000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMp, kMp, exponentQ]) (by norm_num [radMp, kMp, exponentQ])
theorem heMp_16 : |tailEndpoint rMp 16 - ((cenMp 16 : ℚ) : ℝ)| ≤ ((radMp 16 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 16 (by decide)
    (A := 160707107486649435657516) (Z := 738631771) (E := 321414214979351220062994)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMp, kMp, exponentQ]) (by norm_num [radMp, kMp, exponentQ])
theorem heMp_17 : |tailEndpoint rMp 17 - ((cenMp 17 : ℚ) : ℝ)| ≤ ((radMp 17 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 17 (by decide)
    (A := -147058791908788040277550) (Z := 1000000000) (E := 8194000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMp, kMp, exponentQ]) (by norm_num [radMp, kMp, exponentQ])
theorem heMp_18 : |tailEndpoint rMp 18 - ((cenMp 18 : ℚ) : ℝ)| ≤ ((radMp 18 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 18 (by decide)
    (A := -160737856168869596950923) (Z := 738631771) (E := 321475712343790804018035)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMp, kMp, exponentQ]) (by norm_num [radMp, kMp, exponentQ])
theorem heMp_19 : |tailEndpoint rMp 19 - ((cenMp 19 : ℚ) : ℝ)| ≤ ((radMp 19 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 19 (by decide)
    (A := 147086930925782126106158) (Z := 1000000000) (E := 8193000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMp, kMp, exponentQ]) (by norm_num [radMp, kMp, exponentQ])
theorem heMp_20 : |tailEndpoint rMp 20 - ((cenMp 20 : ℚ) : ℝ)| ≤ ((radMp 20 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 20 (by decide)
    (A := 160768614488468621880872) (Z := 738631771) (E := 321537228982988115246160)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMp, kMp, exponentQ]) (by norm_num [radMp, kMp, exponentQ])
theorem heMp_21 : |tailEndpoint rMp 21 - ((cenMp 21 : ℚ) : ℝ)| ≤ ((radMp 21 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 21 (by decide)
    (A := -147115078762761346786687) (Z := 1000000000) (E := 8192000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMp, kMp, exponentQ]) (by norm_num [radMp, kMp, exponentQ])
theorem heMp_22 : |tailEndpoint rMp 22 - ((cenMp 22 : ℚ) : ℝ)| ≤ ((radMp 22 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 22 (by decide)
    (A := -160799382449644016681172) (Z := 738631771) (E := 321598764905338166214987)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMp, kMp, exponentQ]) (by norm_num [radMp, kMp, exponentQ])
theorem heMp_23 : |tailEndpoint rMp 23 - ((cenMp 23 : ℚ) : ℝ)| ≤ ((radMp 23 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 23 (by decide)
    (A := 147143235423567431808422) (Z := 1000000000) (E := 8191000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMp, kMp, exponentQ]) (by norm_num [radMp, kMp, exponentQ])
theorem heMp_24 : |tailEndpoint rMp 24 - ((cenMp 24 : ℚ) : ℝ)| ≤ ((radMp 24 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 24 (by decide)
    (A := 160830160056595628511605) (Z := 738631771) (E := 321660320119240651244080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMp, kMp, exponentQ]) (by norm_num [radMp, kMp, exponentQ])
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
theorem errMp : tailError rMp ((49162 : ℚ) : ℝ) ≤
    ((tailErrorUpperQ kqMp 49162 cenMp radMp : ℚ) : ℝ) :=
  tailError_le_Q rMp kqMp 49162 cenMp radMp
    (fun i => by fin_cases i <;> norm_num [rMp, kMp, kqMp])
    (by decide +kernel) (by decide +kernel) heMp
theorem leadValMp : tailLeadingUpperQ cenMp radMp = (67165703292484860898065632684097259050820691638918913842852759017370039760543115134016236482260223069090233606295247182397 / 1704340790977500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by decide +kernel
theorem errValMp : tailErrorUpperQ kqMp 49162 cenMp radMp = (390988015024349859551844897757729171691967287606086097161703129709881828606263021147467972570723945851915504279894264434212066119506032772998395039455349063032603583 / 9484641169201891759698563309326763873986822746677699123250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by decide +kernel
end KsIndex.NegSignProd
