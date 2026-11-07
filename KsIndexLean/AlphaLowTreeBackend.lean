module
public import KsIndexLean.AlphaLowLookupTree
public import KsIndexLean.AlphaLowTreeDataF0R0B0
public import KsIndexLean.AlphaLowTreeDataF0R0B16
public import KsIndexLean.AlphaLowTreeDataF0R0B32
public import KsIndexLean.AlphaLowTreeDataF0R0B48
public import KsIndexLean.AlphaLowTreeDataF0R0B64
public import KsIndexLean.AlphaLowTreeDataF0R0B80
public import KsIndexLean.AlphaLowTreeDataF0R0B96
public import KsIndexLean.AlphaLowTreeDataF0R0B112
public import KsIndexLean.AlphaLowTreeDataF0R1B0
public import KsIndexLean.AlphaLowTreeDataF0R1B16
public import KsIndexLean.AlphaLowTreeDataF0R1B32
public import KsIndexLean.AlphaLowTreeDataF0R1B48
public import KsIndexLean.AlphaLowTreeDataF0R1B64
public import KsIndexLean.AlphaLowTreeDataF0R1B80
public import KsIndexLean.AlphaLowTreeDataF0R1B96
public import KsIndexLean.AlphaLowTreeDataF0R1B112
public import KsIndexLean.AlphaLowTreeDataF1R0B0
public import KsIndexLean.AlphaLowTreeDataF1R0B16
public import KsIndexLean.AlphaLowTreeDataF1R0B32
public import KsIndexLean.AlphaLowTreeDataF1R0B48
public import KsIndexLean.AlphaLowTreeDataF1R0B64
public import KsIndexLean.AlphaLowTreeDataF1R0B80
public import KsIndexLean.AlphaLowTreeDataF1R0B96
public import KsIndexLean.AlphaLowTreeDataF1R0B112
public import KsIndexLean.AlphaLowTreeDataF1R1B0
public import KsIndexLean.AlphaLowTreeDataF1R1B16
public import KsIndexLean.AlphaLowTreeDataF1R1B32
public import KsIndexLean.AlphaLowTreeDataF1R1B48
public import KsIndexLean.AlphaLowTreeDataF1R1B64
public import KsIndexLean.AlphaLowTreeDataF1R1B80
public import KsIndexLean.AlphaLowTreeDataF1R1B96
public import KsIndexLean.AlphaLowTreeDataF1R1B112
public import KsIndexLean.AlphaLowProdAccessorFast
public import Mathlib.Tactic.IntervalCases
@[expose] public section
namespace KsIndex.AlphaLowTreeBackend
open KsIndex.LookupTreePilot KsIndex.PositiveEnergyAlphaLowProd
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
/-! Balanced replay representation of the exact coefficient-table data.
Each full chunk has 128 leaves. All values are checked against the original arrays.
The six-element final chunk and out-of-table defaults retain their original route. -/
def select00 (b : Nat) : KsIndex.LookupTreePilot.Tree 7 := (if b < 64 then (if b < 32 then (if b < 16 then (if b < 8 then (if b < 4 then (if b < 2 then (if b < 1 then tree00_0 else tree00_1) else (if b < 3 then tree00_2 else tree00_3)) else (if b < 6 then (if b < 5 then tree00_4 else tree00_5) else (if b < 7 then tree00_6 else tree00_7))) else (if b < 12 then (if b < 10 then (if b < 9 then tree00_8 else tree00_9) else (if b < 11 then tree00_10 else tree00_11)) else (if b < 14 then (if b < 13 then tree00_12 else tree00_13) else (if b < 15 then tree00_14 else tree00_15)))) else (if b < 24 then (if b < 20 then (if b < 18 then (if b < 17 then tree00_16 else tree00_17) else (if b < 19 then tree00_18 else tree00_19)) else (if b < 22 then (if b < 21 then tree00_20 else tree00_21) else (if b < 23 then tree00_22 else tree00_23))) else (if b < 28 then (if b < 26 then (if b < 25 then tree00_24 else tree00_25) else (if b < 27 then tree00_26 else tree00_27)) else (if b < 30 then (if b < 29 then tree00_28 else tree00_29) else (if b < 31 then tree00_30 else tree00_31))))) else (if b < 48 then (if b < 40 then (if b < 36 then (if b < 34 then (if b < 33 then tree00_32 else tree00_33) else (if b < 35 then tree00_34 else tree00_35)) else (if b < 38 then (if b < 37 then tree00_36 else tree00_37) else (if b < 39 then tree00_38 else tree00_39))) else (if b < 44 then (if b < 42 then (if b < 41 then tree00_40 else tree00_41) else (if b < 43 then tree00_42 else tree00_43)) else (if b < 46 then (if b < 45 then tree00_44 else tree00_45) else (if b < 47 then tree00_46 else tree00_47)))) else (if b < 56 then (if b < 52 then (if b < 50 then (if b < 49 then tree00_48 else tree00_49) else (if b < 51 then tree00_50 else tree00_51)) else (if b < 54 then (if b < 53 then tree00_52 else tree00_53) else (if b < 55 then tree00_54 else tree00_55))) else (if b < 60 then (if b < 58 then (if b < 57 then tree00_56 else tree00_57) else (if b < 59 then tree00_58 else tree00_59)) else (if b < 62 then (if b < 61 then tree00_60 else tree00_61) else (if b < 63 then tree00_62 else tree00_63)))))) else (if b < 96 then (if b < 80 then (if b < 72 then (if b < 68 then (if b < 66 then (if b < 65 then tree00_64 else tree00_65) else (if b < 67 then tree00_66 else tree00_67)) else (if b < 70 then (if b < 69 then tree00_68 else tree00_69) else (if b < 71 then tree00_70 else tree00_71))) else (if b < 76 then (if b < 74 then (if b < 73 then tree00_72 else tree00_73) else (if b < 75 then tree00_74 else tree00_75)) else (if b < 78 then (if b < 77 then tree00_76 else tree00_77) else (if b < 79 then tree00_78 else tree00_79)))) else (if b < 88 then (if b < 84 then (if b < 82 then (if b < 81 then tree00_80 else tree00_81) else (if b < 83 then tree00_82 else tree00_83)) else (if b < 86 then (if b < 85 then tree00_84 else tree00_85) else (if b < 87 then tree00_86 else tree00_87))) else (if b < 92 then (if b < 90 then (if b < 89 then tree00_88 else tree00_89) else (if b < 91 then tree00_90 else tree00_91)) else (if b < 94 then (if b < 93 then tree00_92 else tree00_93) else (if b < 95 then tree00_94 else tree00_95))))) else (if b < 112 then (if b < 104 then (if b < 100 then (if b < 98 then (if b < 97 then tree00_96 else tree00_97) else (if b < 99 then tree00_98 else tree00_99)) else (if b < 102 then (if b < 101 then tree00_100 else tree00_101) else (if b < 103 then tree00_102 else tree00_103))) else (if b < 108 then (if b < 106 then (if b < 105 then tree00_104 else tree00_105) else (if b < 107 then tree00_106 else tree00_107)) else (if b < 110 then (if b < 109 then tree00_108 else tree00_109) else (if b < 111 then tree00_110 else tree00_111)))) else (if b < 120 then (if b < 116 then (if b < 114 then (if b < 113 then tree00_112 else tree00_113) else (if b < 115 then tree00_114 else tree00_115)) else (if b < 118 then (if b < 117 then tree00_116 else tree00_117) else (if b < 119 then tree00_118 else tree00_119))) else (if b < 124 then (if b < 122 then (if b < 121 then tree00_120 else tree00_121) else (if b < 123 then tree00_122 else tree00_123)) else (if b < 126 then (if b < 125 then tree00_124 else tree00_125) else (if b < 127 then tree00_126 else tree00_127)))))))
lemma select00_lookup (b n : Nat) (hb : b < 128) : lookup (select00 b) n = (get00 b)[n]?.getD 0 := by
  interval_cases b
  · exact lookup00_0 n
  · exact lookup00_1 n
  · exact lookup00_2 n
  · exact lookup00_3 n
  · exact lookup00_4 n
  · exact lookup00_5 n
  · exact lookup00_6 n
  · exact lookup00_7 n
  · exact lookup00_8 n
  · exact lookup00_9 n
  · exact lookup00_10 n
  · exact lookup00_11 n
  · exact lookup00_12 n
  · exact lookup00_13 n
  · exact lookup00_14 n
  · exact lookup00_15 n
  · exact lookup00_16 n
  · exact lookup00_17 n
  · exact lookup00_18 n
  · exact lookup00_19 n
  · exact lookup00_20 n
  · exact lookup00_21 n
  · exact lookup00_22 n
  · exact lookup00_23 n
  · exact lookup00_24 n
  · exact lookup00_25 n
  · exact lookup00_26 n
  · exact lookup00_27 n
  · exact lookup00_28 n
  · exact lookup00_29 n
  · exact lookup00_30 n
  · exact lookup00_31 n
  · exact lookup00_32 n
  · exact lookup00_33 n
  · exact lookup00_34 n
  · exact lookup00_35 n
  · exact lookup00_36 n
  · exact lookup00_37 n
  · exact lookup00_38 n
  · exact lookup00_39 n
  · exact lookup00_40 n
  · exact lookup00_41 n
  · exact lookup00_42 n
  · exact lookup00_43 n
  · exact lookup00_44 n
  · exact lookup00_45 n
  · exact lookup00_46 n
  · exact lookup00_47 n
  · exact lookup00_48 n
  · exact lookup00_49 n
  · exact lookup00_50 n
  · exact lookup00_51 n
  · exact lookup00_52 n
  · exact lookup00_53 n
  · exact lookup00_54 n
  · exact lookup00_55 n
  · exact lookup00_56 n
  · exact lookup00_57 n
  · exact lookup00_58 n
  · exact lookup00_59 n
  · exact lookup00_60 n
  · exact lookup00_61 n
  · exact lookup00_62 n
  · exact lookup00_63 n
  · exact lookup00_64 n
  · exact lookup00_65 n
  · exact lookup00_66 n
  · exact lookup00_67 n
  · exact lookup00_68 n
  · exact lookup00_69 n
  · exact lookup00_70 n
  · exact lookup00_71 n
  · exact lookup00_72 n
  · exact lookup00_73 n
  · exact lookup00_74 n
  · exact lookup00_75 n
  · exact lookup00_76 n
  · exact lookup00_77 n
  · exact lookup00_78 n
  · exact lookup00_79 n
  · exact lookup00_80 n
  · exact lookup00_81 n
  · exact lookup00_82 n
  · exact lookup00_83 n
  · exact lookup00_84 n
  · exact lookup00_85 n
  · exact lookup00_86 n
  · exact lookup00_87 n
  · exact lookup00_88 n
  · exact lookup00_89 n
  · exact lookup00_90 n
  · exact lookup00_91 n
  · exact lookup00_92 n
  · exact lookup00_93 n
  · exact lookup00_94 n
  · exact lookup00_95 n
  · exact lookup00_96 n
  · exact lookup00_97 n
  · exact lookup00_98 n
  · exact lookup00_99 n
  · exact lookup00_100 n
  · exact lookup00_101 n
  · exact lookup00_102 n
  · exact lookup00_103 n
  · exact lookup00_104 n
  · exact lookup00_105 n
  · exact lookup00_106 n
  · exact lookup00_107 n
  · exact lookup00_108 n
  · exact lookup00_109 n
  · exact lookup00_110 n
  · exact lookup00_111 n
  · exact lookup00_112 n
  · exact lookup00_113 n
  · exact lookup00_114 n
  · exact lookup00_115 n
  · exact lookup00_116 n
  · exact lookup00_117 n
  · exact lookup00_118 n
  · exact lookup00_119 n
  · exact lookup00_120 n
  · exact lookup00_121 n
  · exact lookup00_122 n
  · exact lookup00_123 n
  · exact lookup00_124 n
  · exact lookup00_125 n
  · exact lookup00_126 n
  · exact lookup00_127 n
def select01 (b : Nat) : KsIndex.LookupTreePilot.Tree 7 := (if b < 64 then (if b < 32 then (if b < 16 then (if b < 8 then (if b < 4 then (if b < 2 then (if b < 1 then tree01_0 else tree01_1) else (if b < 3 then tree01_2 else tree01_3)) else (if b < 6 then (if b < 5 then tree01_4 else tree01_5) else (if b < 7 then tree01_6 else tree01_7))) else (if b < 12 then (if b < 10 then (if b < 9 then tree01_8 else tree01_9) else (if b < 11 then tree01_10 else tree01_11)) else (if b < 14 then (if b < 13 then tree01_12 else tree01_13) else (if b < 15 then tree01_14 else tree01_15)))) else (if b < 24 then (if b < 20 then (if b < 18 then (if b < 17 then tree01_16 else tree01_17) else (if b < 19 then tree01_18 else tree01_19)) else (if b < 22 then (if b < 21 then tree01_20 else tree01_21) else (if b < 23 then tree01_22 else tree01_23))) else (if b < 28 then (if b < 26 then (if b < 25 then tree01_24 else tree01_25) else (if b < 27 then tree01_26 else tree01_27)) else (if b < 30 then (if b < 29 then tree01_28 else tree01_29) else (if b < 31 then tree01_30 else tree01_31))))) else (if b < 48 then (if b < 40 then (if b < 36 then (if b < 34 then (if b < 33 then tree01_32 else tree01_33) else (if b < 35 then tree01_34 else tree01_35)) else (if b < 38 then (if b < 37 then tree01_36 else tree01_37) else (if b < 39 then tree01_38 else tree01_39))) else (if b < 44 then (if b < 42 then (if b < 41 then tree01_40 else tree01_41) else (if b < 43 then tree01_42 else tree01_43)) else (if b < 46 then (if b < 45 then tree01_44 else tree01_45) else (if b < 47 then tree01_46 else tree01_47)))) else (if b < 56 then (if b < 52 then (if b < 50 then (if b < 49 then tree01_48 else tree01_49) else (if b < 51 then tree01_50 else tree01_51)) else (if b < 54 then (if b < 53 then tree01_52 else tree01_53) else (if b < 55 then tree01_54 else tree01_55))) else (if b < 60 then (if b < 58 then (if b < 57 then tree01_56 else tree01_57) else (if b < 59 then tree01_58 else tree01_59)) else (if b < 62 then (if b < 61 then tree01_60 else tree01_61) else (if b < 63 then tree01_62 else tree01_63)))))) else (if b < 96 then (if b < 80 then (if b < 72 then (if b < 68 then (if b < 66 then (if b < 65 then tree01_64 else tree01_65) else (if b < 67 then tree01_66 else tree01_67)) else (if b < 70 then (if b < 69 then tree01_68 else tree01_69) else (if b < 71 then tree01_70 else tree01_71))) else (if b < 76 then (if b < 74 then (if b < 73 then tree01_72 else tree01_73) else (if b < 75 then tree01_74 else tree01_75)) else (if b < 78 then (if b < 77 then tree01_76 else tree01_77) else (if b < 79 then tree01_78 else tree01_79)))) else (if b < 88 then (if b < 84 then (if b < 82 then (if b < 81 then tree01_80 else tree01_81) else (if b < 83 then tree01_82 else tree01_83)) else (if b < 86 then (if b < 85 then tree01_84 else tree01_85) else (if b < 87 then tree01_86 else tree01_87))) else (if b < 92 then (if b < 90 then (if b < 89 then tree01_88 else tree01_89) else (if b < 91 then tree01_90 else tree01_91)) else (if b < 94 then (if b < 93 then tree01_92 else tree01_93) else (if b < 95 then tree01_94 else tree01_95))))) else (if b < 112 then (if b < 104 then (if b < 100 then (if b < 98 then (if b < 97 then tree01_96 else tree01_97) else (if b < 99 then tree01_98 else tree01_99)) else (if b < 102 then (if b < 101 then tree01_100 else tree01_101) else (if b < 103 then tree01_102 else tree01_103))) else (if b < 108 then (if b < 106 then (if b < 105 then tree01_104 else tree01_105) else (if b < 107 then tree01_106 else tree01_107)) else (if b < 110 then (if b < 109 then tree01_108 else tree01_109) else (if b < 111 then tree01_110 else tree01_111)))) else (if b < 120 then (if b < 116 then (if b < 114 then (if b < 113 then tree01_112 else tree01_113) else (if b < 115 then tree01_114 else tree01_115)) else (if b < 118 then (if b < 117 then tree01_116 else tree01_117) else (if b < 119 then tree01_118 else tree01_119))) else (if b < 124 then (if b < 122 then (if b < 121 then tree01_120 else tree01_121) else (if b < 123 then tree01_122 else tree01_123)) else (if b < 126 then (if b < 125 then tree01_124 else tree01_125) else (if b < 127 then tree01_126 else tree01_127)))))))
lemma select01_lookup (b n : Nat) (hb : b < 128) : lookup (select01 b) n = (get01 b)[n]?.getD 0 := by
  interval_cases b
  · exact lookup01_0 n
  · exact lookup01_1 n
  · exact lookup01_2 n
  · exact lookup01_3 n
  · exact lookup01_4 n
  · exact lookup01_5 n
  · exact lookup01_6 n
  · exact lookup01_7 n
  · exact lookup01_8 n
  · exact lookup01_9 n
  · exact lookup01_10 n
  · exact lookup01_11 n
  · exact lookup01_12 n
  · exact lookup01_13 n
  · exact lookup01_14 n
  · exact lookup01_15 n
  · exact lookup01_16 n
  · exact lookup01_17 n
  · exact lookup01_18 n
  · exact lookup01_19 n
  · exact lookup01_20 n
  · exact lookup01_21 n
  · exact lookup01_22 n
  · exact lookup01_23 n
  · exact lookup01_24 n
  · exact lookup01_25 n
  · exact lookup01_26 n
  · exact lookup01_27 n
  · exact lookup01_28 n
  · exact lookup01_29 n
  · exact lookup01_30 n
  · exact lookup01_31 n
  · exact lookup01_32 n
  · exact lookup01_33 n
  · exact lookup01_34 n
  · exact lookup01_35 n
  · exact lookup01_36 n
  · exact lookup01_37 n
  · exact lookup01_38 n
  · exact lookup01_39 n
  · exact lookup01_40 n
  · exact lookup01_41 n
  · exact lookup01_42 n
  · exact lookup01_43 n
  · exact lookup01_44 n
  · exact lookup01_45 n
  · exact lookup01_46 n
  · exact lookup01_47 n
  · exact lookup01_48 n
  · exact lookup01_49 n
  · exact lookup01_50 n
  · exact lookup01_51 n
  · exact lookup01_52 n
  · exact lookup01_53 n
  · exact lookup01_54 n
  · exact lookup01_55 n
  · exact lookup01_56 n
  · exact lookup01_57 n
  · exact lookup01_58 n
  · exact lookup01_59 n
  · exact lookup01_60 n
  · exact lookup01_61 n
  · exact lookup01_62 n
  · exact lookup01_63 n
  · exact lookup01_64 n
  · exact lookup01_65 n
  · exact lookup01_66 n
  · exact lookup01_67 n
  · exact lookup01_68 n
  · exact lookup01_69 n
  · exact lookup01_70 n
  · exact lookup01_71 n
  · exact lookup01_72 n
  · exact lookup01_73 n
  · exact lookup01_74 n
  · exact lookup01_75 n
  · exact lookup01_76 n
  · exact lookup01_77 n
  · exact lookup01_78 n
  · exact lookup01_79 n
  · exact lookup01_80 n
  · exact lookup01_81 n
  · exact lookup01_82 n
  · exact lookup01_83 n
  · exact lookup01_84 n
  · exact lookup01_85 n
  · exact lookup01_86 n
  · exact lookup01_87 n
  · exact lookup01_88 n
  · exact lookup01_89 n
  · exact lookup01_90 n
  · exact lookup01_91 n
  · exact lookup01_92 n
  · exact lookup01_93 n
  · exact lookup01_94 n
  · exact lookup01_95 n
  · exact lookup01_96 n
  · exact lookup01_97 n
  · exact lookup01_98 n
  · exact lookup01_99 n
  · exact lookup01_100 n
  · exact lookup01_101 n
  · exact lookup01_102 n
  · exact lookup01_103 n
  · exact lookup01_104 n
  · exact lookup01_105 n
  · exact lookup01_106 n
  · exact lookup01_107 n
  · exact lookup01_108 n
  · exact lookup01_109 n
  · exact lookup01_110 n
  · exact lookup01_111 n
  · exact lookup01_112 n
  · exact lookup01_113 n
  · exact lookup01_114 n
  · exact lookup01_115 n
  · exact lookup01_116 n
  · exact lookup01_117 n
  · exact lookup01_118 n
  · exact lookup01_119 n
  · exact lookup01_120 n
  · exact lookup01_121 n
  · exact lookup01_122 n
  · exact lookup01_123 n
  · exact lookup01_124 n
  · exact lookup01_125 n
  · exact lookup01_126 n
  · exact lookup01_127 n
def select10 (b : Nat) : KsIndex.LookupTreePilot.Tree 7 := (if b < 64 then (if b < 32 then (if b < 16 then (if b < 8 then (if b < 4 then (if b < 2 then (if b < 1 then tree10_0 else tree10_1) else (if b < 3 then tree10_2 else tree10_3)) else (if b < 6 then (if b < 5 then tree10_4 else tree10_5) else (if b < 7 then tree10_6 else tree10_7))) else (if b < 12 then (if b < 10 then (if b < 9 then tree10_8 else tree10_9) else (if b < 11 then tree10_10 else tree10_11)) else (if b < 14 then (if b < 13 then tree10_12 else tree10_13) else (if b < 15 then tree10_14 else tree10_15)))) else (if b < 24 then (if b < 20 then (if b < 18 then (if b < 17 then tree10_16 else tree10_17) else (if b < 19 then tree10_18 else tree10_19)) else (if b < 22 then (if b < 21 then tree10_20 else tree10_21) else (if b < 23 then tree10_22 else tree10_23))) else (if b < 28 then (if b < 26 then (if b < 25 then tree10_24 else tree10_25) else (if b < 27 then tree10_26 else tree10_27)) else (if b < 30 then (if b < 29 then tree10_28 else tree10_29) else (if b < 31 then tree10_30 else tree10_31))))) else (if b < 48 then (if b < 40 then (if b < 36 then (if b < 34 then (if b < 33 then tree10_32 else tree10_33) else (if b < 35 then tree10_34 else tree10_35)) else (if b < 38 then (if b < 37 then tree10_36 else tree10_37) else (if b < 39 then tree10_38 else tree10_39))) else (if b < 44 then (if b < 42 then (if b < 41 then tree10_40 else tree10_41) else (if b < 43 then tree10_42 else tree10_43)) else (if b < 46 then (if b < 45 then tree10_44 else tree10_45) else (if b < 47 then tree10_46 else tree10_47)))) else (if b < 56 then (if b < 52 then (if b < 50 then (if b < 49 then tree10_48 else tree10_49) else (if b < 51 then tree10_50 else tree10_51)) else (if b < 54 then (if b < 53 then tree10_52 else tree10_53) else (if b < 55 then tree10_54 else tree10_55))) else (if b < 60 then (if b < 58 then (if b < 57 then tree10_56 else tree10_57) else (if b < 59 then tree10_58 else tree10_59)) else (if b < 62 then (if b < 61 then tree10_60 else tree10_61) else (if b < 63 then tree10_62 else tree10_63)))))) else (if b < 96 then (if b < 80 then (if b < 72 then (if b < 68 then (if b < 66 then (if b < 65 then tree10_64 else tree10_65) else (if b < 67 then tree10_66 else tree10_67)) else (if b < 70 then (if b < 69 then tree10_68 else tree10_69) else (if b < 71 then tree10_70 else tree10_71))) else (if b < 76 then (if b < 74 then (if b < 73 then tree10_72 else tree10_73) else (if b < 75 then tree10_74 else tree10_75)) else (if b < 78 then (if b < 77 then tree10_76 else tree10_77) else (if b < 79 then tree10_78 else tree10_79)))) else (if b < 88 then (if b < 84 then (if b < 82 then (if b < 81 then tree10_80 else tree10_81) else (if b < 83 then tree10_82 else tree10_83)) else (if b < 86 then (if b < 85 then tree10_84 else tree10_85) else (if b < 87 then tree10_86 else tree10_87))) else (if b < 92 then (if b < 90 then (if b < 89 then tree10_88 else tree10_89) else (if b < 91 then tree10_90 else tree10_91)) else (if b < 94 then (if b < 93 then tree10_92 else tree10_93) else (if b < 95 then tree10_94 else tree10_95))))) else (if b < 112 then (if b < 104 then (if b < 100 then (if b < 98 then (if b < 97 then tree10_96 else tree10_97) else (if b < 99 then tree10_98 else tree10_99)) else (if b < 102 then (if b < 101 then tree10_100 else tree10_101) else (if b < 103 then tree10_102 else tree10_103))) else (if b < 108 then (if b < 106 then (if b < 105 then tree10_104 else tree10_105) else (if b < 107 then tree10_106 else tree10_107)) else (if b < 110 then (if b < 109 then tree10_108 else tree10_109) else (if b < 111 then tree10_110 else tree10_111)))) else (if b < 120 then (if b < 116 then (if b < 114 then (if b < 113 then tree10_112 else tree10_113) else (if b < 115 then tree10_114 else tree10_115)) else (if b < 118 then (if b < 117 then tree10_116 else tree10_117) else (if b < 119 then tree10_118 else tree10_119))) else (if b < 124 then (if b < 122 then (if b < 121 then tree10_120 else tree10_121) else (if b < 123 then tree10_122 else tree10_123)) else (if b < 126 then (if b < 125 then tree10_124 else tree10_125) else (if b < 127 then tree10_126 else tree10_127)))))))
lemma select10_lookup (b n : Nat) (hb : b < 128) : lookup (select10 b) n = (get10 b)[n]?.getD 0 := by
  interval_cases b
  · exact lookup10_0 n
  · exact lookup10_1 n
  · exact lookup10_2 n
  · exact lookup10_3 n
  · exact lookup10_4 n
  · exact lookup10_5 n
  · exact lookup10_6 n
  · exact lookup10_7 n
  · exact lookup10_8 n
  · exact lookup10_9 n
  · exact lookup10_10 n
  · exact lookup10_11 n
  · exact lookup10_12 n
  · exact lookup10_13 n
  · exact lookup10_14 n
  · exact lookup10_15 n
  · exact lookup10_16 n
  · exact lookup10_17 n
  · exact lookup10_18 n
  · exact lookup10_19 n
  · exact lookup10_20 n
  · exact lookup10_21 n
  · exact lookup10_22 n
  · exact lookup10_23 n
  · exact lookup10_24 n
  · exact lookup10_25 n
  · exact lookup10_26 n
  · exact lookup10_27 n
  · exact lookup10_28 n
  · exact lookup10_29 n
  · exact lookup10_30 n
  · exact lookup10_31 n
  · exact lookup10_32 n
  · exact lookup10_33 n
  · exact lookup10_34 n
  · exact lookup10_35 n
  · exact lookup10_36 n
  · exact lookup10_37 n
  · exact lookup10_38 n
  · exact lookup10_39 n
  · exact lookup10_40 n
  · exact lookup10_41 n
  · exact lookup10_42 n
  · exact lookup10_43 n
  · exact lookup10_44 n
  · exact lookup10_45 n
  · exact lookup10_46 n
  · exact lookup10_47 n
  · exact lookup10_48 n
  · exact lookup10_49 n
  · exact lookup10_50 n
  · exact lookup10_51 n
  · exact lookup10_52 n
  · exact lookup10_53 n
  · exact lookup10_54 n
  · exact lookup10_55 n
  · exact lookup10_56 n
  · exact lookup10_57 n
  · exact lookup10_58 n
  · exact lookup10_59 n
  · exact lookup10_60 n
  · exact lookup10_61 n
  · exact lookup10_62 n
  · exact lookup10_63 n
  · exact lookup10_64 n
  · exact lookup10_65 n
  · exact lookup10_66 n
  · exact lookup10_67 n
  · exact lookup10_68 n
  · exact lookup10_69 n
  · exact lookup10_70 n
  · exact lookup10_71 n
  · exact lookup10_72 n
  · exact lookup10_73 n
  · exact lookup10_74 n
  · exact lookup10_75 n
  · exact lookup10_76 n
  · exact lookup10_77 n
  · exact lookup10_78 n
  · exact lookup10_79 n
  · exact lookup10_80 n
  · exact lookup10_81 n
  · exact lookup10_82 n
  · exact lookup10_83 n
  · exact lookup10_84 n
  · exact lookup10_85 n
  · exact lookup10_86 n
  · exact lookup10_87 n
  · exact lookup10_88 n
  · exact lookup10_89 n
  · exact lookup10_90 n
  · exact lookup10_91 n
  · exact lookup10_92 n
  · exact lookup10_93 n
  · exact lookup10_94 n
  · exact lookup10_95 n
  · exact lookup10_96 n
  · exact lookup10_97 n
  · exact lookup10_98 n
  · exact lookup10_99 n
  · exact lookup10_100 n
  · exact lookup10_101 n
  · exact lookup10_102 n
  · exact lookup10_103 n
  · exact lookup10_104 n
  · exact lookup10_105 n
  · exact lookup10_106 n
  · exact lookup10_107 n
  · exact lookup10_108 n
  · exact lookup10_109 n
  · exact lookup10_110 n
  · exact lookup10_111 n
  · exact lookup10_112 n
  · exact lookup10_113 n
  · exact lookup10_114 n
  · exact lookup10_115 n
  · exact lookup10_116 n
  · exact lookup10_117 n
  · exact lookup10_118 n
  · exact lookup10_119 n
  · exact lookup10_120 n
  · exact lookup10_121 n
  · exact lookup10_122 n
  · exact lookup10_123 n
  · exact lookup10_124 n
  · exact lookup10_125 n
  · exact lookup10_126 n
  · exact lookup10_127 n
def select11 (b : Nat) : KsIndex.LookupTreePilot.Tree 7 := (if b < 64 then (if b < 32 then (if b < 16 then (if b < 8 then (if b < 4 then (if b < 2 then (if b < 1 then tree11_0 else tree11_1) else (if b < 3 then tree11_2 else tree11_3)) else (if b < 6 then (if b < 5 then tree11_4 else tree11_5) else (if b < 7 then tree11_6 else tree11_7))) else (if b < 12 then (if b < 10 then (if b < 9 then tree11_8 else tree11_9) else (if b < 11 then tree11_10 else tree11_11)) else (if b < 14 then (if b < 13 then tree11_12 else tree11_13) else (if b < 15 then tree11_14 else tree11_15)))) else (if b < 24 then (if b < 20 then (if b < 18 then (if b < 17 then tree11_16 else tree11_17) else (if b < 19 then tree11_18 else tree11_19)) else (if b < 22 then (if b < 21 then tree11_20 else tree11_21) else (if b < 23 then tree11_22 else tree11_23))) else (if b < 28 then (if b < 26 then (if b < 25 then tree11_24 else tree11_25) else (if b < 27 then tree11_26 else tree11_27)) else (if b < 30 then (if b < 29 then tree11_28 else tree11_29) else (if b < 31 then tree11_30 else tree11_31))))) else (if b < 48 then (if b < 40 then (if b < 36 then (if b < 34 then (if b < 33 then tree11_32 else tree11_33) else (if b < 35 then tree11_34 else tree11_35)) else (if b < 38 then (if b < 37 then tree11_36 else tree11_37) else (if b < 39 then tree11_38 else tree11_39))) else (if b < 44 then (if b < 42 then (if b < 41 then tree11_40 else tree11_41) else (if b < 43 then tree11_42 else tree11_43)) else (if b < 46 then (if b < 45 then tree11_44 else tree11_45) else (if b < 47 then tree11_46 else tree11_47)))) else (if b < 56 then (if b < 52 then (if b < 50 then (if b < 49 then tree11_48 else tree11_49) else (if b < 51 then tree11_50 else tree11_51)) else (if b < 54 then (if b < 53 then tree11_52 else tree11_53) else (if b < 55 then tree11_54 else tree11_55))) else (if b < 60 then (if b < 58 then (if b < 57 then tree11_56 else tree11_57) else (if b < 59 then tree11_58 else tree11_59)) else (if b < 62 then (if b < 61 then tree11_60 else tree11_61) else (if b < 63 then tree11_62 else tree11_63)))))) else (if b < 96 then (if b < 80 then (if b < 72 then (if b < 68 then (if b < 66 then (if b < 65 then tree11_64 else tree11_65) else (if b < 67 then tree11_66 else tree11_67)) else (if b < 70 then (if b < 69 then tree11_68 else tree11_69) else (if b < 71 then tree11_70 else tree11_71))) else (if b < 76 then (if b < 74 then (if b < 73 then tree11_72 else tree11_73) else (if b < 75 then tree11_74 else tree11_75)) else (if b < 78 then (if b < 77 then tree11_76 else tree11_77) else (if b < 79 then tree11_78 else tree11_79)))) else (if b < 88 then (if b < 84 then (if b < 82 then (if b < 81 then tree11_80 else tree11_81) else (if b < 83 then tree11_82 else tree11_83)) else (if b < 86 then (if b < 85 then tree11_84 else tree11_85) else (if b < 87 then tree11_86 else tree11_87))) else (if b < 92 then (if b < 90 then (if b < 89 then tree11_88 else tree11_89) else (if b < 91 then tree11_90 else tree11_91)) else (if b < 94 then (if b < 93 then tree11_92 else tree11_93) else (if b < 95 then tree11_94 else tree11_95))))) else (if b < 112 then (if b < 104 then (if b < 100 then (if b < 98 then (if b < 97 then tree11_96 else tree11_97) else (if b < 99 then tree11_98 else tree11_99)) else (if b < 102 then (if b < 101 then tree11_100 else tree11_101) else (if b < 103 then tree11_102 else tree11_103))) else (if b < 108 then (if b < 106 then (if b < 105 then tree11_104 else tree11_105) else (if b < 107 then tree11_106 else tree11_107)) else (if b < 110 then (if b < 109 then tree11_108 else tree11_109) else (if b < 111 then tree11_110 else tree11_111)))) else (if b < 120 then (if b < 116 then (if b < 114 then (if b < 113 then tree11_112 else tree11_113) else (if b < 115 then tree11_114 else tree11_115)) else (if b < 118 then (if b < 117 then tree11_116 else tree11_117) else (if b < 119 then tree11_118 else tree11_119))) else (if b < 124 then (if b < 122 then (if b < 121 then tree11_120 else tree11_121) else (if b < 123 then tree11_122 else tree11_123)) else (if b < 126 then (if b < 125 then tree11_124 else tree11_125) else (if b < 127 then tree11_126 else tree11_127)))))))
lemma select11_lookup (b n : Nat) (hb : b < 128) : lookup (select11 b) n = (get11 b)[n]?.getD 0 := by
  interval_cases b
  · exact lookup11_0 n
  · exact lookup11_1 n
  · exact lookup11_2 n
  · exact lookup11_3 n
  · exact lookup11_4 n
  · exact lookup11_5 n
  · exact lookup11_6 n
  · exact lookup11_7 n
  · exact lookup11_8 n
  · exact lookup11_9 n
  · exact lookup11_10 n
  · exact lookup11_11 n
  · exact lookup11_12 n
  · exact lookup11_13 n
  · exact lookup11_14 n
  · exact lookup11_15 n
  · exact lookup11_16 n
  · exact lookup11_17 n
  · exact lookup11_18 n
  · exact lookup11_19 n
  · exact lookup11_20 n
  · exact lookup11_21 n
  · exact lookup11_22 n
  · exact lookup11_23 n
  · exact lookup11_24 n
  · exact lookup11_25 n
  · exact lookup11_26 n
  · exact lookup11_27 n
  · exact lookup11_28 n
  · exact lookup11_29 n
  · exact lookup11_30 n
  · exact lookup11_31 n
  · exact lookup11_32 n
  · exact lookup11_33 n
  · exact lookup11_34 n
  · exact lookup11_35 n
  · exact lookup11_36 n
  · exact lookup11_37 n
  · exact lookup11_38 n
  · exact lookup11_39 n
  · exact lookup11_40 n
  · exact lookup11_41 n
  · exact lookup11_42 n
  · exact lookup11_43 n
  · exact lookup11_44 n
  · exact lookup11_45 n
  · exact lookup11_46 n
  · exact lookup11_47 n
  · exact lookup11_48 n
  · exact lookup11_49 n
  · exact lookup11_50 n
  · exact lookup11_51 n
  · exact lookup11_52 n
  · exact lookup11_53 n
  · exact lookup11_54 n
  · exact lookup11_55 n
  · exact lookup11_56 n
  · exact lookup11_57 n
  · exact lookup11_58 n
  · exact lookup11_59 n
  · exact lookup11_60 n
  · exact lookup11_61 n
  · exact lookup11_62 n
  · exact lookup11_63 n
  · exact lookup11_64 n
  · exact lookup11_65 n
  · exact lookup11_66 n
  · exact lookup11_67 n
  · exact lookup11_68 n
  · exact lookup11_69 n
  · exact lookup11_70 n
  · exact lookup11_71 n
  · exact lookup11_72 n
  · exact lookup11_73 n
  · exact lookup11_74 n
  · exact lookup11_75 n
  · exact lookup11_76 n
  · exact lookup11_77 n
  · exact lookup11_78 n
  · exact lookup11_79 n
  · exact lookup11_80 n
  · exact lookup11_81 n
  · exact lookup11_82 n
  · exact lookup11_83 n
  · exact lookup11_84 n
  · exact lookup11_85 n
  · exact lookup11_86 n
  · exact lookup11_87 n
  · exact lookup11_88 n
  · exact lookup11_89 n
  · exact lookup11_90 n
  · exact lookup11_91 n
  · exact lookup11_92 n
  · exact lookup11_93 n
  · exact lookup11_94 n
  · exact lookup11_95 n
  · exact lookup11_96 n
  · exact lookup11_97 n
  · exact lookup11_98 n
  · exact lookup11_99 n
  · exact lookup11_100 n
  · exact lookup11_101 n
  · exact lookup11_102 n
  · exact lookup11_103 n
  · exact lookup11_104 n
  · exact lookup11_105 n
  · exact lookup11_106 n
  · exact lookup11_107 n
  · exact lookup11_108 n
  · exact lookup11_109 n
  · exact lookup11_110 n
  · exact lookup11_111 n
  · exact lookup11_112 n
  · exact lookup11_113 n
  · exact lookup11_114 n
  · exact lookup11_115 n
  · exact lookup11_116 n
  · exact lookup11_117 n
  · exact lookup11_118 n
  · exact lookup11_119 n
  · exact lookup11_120 n
  · exact lookup11_121 n
  · exact lookup11_122 n
  · exact lookup11_123 n
  · exact lookup11_124 n
  · exact lookup11_125 n
  · exact lookup11_126 n
  · exact lookup11_127 n
/-- Exact coefficient lookup using two balanced levels for the full chunks. -/
def fastTable (B : Int) (r n : Nat) : Int :=
  if n / 128 < 128 then
    if B = 2161809 then
      if r = 0 then lookup (select00 (n/128)) (n%128) else lookup (select01 (n/128)) (n%128)
    else
      if r = 0 then lookup (select10 (n/128)) (n%128) else lookup (select11 (n/128)) (n%128)
  else tFast B r n
lemma fastTable_eq_apply (B : Int) (r n : Nat) : fastTable B r n = tFast B r n := by
  by_cases h : n / 128 < 128
  · by_cases hb : B = 2161809 <;> by_cases hr : r = 0
    all_goals simp [fastTable, tFast, h, hb, hr, select00_lookup _ _ h, select01_lookup _ _ h,
      select10_lookup _ _ h, select11_lookup _ _ h]
  · simp [fastTable, h]
/-- Equality on all inputs, including every original family, parity and out-of-range default. -/
theorem table_eq : fastTable = tFast := by
  funext B r n
  exact fastTable_eq_apply B r n
#print axioms table_eq
end KsIndex.AlphaLowTreeBackend
