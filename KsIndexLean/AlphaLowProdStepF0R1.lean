module

public import KsIndexLean.AlphaLowProdCheckF0R1P0
public import KsIndexLean.AlphaLowProdCheckF0R1P1
public import KsIndexLean.AlphaLowProdCheckF0R1P2
public import KsIndexLean.AlphaLowProdCheckF0R1P3
public import KsIndexLean.AlphaLowProdCheckF0R1P4
public import KsIndexLean.AlphaLowProdCheckF0R1P5
public import KsIndexLean.AlphaLowProdCheckF0R1P6
public import KsIndexLean.AlphaLowProdCheckF0R1P7
public import KsIndexLean.AlphaLowProdCheckF0R1P8
public import KsIndexLean.AlphaLowProdCheckF0R1P9
public import KsIndexLean.AlphaLowProdCheckF0R1P10
public import KsIndexLean.AlphaLowProdCheckF0R1P11
public import KsIndexLean.AlphaLowProdCheckF0R1P12
public import KsIndexLean.AlphaLowProdCheckF0R1P13
public import KsIndexLean.AlphaLowProdCheckF0R1P14
public import KsIndexLean.AlphaLowProdCheckF0R1P15
public import KsIndexLean.AlphaLowProdCheckF0R1P16

@[expose] public section

/-! Step assembly for stream (0,1). -/
namespace KsIndex.PositiveEnergyAlphaLowProd
theorem step01 : ∀ n < 16389, tFast 2161809 1 (n + 1) =
    (2161809 - 5000000 * ((1 : ℤ) + 2 * n)) * tFast 2161809 1 n /
      (2161809 + 5000000 * ((1 : ℤ) + 2 * n + 2)) := by
  intro n hn
  by_cases h0 : n < 128
  · exact block01_0 ⟨n, h0⟩
  by_cases h128 : n < 256
  · have e : 128 + (n - 128) = n := by omega
    rw [← e]
    exact block01_1 ⟨n - 128, by omega⟩
  by_cases h256 : n < 384
  · have e : 256 + (n - 256) = n := by omega
    rw [← e]
    exact block01_2 ⟨n - 256, by omega⟩
  by_cases h384 : n < 512
  · have e : 384 + (n - 384) = n := by omega
    rw [← e]
    exact block01_3 ⟨n - 384, by omega⟩
  by_cases h512 : n < 640
  · have e : 512 + (n - 512) = n := by omega
    rw [← e]
    exact block01_4 ⟨n - 512, by omega⟩
  by_cases h640 : n < 768
  · have e : 640 + (n - 640) = n := by omega
    rw [← e]
    exact block01_5 ⟨n - 640, by omega⟩
  by_cases h768 : n < 896
  · have e : 768 + (n - 768) = n := by omega
    rw [← e]
    exact block01_6 ⟨n - 768, by omega⟩
  by_cases h896 : n < 1024
  · have e : 896 + (n - 896) = n := by omega
    rw [← e]
    exact block01_7 ⟨n - 896, by omega⟩
  by_cases h1024 : n < 1152
  · have e : 1024 + (n - 1024) = n := by omega
    rw [← e]
    exact block01_8 ⟨n - 1024, by omega⟩
  by_cases h1152 : n < 1280
  · have e : 1152 + (n - 1152) = n := by omega
    rw [← e]
    exact block01_9 ⟨n - 1152, by omega⟩
  by_cases h1280 : n < 1408
  · have e : 1280 + (n - 1280) = n := by omega
    rw [← e]
    exact block01_10 ⟨n - 1280, by omega⟩
  by_cases h1408 : n < 1536
  · have e : 1408 + (n - 1408) = n := by omega
    rw [← e]
    exact block01_11 ⟨n - 1408, by omega⟩
  by_cases h1536 : n < 1664
  · have e : 1536 + (n - 1536) = n := by omega
    rw [← e]
    exact block01_12 ⟨n - 1536, by omega⟩
  by_cases h1664 : n < 1792
  · have e : 1664 + (n - 1664) = n := by omega
    rw [← e]
    exact block01_13 ⟨n - 1664, by omega⟩
  by_cases h1792 : n < 1920
  · have e : 1792 + (n - 1792) = n := by omega
    rw [← e]
    exact block01_14 ⟨n - 1792, by omega⟩
  by_cases h1920 : n < 2048
  · have e : 1920 + (n - 1920) = n := by omega
    rw [← e]
    exact block01_15 ⟨n - 1920, by omega⟩
  by_cases h2048 : n < 2176
  · have e : 2048 + (n - 2048) = n := by omega
    rw [← e]
    exact block01_16 ⟨n - 2048, by omega⟩
  by_cases h2176 : n < 2304
  · have e : 2176 + (n - 2176) = n := by omega
    rw [← e]
    exact block01_17 ⟨n - 2176, by omega⟩
  by_cases h2304 : n < 2432
  · have e : 2304 + (n - 2304) = n := by omega
    rw [← e]
    exact block01_18 ⟨n - 2304, by omega⟩
  by_cases h2432 : n < 2560
  · have e : 2432 + (n - 2432) = n := by omega
    rw [← e]
    exact block01_19 ⟨n - 2432, by omega⟩
  by_cases h2560 : n < 2688
  · have e : 2560 + (n - 2560) = n := by omega
    rw [← e]
    exact block01_20 ⟨n - 2560, by omega⟩
  by_cases h2688 : n < 2816
  · have e : 2688 + (n - 2688) = n := by omega
    rw [← e]
    exact block01_21 ⟨n - 2688, by omega⟩
  by_cases h2816 : n < 2944
  · have e : 2816 + (n - 2816) = n := by omega
    rw [← e]
    exact block01_22 ⟨n - 2816, by omega⟩
  by_cases h2944 : n < 3072
  · have e : 2944 + (n - 2944) = n := by omega
    rw [← e]
    exact block01_23 ⟨n - 2944, by omega⟩
  by_cases h3072 : n < 3200
  · have e : 3072 + (n - 3072) = n := by omega
    rw [← e]
    exact block01_24 ⟨n - 3072, by omega⟩
  by_cases h3200 : n < 3328
  · have e : 3200 + (n - 3200) = n := by omega
    rw [← e]
    exact block01_25 ⟨n - 3200, by omega⟩
  by_cases h3328 : n < 3456
  · have e : 3328 + (n - 3328) = n := by omega
    rw [← e]
    exact block01_26 ⟨n - 3328, by omega⟩
  by_cases h3456 : n < 3584
  · have e : 3456 + (n - 3456) = n := by omega
    rw [← e]
    exact block01_27 ⟨n - 3456, by omega⟩
  by_cases h3584 : n < 3712
  · have e : 3584 + (n - 3584) = n := by omega
    rw [← e]
    exact block01_28 ⟨n - 3584, by omega⟩
  by_cases h3712 : n < 3840
  · have e : 3712 + (n - 3712) = n := by omega
    rw [← e]
    exact block01_29 ⟨n - 3712, by omega⟩
  by_cases h3840 : n < 3968
  · have e : 3840 + (n - 3840) = n := by omega
    rw [← e]
    exact block01_30 ⟨n - 3840, by omega⟩
  by_cases h3968 : n < 4096
  · have e : 3968 + (n - 3968) = n := by omega
    rw [← e]
    exact block01_31 ⟨n - 3968, by omega⟩
  by_cases h4096 : n < 4224
  · have e : 4096 + (n - 4096) = n := by omega
    rw [← e]
    exact block01_32 ⟨n - 4096, by omega⟩
  by_cases h4224 : n < 4352
  · have e : 4224 + (n - 4224) = n := by omega
    rw [← e]
    exact block01_33 ⟨n - 4224, by omega⟩
  by_cases h4352 : n < 4480
  · have e : 4352 + (n - 4352) = n := by omega
    rw [← e]
    exact block01_34 ⟨n - 4352, by omega⟩
  by_cases h4480 : n < 4608
  · have e : 4480 + (n - 4480) = n := by omega
    rw [← e]
    exact block01_35 ⟨n - 4480, by omega⟩
  by_cases h4608 : n < 4736
  · have e : 4608 + (n - 4608) = n := by omega
    rw [← e]
    exact block01_36 ⟨n - 4608, by omega⟩
  by_cases h4736 : n < 4864
  · have e : 4736 + (n - 4736) = n := by omega
    rw [← e]
    exact block01_37 ⟨n - 4736, by omega⟩
  by_cases h4864 : n < 4992
  · have e : 4864 + (n - 4864) = n := by omega
    rw [← e]
    exact block01_38 ⟨n - 4864, by omega⟩
  by_cases h4992 : n < 5120
  · have e : 4992 + (n - 4992) = n := by omega
    rw [← e]
    exact block01_39 ⟨n - 4992, by omega⟩
  by_cases h5120 : n < 5248
  · have e : 5120 + (n - 5120) = n := by omega
    rw [← e]
    exact block01_40 ⟨n - 5120, by omega⟩
  by_cases h5248 : n < 5376
  · have e : 5248 + (n - 5248) = n := by omega
    rw [← e]
    exact block01_41 ⟨n - 5248, by omega⟩
  by_cases h5376 : n < 5504
  · have e : 5376 + (n - 5376) = n := by omega
    rw [← e]
    exact block01_42 ⟨n - 5376, by omega⟩
  by_cases h5504 : n < 5632
  · have e : 5504 + (n - 5504) = n := by omega
    rw [← e]
    exact block01_43 ⟨n - 5504, by omega⟩
  by_cases h5632 : n < 5760
  · have e : 5632 + (n - 5632) = n := by omega
    rw [← e]
    exact block01_44 ⟨n - 5632, by omega⟩
  by_cases h5760 : n < 5888
  · have e : 5760 + (n - 5760) = n := by omega
    rw [← e]
    exact block01_45 ⟨n - 5760, by omega⟩
  by_cases h5888 : n < 6016
  · have e : 5888 + (n - 5888) = n := by omega
    rw [← e]
    exact block01_46 ⟨n - 5888, by omega⟩
  by_cases h6016 : n < 6144
  · have e : 6016 + (n - 6016) = n := by omega
    rw [← e]
    exact block01_47 ⟨n - 6016, by omega⟩
  by_cases h6144 : n < 6272
  · have e : 6144 + (n - 6144) = n := by omega
    rw [← e]
    exact block01_48 ⟨n - 6144, by omega⟩
  by_cases h6272 : n < 6400
  · have e : 6272 + (n - 6272) = n := by omega
    rw [← e]
    exact block01_49 ⟨n - 6272, by omega⟩
  by_cases h6400 : n < 6528
  · have e : 6400 + (n - 6400) = n := by omega
    rw [← e]
    exact block01_50 ⟨n - 6400, by omega⟩
  by_cases h6528 : n < 6656
  · have e : 6528 + (n - 6528) = n := by omega
    rw [← e]
    exact block01_51 ⟨n - 6528, by omega⟩
  by_cases h6656 : n < 6784
  · have e : 6656 + (n - 6656) = n := by omega
    rw [← e]
    exact block01_52 ⟨n - 6656, by omega⟩
  by_cases h6784 : n < 6912
  · have e : 6784 + (n - 6784) = n := by omega
    rw [← e]
    exact block01_53 ⟨n - 6784, by omega⟩
  by_cases h6912 : n < 7040
  · have e : 6912 + (n - 6912) = n := by omega
    rw [← e]
    exact block01_54 ⟨n - 6912, by omega⟩
  by_cases h7040 : n < 7168
  · have e : 7040 + (n - 7040) = n := by omega
    rw [← e]
    exact block01_55 ⟨n - 7040, by omega⟩
  by_cases h7168 : n < 7296
  · have e : 7168 + (n - 7168) = n := by omega
    rw [← e]
    exact block01_56 ⟨n - 7168, by omega⟩
  by_cases h7296 : n < 7424
  · have e : 7296 + (n - 7296) = n := by omega
    rw [← e]
    exact block01_57 ⟨n - 7296, by omega⟩
  by_cases h7424 : n < 7552
  · have e : 7424 + (n - 7424) = n := by omega
    rw [← e]
    exact block01_58 ⟨n - 7424, by omega⟩
  by_cases h7552 : n < 7680
  · have e : 7552 + (n - 7552) = n := by omega
    rw [← e]
    exact block01_59 ⟨n - 7552, by omega⟩
  by_cases h7680 : n < 7808
  · have e : 7680 + (n - 7680) = n := by omega
    rw [← e]
    exact block01_60 ⟨n - 7680, by omega⟩
  by_cases h7808 : n < 7936
  · have e : 7808 + (n - 7808) = n := by omega
    rw [← e]
    exact block01_61 ⟨n - 7808, by omega⟩
  by_cases h7936 : n < 8064
  · have e : 7936 + (n - 7936) = n := by omega
    rw [← e]
    exact block01_62 ⟨n - 7936, by omega⟩
  by_cases h8064 : n < 8192
  · have e : 8064 + (n - 8064) = n := by omega
    rw [← e]
    exact block01_63 ⟨n - 8064, by omega⟩
  by_cases h8192 : n < 8320
  · have e : 8192 + (n - 8192) = n := by omega
    rw [← e]
    exact block01_64 ⟨n - 8192, by omega⟩
  by_cases h8320 : n < 8448
  · have e : 8320 + (n - 8320) = n := by omega
    rw [← e]
    exact block01_65 ⟨n - 8320, by omega⟩
  by_cases h8448 : n < 8576
  · have e : 8448 + (n - 8448) = n := by omega
    rw [← e]
    exact block01_66 ⟨n - 8448, by omega⟩
  by_cases h8576 : n < 8704
  · have e : 8576 + (n - 8576) = n := by omega
    rw [← e]
    exact block01_67 ⟨n - 8576, by omega⟩
  by_cases h8704 : n < 8832
  · have e : 8704 + (n - 8704) = n := by omega
    rw [← e]
    exact block01_68 ⟨n - 8704, by omega⟩
  by_cases h8832 : n < 8960
  · have e : 8832 + (n - 8832) = n := by omega
    rw [← e]
    exact block01_69 ⟨n - 8832, by omega⟩
  by_cases h8960 : n < 9088
  · have e : 8960 + (n - 8960) = n := by omega
    rw [← e]
    exact block01_70 ⟨n - 8960, by omega⟩
  by_cases h9088 : n < 9216
  · have e : 9088 + (n - 9088) = n := by omega
    rw [← e]
    exact block01_71 ⟨n - 9088, by omega⟩
  by_cases h9216 : n < 9344
  · have e : 9216 + (n - 9216) = n := by omega
    rw [← e]
    exact block01_72 ⟨n - 9216, by omega⟩
  by_cases h9344 : n < 9472
  · have e : 9344 + (n - 9344) = n := by omega
    rw [← e]
    exact block01_73 ⟨n - 9344, by omega⟩
  by_cases h9472 : n < 9600
  · have e : 9472 + (n - 9472) = n := by omega
    rw [← e]
    exact block01_74 ⟨n - 9472, by omega⟩
  by_cases h9600 : n < 9728
  · have e : 9600 + (n - 9600) = n := by omega
    rw [← e]
    exact block01_75 ⟨n - 9600, by omega⟩
  by_cases h9728 : n < 9856
  · have e : 9728 + (n - 9728) = n := by omega
    rw [← e]
    exact block01_76 ⟨n - 9728, by omega⟩
  by_cases h9856 : n < 9984
  · have e : 9856 + (n - 9856) = n := by omega
    rw [← e]
    exact block01_77 ⟨n - 9856, by omega⟩
  by_cases h9984 : n < 10112
  · have e : 9984 + (n - 9984) = n := by omega
    rw [← e]
    exact block01_78 ⟨n - 9984, by omega⟩
  by_cases h10112 : n < 10240
  · have e : 10112 + (n - 10112) = n := by omega
    rw [← e]
    exact block01_79 ⟨n - 10112, by omega⟩
  by_cases h10240 : n < 10368
  · have e : 10240 + (n - 10240) = n := by omega
    rw [← e]
    exact block01_80 ⟨n - 10240, by omega⟩
  by_cases h10368 : n < 10496
  · have e : 10368 + (n - 10368) = n := by omega
    rw [← e]
    exact block01_81 ⟨n - 10368, by omega⟩
  by_cases h10496 : n < 10624
  · have e : 10496 + (n - 10496) = n := by omega
    rw [← e]
    exact block01_82 ⟨n - 10496, by omega⟩
  by_cases h10624 : n < 10752
  · have e : 10624 + (n - 10624) = n := by omega
    rw [← e]
    exact block01_83 ⟨n - 10624, by omega⟩
  by_cases h10752 : n < 10880
  · have e : 10752 + (n - 10752) = n := by omega
    rw [← e]
    exact block01_84 ⟨n - 10752, by omega⟩
  by_cases h10880 : n < 11008
  · have e : 10880 + (n - 10880) = n := by omega
    rw [← e]
    exact block01_85 ⟨n - 10880, by omega⟩
  by_cases h11008 : n < 11136
  · have e : 11008 + (n - 11008) = n := by omega
    rw [← e]
    exact block01_86 ⟨n - 11008, by omega⟩
  by_cases h11136 : n < 11264
  · have e : 11136 + (n - 11136) = n := by omega
    rw [← e]
    exact block01_87 ⟨n - 11136, by omega⟩
  by_cases h11264 : n < 11392
  · have e : 11264 + (n - 11264) = n := by omega
    rw [← e]
    exact block01_88 ⟨n - 11264, by omega⟩
  by_cases h11392 : n < 11520
  · have e : 11392 + (n - 11392) = n := by omega
    rw [← e]
    exact block01_89 ⟨n - 11392, by omega⟩
  by_cases h11520 : n < 11648
  · have e : 11520 + (n - 11520) = n := by omega
    rw [← e]
    exact block01_90 ⟨n - 11520, by omega⟩
  by_cases h11648 : n < 11776
  · have e : 11648 + (n - 11648) = n := by omega
    rw [← e]
    exact block01_91 ⟨n - 11648, by omega⟩
  by_cases h11776 : n < 11904
  · have e : 11776 + (n - 11776) = n := by omega
    rw [← e]
    exact block01_92 ⟨n - 11776, by omega⟩
  by_cases h11904 : n < 12032
  · have e : 11904 + (n - 11904) = n := by omega
    rw [← e]
    exact block01_93 ⟨n - 11904, by omega⟩
  by_cases h12032 : n < 12160
  · have e : 12032 + (n - 12032) = n := by omega
    rw [← e]
    exact block01_94 ⟨n - 12032, by omega⟩
  by_cases h12160 : n < 12288
  · have e : 12160 + (n - 12160) = n := by omega
    rw [← e]
    exact block01_95 ⟨n - 12160, by omega⟩
  by_cases h12288 : n < 12416
  · have e : 12288 + (n - 12288) = n := by omega
    rw [← e]
    exact block01_96 ⟨n - 12288, by omega⟩
  by_cases h12416 : n < 12544
  · have e : 12416 + (n - 12416) = n := by omega
    rw [← e]
    exact block01_97 ⟨n - 12416, by omega⟩
  by_cases h12544 : n < 12672
  · have e : 12544 + (n - 12544) = n := by omega
    rw [← e]
    exact block01_98 ⟨n - 12544, by omega⟩
  by_cases h12672 : n < 12800
  · have e : 12672 + (n - 12672) = n := by omega
    rw [← e]
    exact block01_99 ⟨n - 12672, by omega⟩
  by_cases h12800 : n < 12928
  · have e : 12800 + (n - 12800) = n := by omega
    rw [← e]
    exact block01_100 ⟨n - 12800, by omega⟩
  by_cases h12928 : n < 13056
  · have e : 12928 + (n - 12928) = n := by omega
    rw [← e]
    exact block01_101 ⟨n - 12928, by omega⟩
  by_cases h13056 : n < 13184
  · have e : 13056 + (n - 13056) = n := by omega
    rw [← e]
    exact block01_102 ⟨n - 13056, by omega⟩
  by_cases h13184 : n < 13312
  · have e : 13184 + (n - 13184) = n := by omega
    rw [← e]
    exact block01_103 ⟨n - 13184, by omega⟩
  by_cases h13312 : n < 13440
  · have e : 13312 + (n - 13312) = n := by omega
    rw [← e]
    exact block01_104 ⟨n - 13312, by omega⟩
  by_cases h13440 : n < 13568
  · have e : 13440 + (n - 13440) = n := by omega
    rw [← e]
    exact block01_105 ⟨n - 13440, by omega⟩
  by_cases h13568 : n < 13696
  · have e : 13568 + (n - 13568) = n := by omega
    rw [← e]
    exact block01_106 ⟨n - 13568, by omega⟩
  by_cases h13696 : n < 13824
  · have e : 13696 + (n - 13696) = n := by omega
    rw [← e]
    exact block01_107 ⟨n - 13696, by omega⟩
  by_cases h13824 : n < 13952
  · have e : 13824 + (n - 13824) = n := by omega
    rw [← e]
    exact block01_108 ⟨n - 13824, by omega⟩
  by_cases h13952 : n < 14080
  · have e : 13952 + (n - 13952) = n := by omega
    rw [← e]
    exact block01_109 ⟨n - 13952, by omega⟩
  by_cases h14080 : n < 14208
  · have e : 14080 + (n - 14080) = n := by omega
    rw [← e]
    exact block01_110 ⟨n - 14080, by omega⟩
  by_cases h14208 : n < 14336
  · have e : 14208 + (n - 14208) = n := by omega
    rw [← e]
    exact block01_111 ⟨n - 14208, by omega⟩
  by_cases h14336 : n < 14464
  · have e : 14336 + (n - 14336) = n := by omega
    rw [← e]
    exact block01_112 ⟨n - 14336, by omega⟩
  by_cases h14464 : n < 14592
  · have e : 14464 + (n - 14464) = n := by omega
    rw [← e]
    exact block01_113 ⟨n - 14464, by omega⟩
  by_cases h14592 : n < 14720
  · have e : 14592 + (n - 14592) = n := by omega
    rw [← e]
    exact block01_114 ⟨n - 14592, by omega⟩
  by_cases h14720 : n < 14848
  · have e : 14720 + (n - 14720) = n := by omega
    rw [← e]
    exact block01_115 ⟨n - 14720, by omega⟩
  by_cases h14848 : n < 14976
  · have e : 14848 + (n - 14848) = n := by omega
    rw [← e]
    exact block01_116 ⟨n - 14848, by omega⟩
  by_cases h14976 : n < 15104
  · have e : 14976 + (n - 14976) = n := by omega
    rw [← e]
    exact block01_117 ⟨n - 14976, by omega⟩
  by_cases h15104 : n < 15232
  · have e : 15104 + (n - 15104) = n := by omega
    rw [← e]
    exact block01_118 ⟨n - 15104, by omega⟩
  by_cases h15232 : n < 15360
  · have e : 15232 + (n - 15232) = n := by omega
    rw [← e]
    exact block01_119 ⟨n - 15232, by omega⟩
  by_cases h15360 : n < 15488
  · have e : 15360 + (n - 15360) = n := by omega
    rw [← e]
    exact block01_120 ⟨n - 15360, by omega⟩
  by_cases h15488 : n < 15616
  · have e : 15488 + (n - 15488) = n := by omega
    rw [← e]
    exact block01_121 ⟨n - 15488, by omega⟩
  by_cases h15616 : n < 15744
  · have e : 15616 + (n - 15616) = n := by omega
    rw [← e]
    exact block01_122 ⟨n - 15616, by omega⟩
  by_cases h15744 : n < 15872
  · have e : 15744 + (n - 15744) = n := by omega
    rw [← e]
    exact block01_123 ⟨n - 15744, by omega⟩
  by_cases h15872 : n < 16000
  · have e : 15872 + (n - 15872) = n := by omega
    rw [← e]
    exact block01_124 ⟨n - 15872, by omega⟩
  by_cases h16000 : n < 16128
  · have e : 16000 + (n - 16000) = n := by omega
    rw [← e]
    exact block01_125 ⟨n - 16000, by omega⟩
  by_cases h16128 : n < 16256
  · have e : 16128 + (n - 16128) = n := by omega
    rw [← e]
    exact block01_126 ⟨n - 16128, by omega⟩
  by_cases h16256 : n < 16384
  · have e : 16256 + (n - 16256) = n := by omega
    rw [← e]
    exact block01_127 ⟨n - 16256, by omega⟩
  · have e : 16384 + (n - 16384) = n := by omega
    rw [← e]
    exact block01_128 ⟨n - 16384, by omega⟩
end KsIndex.PositiveEnergyAlphaLowProd
