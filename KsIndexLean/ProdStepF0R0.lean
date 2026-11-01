module

public import KsIndexLean.ProdCheckF0R0P0
public import KsIndexLean.ProdCheckF0R0P1
public import KsIndexLean.ProdCheckF0R0P2
public import KsIndexLean.ProdCheckF0R0P3
public import KsIndexLean.ProdCheckF0R0P4
public import KsIndexLean.ProdCheckF0R0P5
public import KsIndexLean.ProdCheckF0R0P6
public import KsIndexLean.ProdCheckF0R0P7
public import KsIndexLean.ProdCheckF0R0P8

@[expose] public section

/-! Step assembly for stream (0,0). -/
namespace KsIndex.NegSignProd
theorem step00 : ∀ n < 8196, t 2161809 0 (n + 1) =
    (2161809 - 5000000 * ((0 : ℤ) + 2 * n)) * t 2161809 0 n /
      (2161809 + 5000000 * ((0 : ℤ) + 2 * n + 2)) := by
  intro n hn
  by_cases h0 : n < 128
  · exact block00_0 ⟨n, h0⟩
  by_cases h128 : n < 256
  · have e : 128 + (n - 128) = n := by omega
    rw [← e]
    exact block00_1 ⟨n - 128, by omega⟩
  by_cases h256 : n < 384
  · have e : 256 + (n - 256) = n := by omega
    rw [← e]
    exact block00_2 ⟨n - 256, by omega⟩
  by_cases h384 : n < 512
  · have e : 384 + (n - 384) = n := by omega
    rw [← e]
    exact block00_3 ⟨n - 384, by omega⟩
  by_cases h512 : n < 640
  · have e : 512 + (n - 512) = n := by omega
    rw [← e]
    exact block00_4 ⟨n - 512, by omega⟩
  by_cases h640 : n < 768
  · have e : 640 + (n - 640) = n := by omega
    rw [← e]
    exact block00_5 ⟨n - 640, by omega⟩
  by_cases h768 : n < 896
  · have e : 768 + (n - 768) = n := by omega
    rw [← e]
    exact block00_6 ⟨n - 768, by omega⟩
  by_cases h896 : n < 1024
  · have e : 896 + (n - 896) = n := by omega
    rw [← e]
    exact block00_7 ⟨n - 896, by omega⟩
  by_cases h1024 : n < 1152
  · have e : 1024 + (n - 1024) = n := by omega
    rw [← e]
    exact block00_8 ⟨n - 1024, by omega⟩
  by_cases h1152 : n < 1280
  · have e : 1152 + (n - 1152) = n := by omega
    rw [← e]
    exact block00_9 ⟨n - 1152, by omega⟩
  by_cases h1280 : n < 1408
  · have e : 1280 + (n - 1280) = n := by omega
    rw [← e]
    exact block00_10 ⟨n - 1280, by omega⟩
  by_cases h1408 : n < 1536
  · have e : 1408 + (n - 1408) = n := by omega
    rw [← e]
    exact block00_11 ⟨n - 1408, by omega⟩
  by_cases h1536 : n < 1664
  · have e : 1536 + (n - 1536) = n := by omega
    rw [← e]
    exact block00_12 ⟨n - 1536, by omega⟩
  by_cases h1664 : n < 1792
  · have e : 1664 + (n - 1664) = n := by omega
    rw [← e]
    exact block00_13 ⟨n - 1664, by omega⟩
  by_cases h1792 : n < 1920
  · have e : 1792 + (n - 1792) = n := by omega
    rw [← e]
    exact block00_14 ⟨n - 1792, by omega⟩
  by_cases h1920 : n < 2048
  · have e : 1920 + (n - 1920) = n := by omega
    rw [← e]
    exact block00_15 ⟨n - 1920, by omega⟩
  by_cases h2048 : n < 2176
  · have e : 2048 + (n - 2048) = n := by omega
    rw [← e]
    exact block00_16 ⟨n - 2048, by omega⟩
  by_cases h2176 : n < 2304
  · have e : 2176 + (n - 2176) = n := by omega
    rw [← e]
    exact block00_17 ⟨n - 2176, by omega⟩
  by_cases h2304 : n < 2432
  · have e : 2304 + (n - 2304) = n := by omega
    rw [← e]
    exact block00_18 ⟨n - 2304, by omega⟩
  by_cases h2432 : n < 2560
  · have e : 2432 + (n - 2432) = n := by omega
    rw [← e]
    exact block00_19 ⟨n - 2432, by omega⟩
  by_cases h2560 : n < 2688
  · have e : 2560 + (n - 2560) = n := by omega
    rw [← e]
    exact block00_20 ⟨n - 2560, by omega⟩
  by_cases h2688 : n < 2816
  · have e : 2688 + (n - 2688) = n := by omega
    rw [← e]
    exact block00_21 ⟨n - 2688, by omega⟩
  by_cases h2816 : n < 2944
  · have e : 2816 + (n - 2816) = n := by omega
    rw [← e]
    exact block00_22 ⟨n - 2816, by omega⟩
  by_cases h2944 : n < 3072
  · have e : 2944 + (n - 2944) = n := by omega
    rw [← e]
    exact block00_23 ⟨n - 2944, by omega⟩
  by_cases h3072 : n < 3200
  · have e : 3072 + (n - 3072) = n := by omega
    rw [← e]
    exact block00_24 ⟨n - 3072, by omega⟩
  by_cases h3200 : n < 3328
  · have e : 3200 + (n - 3200) = n := by omega
    rw [← e]
    exact block00_25 ⟨n - 3200, by omega⟩
  by_cases h3328 : n < 3456
  · have e : 3328 + (n - 3328) = n := by omega
    rw [← e]
    exact block00_26 ⟨n - 3328, by omega⟩
  by_cases h3456 : n < 3584
  · have e : 3456 + (n - 3456) = n := by omega
    rw [← e]
    exact block00_27 ⟨n - 3456, by omega⟩
  by_cases h3584 : n < 3712
  · have e : 3584 + (n - 3584) = n := by omega
    rw [← e]
    exact block00_28 ⟨n - 3584, by omega⟩
  by_cases h3712 : n < 3840
  · have e : 3712 + (n - 3712) = n := by omega
    rw [← e]
    exact block00_29 ⟨n - 3712, by omega⟩
  by_cases h3840 : n < 3968
  · have e : 3840 + (n - 3840) = n := by omega
    rw [← e]
    exact block00_30 ⟨n - 3840, by omega⟩
  by_cases h3968 : n < 4096
  · have e : 3968 + (n - 3968) = n := by omega
    rw [← e]
    exact block00_31 ⟨n - 3968, by omega⟩
  by_cases h4096 : n < 4224
  · have e : 4096 + (n - 4096) = n := by omega
    rw [← e]
    exact block00_32 ⟨n - 4096, by omega⟩
  by_cases h4224 : n < 4352
  · have e : 4224 + (n - 4224) = n := by omega
    rw [← e]
    exact block00_33 ⟨n - 4224, by omega⟩
  by_cases h4352 : n < 4480
  · have e : 4352 + (n - 4352) = n := by omega
    rw [← e]
    exact block00_34 ⟨n - 4352, by omega⟩
  by_cases h4480 : n < 4608
  · have e : 4480 + (n - 4480) = n := by omega
    rw [← e]
    exact block00_35 ⟨n - 4480, by omega⟩
  by_cases h4608 : n < 4736
  · have e : 4608 + (n - 4608) = n := by omega
    rw [← e]
    exact block00_36 ⟨n - 4608, by omega⟩
  by_cases h4736 : n < 4864
  · have e : 4736 + (n - 4736) = n := by omega
    rw [← e]
    exact block00_37 ⟨n - 4736, by omega⟩
  by_cases h4864 : n < 4992
  · have e : 4864 + (n - 4864) = n := by omega
    rw [← e]
    exact block00_38 ⟨n - 4864, by omega⟩
  by_cases h4992 : n < 5120
  · have e : 4992 + (n - 4992) = n := by omega
    rw [← e]
    exact block00_39 ⟨n - 4992, by omega⟩
  by_cases h5120 : n < 5248
  · have e : 5120 + (n - 5120) = n := by omega
    rw [← e]
    exact block00_40 ⟨n - 5120, by omega⟩
  by_cases h5248 : n < 5376
  · have e : 5248 + (n - 5248) = n := by omega
    rw [← e]
    exact block00_41 ⟨n - 5248, by omega⟩
  by_cases h5376 : n < 5504
  · have e : 5376 + (n - 5376) = n := by omega
    rw [← e]
    exact block00_42 ⟨n - 5376, by omega⟩
  by_cases h5504 : n < 5632
  · have e : 5504 + (n - 5504) = n := by omega
    rw [← e]
    exact block00_43 ⟨n - 5504, by omega⟩
  by_cases h5632 : n < 5760
  · have e : 5632 + (n - 5632) = n := by omega
    rw [← e]
    exact block00_44 ⟨n - 5632, by omega⟩
  by_cases h5760 : n < 5888
  · have e : 5760 + (n - 5760) = n := by omega
    rw [← e]
    exact block00_45 ⟨n - 5760, by omega⟩
  by_cases h5888 : n < 6016
  · have e : 5888 + (n - 5888) = n := by omega
    rw [← e]
    exact block00_46 ⟨n - 5888, by omega⟩
  by_cases h6016 : n < 6144
  · have e : 6016 + (n - 6016) = n := by omega
    rw [← e]
    exact block00_47 ⟨n - 6016, by omega⟩
  by_cases h6144 : n < 6272
  · have e : 6144 + (n - 6144) = n := by omega
    rw [← e]
    exact block00_48 ⟨n - 6144, by omega⟩
  by_cases h6272 : n < 6400
  · have e : 6272 + (n - 6272) = n := by omega
    rw [← e]
    exact block00_49 ⟨n - 6272, by omega⟩
  by_cases h6400 : n < 6528
  · have e : 6400 + (n - 6400) = n := by omega
    rw [← e]
    exact block00_50 ⟨n - 6400, by omega⟩
  by_cases h6528 : n < 6656
  · have e : 6528 + (n - 6528) = n := by omega
    rw [← e]
    exact block00_51 ⟨n - 6528, by omega⟩
  by_cases h6656 : n < 6784
  · have e : 6656 + (n - 6656) = n := by omega
    rw [← e]
    exact block00_52 ⟨n - 6656, by omega⟩
  by_cases h6784 : n < 6912
  · have e : 6784 + (n - 6784) = n := by omega
    rw [← e]
    exact block00_53 ⟨n - 6784, by omega⟩
  by_cases h6912 : n < 7040
  · have e : 6912 + (n - 6912) = n := by omega
    rw [← e]
    exact block00_54 ⟨n - 6912, by omega⟩
  by_cases h7040 : n < 7168
  · have e : 7040 + (n - 7040) = n := by omega
    rw [← e]
    exact block00_55 ⟨n - 7040, by omega⟩
  by_cases h7168 : n < 7296
  · have e : 7168 + (n - 7168) = n := by omega
    rw [← e]
    exact block00_56 ⟨n - 7168, by omega⟩
  by_cases h7296 : n < 7424
  · have e : 7296 + (n - 7296) = n := by omega
    rw [← e]
    exact block00_57 ⟨n - 7296, by omega⟩
  by_cases h7424 : n < 7552
  · have e : 7424 + (n - 7424) = n := by omega
    rw [← e]
    exact block00_58 ⟨n - 7424, by omega⟩
  by_cases h7552 : n < 7680
  · have e : 7552 + (n - 7552) = n := by omega
    rw [← e]
    exact block00_59 ⟨n - 7552, by omega⟩
  by_cases h7680 : n < 7808
  · have e : 7680 + (n - 7680) = n := by omega
    rw [← e]
    exact block00_60 ⟨n - 7680, by omega⟩
  by_cases h7808 : n < 7936
  · have e : 7808 + (n - 7808) = n := by omega
    rw [← e]
    exact block00_61 ⟨n - 7808, by omega⟩
  by_cases h7936 : n < 8064
  · have e : 7936 + (n - 7936) = n := by omega
    rw [← e]
    exact block00_62 ⟨n - 7936, by omega⟩
  by_cases h8064 : n < 8192
  · have e : 8064 + (n - 8064) = n := by omega
    rw [← e]
    exact block00_63 ⟨n - 8064, by omega⟩
  · have e : 8192 + (n - 8192) = n := by omega
    rw [← e]
    exact block00_64 ⟨n - 8192, by omega⟩
end KsIndex.NegSignProd
