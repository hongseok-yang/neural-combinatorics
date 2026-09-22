import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks0000
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks0512
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks1024
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks1536
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks2048
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks2560
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks3072
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks3584
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks4096
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks4608
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks5120
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks5632
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks6144
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks6656
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks7168
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks7680
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks8192
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks8704
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks9216
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks9728
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks10240
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks10752
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks11264
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks11776
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks12288
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks12800
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks13312
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks13824
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks14336
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks14848
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks15360
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks15872
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks16384
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks16896
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks17408
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks17920
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks18432
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks18944
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks19456
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks19968
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks20480
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks20992
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks21504
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks22016
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks22528
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks23040
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks23552
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks24064
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks24576
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks25088
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks25600
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks26112
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks26624
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks27136
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks27648
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks28160
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks28672
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks29184
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks29696
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks30208
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks30720
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks31232
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks31744
import Taeyoung.Methods.RootedSOS.Induced.Six.ClassificationChecks32256
import Taeyoung.Methods.RootedSOS.Induced.Six.Permutations
namespace Taeyoung.Methods.RootedSOS.Induced.Six
theorem classificationCheck_all (k : Fin 32768) : classificationCheck k := by
  by_cases h : k.1 < 512
  · let j : Fin 512 := ⟨k.1-0, by omega⟩
    have he : (⟨0+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_0000 j
  by_cases h : k.1 < 1024
  · let j : Fin 512 := ⟨k.1-512, by omega⟩
    have he : (⟨512+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_0512 j
  by_cases h : k.1 < 1536
  · let j : Fin 512 := ⟨k.1-1024, by omega⟩
    have he : (⟨1024+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_1024 j
  by_cases h : k.1 < 2048
  · let j : Fin 512 := ⟨k.1-1536, by omega⟩
    have he : (⟨1536+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_1536 j
  by_cases h : k.1 < 2560
  · let j : Fin 512 := ⟨k.1-2048, by omega⟩
    have he : (⟨2048+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_2048 j
  by_cases h : k.1 < 3072
  · let j : Fin 512 := ⟨k.1-2560, by omega⟩
    have he : (⟨2560+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_2560 j
  by_cases h : k.1 < 3584
  · let j : Fin 512 := ⟨k.1-3072, by omega⟩
    have he : (⟨3072+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_3072 j
  by_cases h : k.1 < 4096
  · let j : Fin 512 := ⟨k.1-3584, by omega⟩
    have he : (⟨3584+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_3584 j
  by_cases h : k.1 < 4608
  · let j : Fin 512 := ⟨k.1-4096, by omega⟩
    have he : (⟨4096+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_4096 j
  by_cases h : k.1 < 5120
  · let j : Fin 512 := ⟨k.1-4608, by omega⟩
    have he : (⟨4608+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_4608 j
  by_cases h : k.1 < 5632
  · let j : Fin 512 := ⟨k.1-5120, by omega⟩
    have he : (⟨5120+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_5120 j
  by_cases h : k.1 < 6144
  · let j : Fin 512 := ⟨k.1-5632, by omega⟩
    have he : (⟨5632+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_5632 j
  by_cases h : k.1 < 6656
  · let j : Fin 512 := ⟨k.1-6144, by omega⟩
    have he : (⟨6144+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_6144 j
  by_cases h : k.1 < 7168
  · let j : Fin 512 := ⟨k.1-6656, by omega⟩
    have he : (⟨6656+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_6656 j
  by_cases h : k.1 < 7680
  · let j : Fin 512 := ⟨k.1-7168, by omega⟩
    have he : (⟨7168+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_7168 j
  by_cases h : k.1 < 8192
  · let j : Fin 512 := ⟨k.1-7680, by omega⟩
    have he : (⟨7680+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_7680 j
  by_cases h : k.1 < 8704
  · let j : Fin 512 := ⟨k.1-8192, by omega⟩
    have he : (⟨8192+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_8192 j
  by_cases h : k.1 < 9216
  · let j : Fin 512 := ⟨k.1-8704, by omega⟩
    have he : (⟨8704+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_8704 j
  by_cases h : k.1 < 9728
  · let j : Fin 512 := ⟨k.1-9216, by omega⟩
    have he : (⟨9216+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_9216 j
  by_cases h : k.1 < 10240
  · let j : Fin 512 := ⟨k.1-9728, by omega⟩
    have he : (⟨9728+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_9728 j
  by_cases h : k.1 < 10752
  · let j : Fin 512 := ⟨k.1-10240, by omega⟩
    have he : (⟨10240+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_10240 j
  by_cases h : k.1 < 11264
  · let j : Fin 512 := ⟨k.1-10752, by omega⟩
    have he : (⟨10752+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_10752 j
  by_cases h : k.1 < 11776
  · let j : Fin 512 := ⟨k.1-11264, by omega⟩
    have he : (⟨11264+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_11264 j
  by_cases h : k.1 < 12288
  · let j : Fin 512 := ⟨k.1-11776, by omega⟩
    have he : (⟨11776+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_11776 j
  by_cases h : k.1 < 12800
  · let j : Fin 512 := ⟨k.1-12288, by omega⟩
    have he : (⟨12288+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_12288 j
  by_cases h : k.1 < 13312
  · let j : Fin 512 := ⟨k.1-12800, by omega⟩
    have he : (⟨12800+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_12800 j
  by_cases h : k.1 < 13824
  · let j : Fin 512 := ⟨k.1-13312, by omega⟩
    have he : (⟨13312+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_13312 j
  by_cases h : k.1 < 14336
  · let j : Fin 512 := ⟨k.1-13824, by omega⟩
    have he : (⟨13824+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_13824 j
  by_cases h : k.1 < 14848
  · let j : Fin 512 := ⟨k.1-14336, by omega⟩
    have he : (⟨14336+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_14336 j
  by_cases h : k.1 < 15360
  · let j : Fin 512 := ⟨k.1-14848, by omega⟩
    have he : (⟨14848+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_14848 j
  by_cases h : k.1 < 15872
  · let j : Fin 512 := ⟨k.1-15360, by omega⟩
    have he : (⟨15360+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_15360 j
  by_cases h : k.1 < 16384
  · let j : Fin 512 := ⟨k.1-15872, by omega⟩
    have he : (⟨15872+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_15872 j
  by_cases h : k.1 < 16896
  · let j : Fin 512 := ⟨k.1-16384, by omega⟩
    have he : (⟨16384+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_16384 j
  by_cases h : k.1 < 17408
  · let j : Fin 512 := ⟨k.1-16896, by omega⟩
    have he : (⟨16896+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_16896 j
  by_cases h : k.1 < 17920
  · let j : Fin 512 := ⟨k.1-17408, by omega⟩
    have he : (⟨17408+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_17408 j
  by_cases h : k.1 < 18432
  · let j : Fin 512 := ⟨k.1-17920, by omega⟩
    have he : (⟨17920+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_17920 j
  by_cases h : k.1 < 18944
  · let j : Fin 512 := ⟨k.1-18432, by omega⟩
    have he : (⟨18432+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_18432 j
  by_cases h : k.1 < 19456
  · let j : Fin 512 := ⟨k.1-18944, by omega⟩
    have he : (⟨18944+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_18944 j
  by_cases h : k.1 < 19968
  · let j : Fin 512 := ⟨k.1-19456, by omega⟩
    have he : (⟨19456+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_19456 j
  by_cases h : k.1 < 20480
  · let j : Fin 512 := ⟨k.1-19968, by omega⟩
    have he : (⟨19968+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_19968 j
  by_cases h : k.1 < 20992
  · let j : Fin 512 := ⟨k.1-20480, by omega⟩
    have he : (⟨20480+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_20480 j
  by_cases h : k.1 < 21504
  · let j : Fin 512 := ⟨k.1-20992, by omega⟩
    have he : (⟨20992+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_20992 j
  by_cases h : k.1 < 22016
  · let j : Fin 512 := ⟨k.1-21504, by omega⟩
    have he : (⟨21504+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_21504 j
  by_cases h : k.1 < 22528
  · let j : Fin 512 := ⟨k.1-22016, by omega⟩
    have he : (⟨22016+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_22016 j
  by_cases h : k.1 < 23040
  · let j : Fin 512 := ⟨k.1-22528, by omega⟩
    have he : (⟨22528+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_22528 j
  by_cases h : k.1 < 23552
  · let j : Fin 512 := ⟨k.1-23040, by omega⟩
    have he : (⟨23040+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_23040 j
  by_cases h : k.1 < 24064
  · let j : Fin 512 := ⟨k.1-23552, by omega⟩
    have he : (⟨23552+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_23552 j
  by_cases h : k.1 < 24576
  · let j : Fin 512 := ⟨k.1-24064, by omega⟩
    have he : (⟨24064+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_24064 j
  by_cases h : k.1 < 25088
  · let j : Fin 512 := ⟨k.1-24576, by omega⟩
    have he : (⟨24576+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_24576 j
  by_cases h : k.1 < 25600
  · let j : Fin 512 := ⟨k.1-25088, by omega⟩
    have he : (⟨25088+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_25088 j
  by_cases h : k.1 < 26112
  · let j : Fin 512 := ⟨k.1-25600, by omega⟩
    have he : (⟨25600+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_25600 j
  by_cases h : k.1 < 26624
  · let j : Fin 512 := ⟨k.1-26112, by omega⟩
    have he : (⟨26112+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_26112 j
  by_cases h : k.1 < 27136
  · let j : Fin 512 := ⟨k.1-26624, by omega⟩
    have he : (⟨26624+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_26624 j
  by_cases h : k.1 < 27648
  · let j : Fin 512 := ⟨k.1-27136, by omega⟩
    have he : (⟨27136+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_27136 j
  by_cases h : k.1 < 28160
  · let j : Fin 512 := ⟨k.1-27648, by omega⟩
    have he : (⟨27648+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_27648 j
  by_cases h : k.1 < 28672
  · let j : Fin 512 := ⟨k.1-28160, by omega⟩
    have he : (⟨28160+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_28160 j
  by_cases h : k.1 < 29184
  · let j : Fin 512 := ⟨k.1-28672, by omega⟩
    have he : (⟨28672+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_28672 j
  by_cases h : k.1 < 29696
  · let j : Fin 512 := ⟨k.1-29184, by omega⟩
    have he : (⟨29184+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_29184 j
  by_cases h : k.1 < 30208
  · let j : Fin 512 := ⟨k.1-29696, by omega⟩
    have he : (⟨29696+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_29696 j
  by_cases h : k.1 < 30720
  · let j : Fin 512 := ⟨k.1-30208, by omega⟩
    have he : (⟨30208+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_30208 j
  by_cases h : k.1 < 31232
  · let j : Fin 512 := ⟨k.1-30720, by omega⟩
    have he : (⟨30720+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_30720 j
  by_cases h : k.1 < 31744
  · let j : Fin 512 := ⟨k.1-31232, by omega⟩
    have he : (⟨31232+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_31232 j
  by_cases h : k.1 < 32256
  · let j : Fin 512 := ⟨k.1-31744, by omega⟩
    have he : (⟨31744+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_31744 j
  by_cases h : k.1 < 32768
  · let j : Fin 512 := ⟨k.1-32256, by omega⟩
    have he : (⟨32256+j.1, by omega⟩ : Fin 32768) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ClassificationChecks_32256 j
  omega

open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
noncomputable def density (j : Fin 156) (W : Taeyoung.Graphon Ω μ) : Real :=
  inducedDensity pairs (bits (hostCode j)) W
theorem density_nonneg (j : Fin 156) (W : Taeyoung.Graphon Ω μ) : 0 ≤ density j W :=
  inducedDensity_nonneg _ _ W
theorem inducedDensity_classification (code : Fin 32768) (W : Taeyoung.Graphon Ω μ) :
    inducedDensity pairs (bits code) W = density (host code) W :=
  inducedDensity_relabel pairs pairs (bits code) (bits (hostCode (host code)))
    (vertexEquiv (permutation code)) (edgeEquiv (permutation code))
    (classificationCheck_all code) (permutationCheck_all (permutation code)).2.2 W
end Taeyoung.Methods.RootedSOS.Induced.Six
