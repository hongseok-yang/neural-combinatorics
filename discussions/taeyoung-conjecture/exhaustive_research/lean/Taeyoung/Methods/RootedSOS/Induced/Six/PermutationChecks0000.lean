import Taeyoung.Methods.RootedSOS.Induced.Six.Base
namespace Taeyoung.Methods.RootedSOS.Induced.Six
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_0000 : ∀ i : Fin 8,
    permutationCheck ⟨0+i.1, by omega⟩ := by decide +kernel
private theorem check_0008 : ∀ i : Fin 8,
    permutationCheck ⟨8+i.1, by omega⟩ := by decide +kernel
private theorem check_0016 : ∀ i : Fin 8,
    permutationCheck ⟨16+i.1, by omega⟩ := by decide +kernel
private theorem check_0024 : ∀ i : Fin 8,
    permutationCheck ⟨24+i.1, by omega⟩ := by decide +kernel
private theorem check_0032 : ∀ i : Fin 8,
    permutationCheck ⟨32+i.1, by omega⟩ := by decide +kernel
private theorem check_0040 : ∀ i : Fin 8,
    permutationCheck ⟨40+i.1, by omega⟩ := by decide +kernel
private theorem check_0048 : ∀ i : Fin 8,
    permutationCheck ⟨48+i.1, by omega⟩ := by decide +kernel
private theorem check_0056 : ∀ i : Fin 8,
    permutationCheck ⟨56+i.1, by omega⟩ := by decide +kernel
private theorem check_0064 : ∀ i : Fin 8,
    permutationCheck ⟨64+i.1, by omega⟩ := by decide +kernel
private theorem check_0072 : ∀ i : Fin 8,
    permutationCheck ⟨72+i.1, by omega⟩ := by decide +kernel
private theorem check_0080 : ∀ i : Fin 8,
    permutationCheck ⟨80+i.1, by omega⟩ := by decide +kernel
private theorem check_0088 : ∀ i : Fin 8,
    permutationCheck ⟨88+i.1, by omega⟩ := by decide +kernel
private theorem check_0096 : ∀ i : Fin 8,
    permutationCheck ⟨96+i.1, by omega⟩ := by decide +kernel
private theorem check_0104 : ∀ i : Fin 8,
    permutationCheck ⟨104+i.1, by omega⟩ := by decide +kernel
private theorem check_0112 : ∀ i : Fin 8,
    permutationCheck ⟨112+i.1, by omega⟩ := by decide +kernel
private theorem check_0120 : ∀ i : Fin 8,
    permutationCheck ⟨120+i.1, by omega⟩ := by decide +kernel
private theorem check_0128 : ∀ i : Fin 8,
    permutationCheck ⟨128+i.1, by omega⟩ := by decide +kernel
private theorem check_0136 : ∀ i : Fin 8,
    permutationCheck ⟨136+i.1, by omega⟩ := by decide +kernel
private theorem check_0144 : ∀ i : Fin 8,
    permutationCheck ⟨144+i.1, by omega⟩ := by decide +kernel
private theorem check_0152 : ∀ i : Fin 8,
    permutationCheck ⟨152+i.1, by omega⟩ := by decide +kernel
private theorem check_0160 : ∀ i : Fin 8,
    permutationCheck ⟨160+i.1, by omega⟩ := by decide +kernel
private theorem check_0168 : ∀ i : Fin 8,
    permutationCheck ⟨168+i.1, by omega⟩ := by decide +kernel
private theorem check_0176 : ∀ i : Fin 8,
    permutationCheck ⟨176+i.1, by omega⟩ := by decide +kernel
private theorem check_0184 : ∀ i : Fin 8,
    permutationCheck ⟨184+i.1, by omega⟩ := by decide +kernel
private theorem check_0192 : ∀ i : Fin 8,
    permutationCheck ⟨192+i.1, by omega⟩ := by decide +kernel
private theorem check_0200 : ∀ i : Fin 8,
    permutationCheck ⟨200+i.1, by omega⟩ := by decide +kernel
private theorem check_0208 : ∀ i : Fin 8,
    permutationCheck ⟨208+i.1, by omega⟩ := by decide +kernel
private theorem check_0216 : ∀ i : Fin 8,
    permutationCheck ⟨216+i.1, by omega⟩ := by decide +kernel
private theorem check_0224 : ∀ i : Fin 8,
    permutationCheck ⟨224+i.1, by omega⟩ := by decide +kernel
private theorem check_0232 : ∀ i : Fin 8,
    permutationCheck ⟨232+i.1, by omega⟩ := by decide +kernel
theorem PermutationChecks_0000 (i : Fin 240) : permutationCheck ⟨0+i.1, by omega⟩ := by
  by_cases h : i.1 < 8
  · let j : Fin 8 := ⟨i.1-0, by omega⟩
    have he : (⟨0+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0000 j
  by_cases h : i.1 < 16
  · let j : Fin 8 := ⟨i.1-8, by omega⟩
    have he : (⟨8+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0008 j
  by_cases h : i.1 < 24
  · let j : Fin 8 := ⟨i.1-16, by omega⟩
    have he : (⟨16+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0016 j
  by_cases h : i.1 < 32
  · let j : Fin 8 := ⟨i.1-24, by omega⟩
    have he : (⟨24+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0024 j
  by_cases h : i.1 < 40
  · let j : Fin 8 := ⟨i.1-32, by omega⟩
    have he : (⟨32+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0032 j
  by_cases h : i.1 < 48
  · let j : Fin 8 := ⟨i.1-40, by omega⟩
    have he : (⟨40+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0040 j
  by_cases h : i.1 < 56
  · let j : Fin 8 := ⟨i.1-48, by omega⟩
    have he : (⟨48+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0048 j
  by_cases h : i.1 < 64
  · let j : Fin 8 := ⟨i.1-56, by omega⟩
    have he : (⟨56+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0056 j
  by_cases h : i.1 < 72
  · let j : Fin 8 := ⟨i.1-64, by omega⟩
    have he : (⟨64+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0064 j
  by_cases h : i.1 < 80
  · let j : Fin 8 := ⟨i.1-72, by omega⟩
    have he : (⟨72+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0072 j
  by_cases h : i.1 < 88
  · let j : Fin 8 := ⟨i.1-80, by omega⟩
    have he : (⟨80+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0080 j
  by_cases h : i.1 < 96
  · let j : Fin 8 := ⟨i.1-88, by omega⟩
    have he : (⟨88+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0088 j
  by_cases h : i.1 < 104
  · let j : Fin 8 := ⟨i.1-96, by omega⟩
    have he : (⟨96+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0096 j
  by_cases h : i.1 < 112
  · let j : Fin 8 := ⟨i.1-104, by omega⟩
    have he : (⟨104+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0104 j
  by_cases h : i.1 < 120
  · let j : Fin 8 := ⟨i.1-112, by omega⟩
    have he : (⟨112+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0112 j
  by_cases h : i.1 < 128
  · let j : Fin 8 := ⟨i.1-120, by omega⟩
    have he : (⟨120+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0120 j
  by_cases h : i.1 < 136
  · let j : Fin 8 := ⟨i.1-128, by omega⟩
    have he : (⟨128+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0128 j
  by_cases h : i.1 < 144
  · let j : Fin 8 := ⟨i.1-136, by omega⟩
    have he : (⟨136+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0136 j
  by_cases h : i.1 < 152
  · let j : Fin 8 := ⟨i.1-144, by omega⟩
    have he : (⟨144+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0144 j
  by_cases h : i.1 < 160
  · let j : Fin 8 := ⟨i.1-152, by omega⟩
    have he : (⟨152+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0152 j
  by_cases h : i.1 < 168
  · let j : Fin 8 := ⟨i.1-160, by omega⟩
    have he : (⟨160+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0160 j
  by_cases h : i.1 < 176
  · let j : Fin 8 := ⟨i.1-168, by omega⟩
    have he : (⟨168+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0168 j
  by_cases h : i.1 < 184
  · let j : Fin 8 := ⟨i.1-176, by omega⟩
    have he : (⟨176+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0176 j
  by_cases h : i.1 < 192
  · let j : Fin 8 := ⟨i.1-184, by omega⟩
    have he : (⟨184+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0184 j
  by_cases h : i.1 < 200
  · let j : Fin 8 := ⟨i.1-192, by omega⟩
    have he : (⟨192+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0192 j
  by_cases h : i.1 < 208
  · let j : Fin 8 := ⟨i.1-200, by omega⟩
    have he : (⟨200+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0200 j
  by_cases h : i.1 < 216
  · let j : Fin 8 := ⟨i.1-208, by omega⟩
    have he : (⟨208+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0208 j
  by_cases h : i.1 < 224
  · let j : Fin 8 := ⟨i.1-216, by omega⟩
    have he : (⟨216+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0216 j
  by_cases h : i.1 < 232
  · let j : Fin 8 := ⟨i.1-224, by omega⟩
    have he : (⟨224+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0224 j
  by_cases h : i.1 < 240
  · let j : Fin 8 := ⟨i.1-232, by omega⟩
    have he : (⟨232+j.1, by omega⟩ : Fin 720) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0232 j
  omega
end Taeyoung.Methods.RootedSOS.Induced.Six
