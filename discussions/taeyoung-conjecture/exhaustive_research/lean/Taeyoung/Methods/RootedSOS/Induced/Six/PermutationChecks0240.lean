import Taeyoung.Methods.RootedSOS.Induced.Six.Base
namespace Taeyoung.Methods.RootedSOS.Induced.Six
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_0240 : ∀ i : Fin 8,
    permutationCheck ⟨240+i.1, by omega⟩ := by decide +kernel
private theorem check_0248 : ∀ i : Fin 8,
    permutationCheck ⟨248+i.1, by omega⟩ := by decide +kernel
private theorem check_0256 : ∀ i : Fin 8,
    permutationCheck ⟨256+i.1, by omega⟩ := by decide +kernel
private theorem check_0264 : ∀ i : Fin 8,
    permutationCheck ⟨264+i.1, by omega⟩ := by decide +kernel
private theorem check_0272 : ∀ i : Fin 8,
    permutationCheck ⟨272+i.1, by omega⟩ := by decide +kernel
private theorem check_0280 : ∀ i : Fin 8,
    permutationCheck ⟨280+i.1, by omega⟩ := by decide +kernel
private theorem check_0288 : ∀ i : Fin 8,
    permutationCheck ⟨288+i.1, by omega⟩ := by decide +kernel
private theorem check_0296 : ∀ i : Fin 8,
    permutationCheck ⟨296+i.1, by omega⟩ := by decide +kernel
private theorem check_0304 : ∀ i : Fin 8,
    permutationCheck ⟨304+i.1, by omega⟩ := by decide +kernel
private theorem check_0312 : ∀ i : Fin 8,
    permutationCheck ⟨312+i.1, by omega⟩ := by decide +kernel
private theorem check_0320 : ∀ i : Fin 8,
    permutationCheck ⟨320+i.1, by omega⟩ := by decide +kernel
private theorem check_0328 : ∀ i : Fin 8,
    permutationCheck ⟨328+i.1, by omega⟩ := by decide +kernel
private theorem check_0336 : ∀ i : Fin 8,
    permutationCheck ⟨336+i.1, by omega⟩ := by decide +kernel
private theorem check_0344 : ∀ i : Fin 8,
    permutationCheck ⟨344+i.1, by omega⟩ := by decide +kernel
private theorem check_0352 : ∀ i : Fin 8,
    permutationCheck ⟨352+i.1, by omega⟩ := by decide +kernel
private theorem check_0360 : ∀ i : Fin 8,
    permutationCheck ⟨360+i.1, by omega⟩ := by decide +kernel
private theorem check_0368 : ∀ i : Fin 8,
    permutationCheck ⟨368+i.1, by omega⟩ := by decide +kernel
private theorem check_0376 : ∀ i : Fin 8,
    permutationCheck ⟨376+i.1, by omega⟩ := by decide +kernel
private theorem check_0384 : ∀ i : Fin 8,
    permutationCheck ⟨384+i.1, by omega⟩ := by decide +kernel
private theorem check_0392 : ∀ i : Fin 8,
    permutationCheck ⟨392+i.1, by omega⟩ := by decide +kernel
private theorem check_0400 : ∀ i : Fin 8,
    permutationCheck ⟨400+i.1, by omega⟩ := by decide +kernel
private theorem check_0408 : ∀ i : Fin 8,
    permutationCheck ⟨408+i.1, by omega⟩ := by decide +kernel
private theorem check_0416 : ∀ i : Fin 8,
    permutationCheck ⟨416+i.1, by omega⟩ := by decide +kernel
private theorem check_0424 : ∀ i : Fin 8,
    permutationCheck ⟨424+i.1, by omega⟩ := by decide +kernel
private theorem check_0432 : ∀ i : Fin 8,
    permutationCheck ⟨432+i.1, by omega⟩ := by decide +kernel
private theorem check_0440 : ∀ i : Fin 8,
    permutationCheck ⟨440+i.1, by omega⟩ := by decide +kernel
private theorem check_0448 : ∀ i : Fin 8,
    permutationCheck ⟨448+i.1, by omega⟩ := by decide +kernel
private theorem check_0456 : ∀ i : Fin 8,
    permutationCheck ⟨456+i.1, by omega⟩ := by decide +kernel
private theorem check_0464 : ∀ i : Fin 8,
    permutationCheck ⟨464+i.1, by omega⟩ := by decide +kernel
private theorem check_0472 : ∀ i : Fin 8,
    permutationCheck ⟨472+i.1, by omega⟩ := by decide +kernel
theorem PermutationChecks_0240 (i : Fin 240) : permutationCheck ⟨240+i.1, by omega⟩ := by
  by_cases h : i.1 < 8
  · let j : Fin 8 := ⟨i.1-0, by omega⟩
    have he : (⟨240+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0240 j
  by_cases h : i.1 < 16
  · let j : Fin 8 := ⟨i.1-8, by omega⟩
    have he : (⟨248+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0248 j
  by_cases h : i.1 < 24
  · let j : Fin 8 := ⟨i.1-16, by omega⟩
    have he : (⟨256+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0256 j
  by_cases h : i.1 < 32
  · let j : Fin 8 := ⟨i.1-24, by omega⟩
    have he : (⟨264+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0264 j
  by_cases h : i.1 < 40
  · let j : Fin 8 := ⟨i.1-32, by omega⟩
    have he : (⟨272+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0272 j
  by_cases h : i.1 < 48
  · let j : Fin 8 := ⟨i.1-40, by omega⟩
    have he : (⟨280+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0280 j
  by_cases h : i.1 < 56
  · let j : Fin 8 := ⟨i.1-48, by omega⟩
    have he : (⟨288+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0288 j
  by_cases h : i.1 < 64
  · let j : Fin 8 := ⟨i.1-56, by omega⟩
    have he : (⟨296+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0296 j
  by_cases h : i.1 < 72
  · let j : Fin 8 := ⟨i.1-64, by omega⟩
    have he : (⟨304+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0304 j
  by_cases h : i.1 < 80
  · let j : Fin 8 := ⟨i.1-72, by omega⟩
    have he : (⟨312+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0312 j
  by_cases h : i.1 < 88
  · let j : Fin 8 := ⟨i.1-80, by omega⟩
    have he : (⟨320+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0320 j
  by_cases h : i.1 < 96
  · let j : Fin 8 := ⟨i.1-88, by omega⟩
    have he : (⟨328+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0328 j
  by_cases h : i.1 < 104
  · let j : Fin 8 := ⟨i.1-96, by omega⟩
    have he : (⟨336+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0336 j
  by_cases h : i.1 < 112
  · let j : Fin 8 := ⟨i.1-104, by omega⟩
    have he : (⟨344+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0344 j
  by_cases h : i.1 < 120
  · let j : Fin 8 := ⟨i.1-112, by omega⟩
    have he : (⟨352+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0352 j
  by_cases h : i.1 < 128
  · let j : Fin 8 := ⟨i.1-120, by omega⟩
    have he : (⟨360+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0360 j
  by_cases h : i.1 < 136
  · let j : Fin 8 := ⟨i.1-128, by omega⟩
    have he : (⟨368+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0368 j
  by_cases h : i.1 < 144
  · let j : Fin 8 := ⟨i.1-136, by omega⟩
    have he : (⟨376+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0376 j
  by_cases h : i.1 < 152
  · let j : Fin 8 := ⟨i.1-144, by omega⟩
    have he : (⟨384+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0384 j
  by_cases h : i.1 < 160
  · let j : Fin 8 := ⟨i.1-152, by omega⟩
    have he : (⟨392+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0392 j
  by_cases h : i.1 < 168
  · let j : Fin 8 := ⟨i.1-160, by omega⟩
    have he : (⟨400+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0400 j
  by_cases h : i.1 < 176
  · let j : Fin 8 := ⟨i.1-168, by omega⟩
    have he : (⟨408+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0408 j
  by_cases h : i.1 < 184
  · let j : Fin 8 := ⟨i.1-176, by omega⟩
    have he : (⟨416+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0416 j
  by_cases h : i.1 < 192
  · let j : Fin 8 := ⟨i.1-184, by omega⟩
    have he : (⟨424+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0424 j
  by_cases h : i.1 < 200
  · let j : Fin 8 := ⟨i.1-192, by omega⟩
    have he : (⟨432+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0432 j
  by_cases h : i.1 < 208
  · let j : Fin 8 := ⟨i.1-200, by omega⟩
    have he : (⟨440+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0440 j
  by_cases h : i.1 < 216
  · let j : Fin 8 := ⟨i.1-208, by omega⟩
    have he : (⟨448+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0448 j
  by_cases h : i.1 < 224
  · let j : Fin 8 := ⟨i.1-216, by omega⟩
    have he : (⟨456+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0456 j
  by_cases h : i.1 < 232
  · let j : Fin 8 := ⟨i.1-224, by omega⟩
    have he : (⟨464+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0464 j
  by_cases h : i.1 < 240
  · let j : Fin 8 := ⟨i.1-232, by omega⟩
    have he : (⟨472+j.1, by omega⟩ : Fin 720) = ⟨240+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0472 j
  omega
end Taeyoung.Methods.RootedSOS.Induced.Six
