import Taeyoung.Methods.RootedSOS.Induced.Six.Base
namespace Taeyoung.Methods.RootedSOS.Induced.Six
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_0480 : ∀ i : Fin 8,
    permutationCheck ⟨480+i.1, by omega⟩ := by decide +kernel
private theorem check_0488 : ∀ i : Fin 8,
    permutationCheck ⟨488+i.1, by omega⟩ := by decide +kernel
private theorem check_0496 : ∀ i : Fin 8,
    permutationCheck ⟨496+i.1, by omega⟩ := by decide +kernel
private theorem check_0504 : ∀ i : Fin 8,
    permutationCheck ⟨504+i.1, by omega⟩ := by decide +kernel
private theorem check_0512 : ∀ i : Fin 8,
    permutationCheck ⟨512+i.1, by omega⟩ := by decide +kernel
private theorem check_0520 : ∀ i : Fin 8,
    permutationCheck ⟨520+i.1, by omega⟩ := by decide +kernel
private theorem check_0528 : ∀ i : Fin 8,
    permutationCheck ⟨528+i.1, by omega⟩ := by decide +kernel
private theorem check_0536 : ∀ i : Fin 8,
    permutationCheck ⟨536+i.1, by omega⟩ := by decide +kernel
private theorem check_0544 : ∀ i : Fin 8,
    permutationCheck ⟨544+i.1, by omega⟩ := by decide +kernel
private theorem check_0552 : ∀ i : Fin 8,
    permutationCheck ⟨552+i.1, by omega⟩ := by decide +kernel
private theorem check_0560 : ∀ i : Fin 8,
    permutationCheck ⟨560+i.1, by omega⟩ := by decide +kernel
private theorem check_0568 : ∀ i : Fin 8,
    permutationCheck ⟨568+i.1, by omega⟩ := by decide +kernel
private theorem check_0576 : ∀ i : Fin 8,
    permutationCheck ⟨576+i.1, by omega⟩ := by decide +kernel
private theorem check_0584 : ∀ i : Fin 8,
    permutationCheck ⟨584+i.1, by omega⟩ := by decide +kernel
private theorem check_0592 : ∀ i : Fin 8,
    permutationCheck ⟨592+i.1, by omega⟩ := by decide +kernel
private theorem check_0600 : ∀ i : Fin 8,
    permutationCheck ⟨600+i.1, by omega⟩ := by decide +kernel
private theorem check_0608 : ∀ i : Fin 8,
    permutationCheck ⟨608+i.1, by omega⟩ := by decide +kernel
private theorem check_0616 : ∀ i : Fin 8,
    permutationCheck ⟨616+i.1, by omega⟩ := by decide +kernel
private theorem check_0624 : ∀ i : Fin 8,
    permutationCheck ⟨624+i.1, by omega⟩ := by decide +kernel
private theorem check_0632 : ∀ i : Fin 8,
    permutationCheck ⟨632+i.1, by omega⟩ := by decide +kernel
private theorem check_0640 : ∀ i : Fin 8,
    permutationCheck ⟨640+i.1, by omega⟩ := by decide +kernel
private theorem check_0648 : ∀ i : Fin 8,
    permutationCheck ⟨648+i.1, by omega⟩ := by decide +kernel
private theorem check_0656 : ∀ i : Fin 8,
    permutationCheck ⟨656+i.1, by omega⟩ := by decide +kernel
private theorem check_0664 : ∀ i : Fin 8,
    permutationCheck ⟨664+i.1, by omega⟩ := by decide +kernel
private theorem check_0672 : ∀ i : Fin 8,
    permutationCheck ⟨672+i.1, by omega⟩ := by decide +kernel
private theorem check_0680 : ∀ i : Fin 8,
    permutationCheck ⟨680+i.1, by omega⟩ := by decide +kernel
private theorem check_0688 : ∀ i : Fin 8,
    permutationCheck ⟨688+i.1, by omega⟩ := by decide +kernel
private theorem check_0696 : ∀ i : Fin 8,
    permutationCheck ⟨696+i.1, by omega⟩ := by decide +kernel
private theorem check_0704 : ∀ i : Fin 8,
    permutationCheck ⟨704+i.1, by omega⟩ := by decide +kernel
private theorem check_0712 : ∀ i : Fin 8,
    permutationCheck ⟨712+i.1, by omega⟩ := by decide +kernel
theorem PermutationChecks_0480 (i : Fin 240) : permutationCheck ⟨480+i.1, by omega⟩ := by
  by_cases h : i.1 < 8
  · let j : Fin 8 := ⟨i.1-0, by omega⟩
    have he : (⟨480+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0480 j
  by_cases h : i.1 < 16
  · let j : Fin 8 := ⟨i.1-8, by omega⟩
    have he : (⟨488+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0488 j
  by_cases h : i.1 < 24
  · let j : Fin 8 := ⟨i.1-16, by omega⟩
    have he : (⟨496+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0496 j
  by_cases h : i.1 < 32
  · let j : Fin 8 := ⟨i.1-24, by omega⟩
    have he : (⟨504+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0504 j
  by_cases h : i.1 < 40
  · let j : Fin 8 := ⟨i.1-32, by omega⟩
    have he : (⟨512+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0512 j
  by_cases h : i.1 < 48
  · let j : Fin 8 := ⟨i.1-40, by omega⟩
    have he : (⟨520+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0520 j
  by_cases h : i.1 < 56
  · let j : Fin 8 := ⟨i.1-48, by omega⟩
    have he : (⟨528+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0528 j
  by_cases h : i.1 < 64
  · let j : Fin 8 := ⟨i.1-56, by omega⟩
    have he : (⟨536+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0536 j
  by_cases h : i.1 < 72
  · let j : Fin 8 := ⟨i.1-64, by omega⟩
    have he : (⟨544+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0544 j
  by_cases h : i.1 < 80
  · let j : Fin 8 := ⟨i.1-72, by omega⟩
    have he : (⟨552+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0552 j
  by_cases h : i.1 < 88
  · let j : Fin 8 := ⟨i.1-80, by omega⟩
    have he : (⟨560+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0560 j
  by_cases h : i.1 < 96
  · let j : Fin 8 := ⟨i.1-88, by omega⟩
    have he : (⟨568+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0568 j
  by_cases h : i.1 < 104
  · let j : Fin 8 := ⟨i.1-96, by omega⟩
    have he : (⟨576+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0576 j
  by_cases h : i.1 < 112
  · let j : Fin 8 := ⟨i.1-104, by omega⟩
    have he : (⟨584+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0584 j
  by_cases h : i.1 < 120
  · let j : Fin 8 := ⟨i.1-112, by omega⟩
    have he : (⟨592+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0592 j
  by_cases h : i.1 < 128
  · let j : Fin 8 := ⟨i.1-120, by omega⟩
    have he : (⟨600+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0600 j
  by_cases h : i.1 < 136
  · let j : Fin 8 := ⟨i.1-128, by omega⟩
    have he : (⟨608+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0608 j
  by_cases h : i.1 < 144
  · let j : Fin 8 := ⟨i.1-136, by omega⟩
    have he : (⟨616+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0616 j
  by_cases h : i.1 < 152
  · let j : Fin 8 := ⟨i.1-144, by omega⟩
    have he : (⟨624+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0624 j
  by_cases h : i.1 < 160
  · let j : Fin 8 := ⟨i.1-152, by omega⟩
    have he : (⟨632+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0632 j
  by_cases h : i.1 < 168
  · let j : Fin 8 := ⟨i.1-160, by omega⟩
    have he : (⟨640+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0640 j
  by_cases h : i.1 < 176
  · let j : Fin 8 := ⟨i.1-168, by omega⟩
    have he : (⟨648+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0648 j
  by_cases h : i.1 < 184
  · let j : Fin 8 := ⟨i.1-176, by omega⟩
    have he : (⟨656+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0656 j
  by_cases h : i.1 < 192
  · let j : Fin 8 := ⟨i.1-184, by omega⟩
    have he : (⟨664+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0664 j
  by_cases h : i.1 < 200
  · let j : Fin 8 := ⟨i.1-192, by omega⟩
    have he : (⟨672+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0672 j
  by_cases h : i.1 < 208
  · let j : Fin 8 := ⟨i.1-200, by omega⟩
    have he : (⟨680+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0680 j
  by_cases h : i.1 < 216
  · let j : Fin 8 := ⟨i.1-208, by omega⟩
    have he : (⟨688+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0688 j
  by_cases h : i.1 < 224
  · let j : Fin 8 := ⟨i.1-216, by omega⟩
    have he : (⟨696+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0696 j
  by_cases h : i.1 < 232
  · let j : Fin 8 := ⟨i.1-224, by omega⟩
    have he : (⟨704+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0704 j
  by_cases h : i.1 < 240
  · let j : Fin 8 := ⟨i.1-232, by omega⟩
    have he : (⟨712+j.1, by omega⟩ : Fin 720) = ⟨480+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0712 j
  omega
end Taeyoung.Methods.RootedSOS.Induced.Six
