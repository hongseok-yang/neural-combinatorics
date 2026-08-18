import OddCycleBound.RegionII.Certificate.Bernstein

/-!
# Staged degree-eight Bernstein tensors

The C13 quadratic certificates have degree eight in three variables.  Expanding
729 Bernstein basis products in a single `ring` call is needlessly expensive.
This module proves once that three checked one-dimensional coefficient
transforms carry a power-basis cube to its Bernstein cube.
-/

namespace OddCycleBound.RegionII.Certificate

open scoped BigOperators

def ratBernsteinRatio (degree power index : Nat) : ℚ :=
  Nat.choose index power / Nat.choose degree power

structure RationalDatum where
  numerator : Int
  denominator : Nat
deriving DecidableEq, Inhabited

def RationalDatum.value (datum : RationalDatum) : ℚ :=
  datum.numerator / datum.denominator

def cubeIndex (i j k : Fin 9) : Nat := i * 81 + j * 9 + k

def cubeCoefficient (values : Fin 9 → Fin 9 → Fin 9 → RationalDatum)
    (i j k : Fin 9) : ℚ :=
  (values i j k).value

structure BernsteinCube8Data where
  power : Fin 9 → Fin 9 → Fin 9 → RationalDatum
  stageTwo : Fin 9 → Fin 9 → Fin 9 → RationalDatum
  stageOne : Fin 9 → Fin 9 → Fin 9 → RationalDatum
  bernstein : Fin 9 → Fin 9 → Fin 9 → RationalDatum

def cubeEval (coefficient : Fin 9 → Fin 9 → Fin 9 → ℝ)
    (f g h : Fin 9 → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, coefficient i j k * f i * g j * h k

def powerFamily (x : ℝ) (i : Fin 9) : ℝ := x ^ (i : Nat)

def bernsteinFamily8 (x : ℝ) (i : Fin 9) : ℝ :=
  bernsteinBasis 8 i x

lemma powerSum_eq_bernsteinSum_eight
    (powerCoefficient bernsteinCoefficient : Fin 9 → ℝ)
    (htransform : ∀ index,
      bernsteinCoefficient index =
        ∑ power : Fin 9, powerCoefficient power * bernsteinRatio 8 power index)
    (x : ℝ) :
    (∑ power : Fin 9, powerCoefficient power * powerFamily x power) =
      ∑ index : Fin 9, bernsteinCoefficient index * bernsteinFamily8 x index := by
  calc
    (∑ power : Fin 9, powerCoefficient power * powerFamily x power) =
        ∑ power : Fin 9, powerCoefficient power *
          (∑ index : Fin 9, bernsteinRatio 8 power index * bernsteinBasis 8 index x) := by
            refine Finset.sum_congr rfl fun power _ => ?_
            change powerCoefficient power * x ^ (power : Nat) = _
            rw [monomial_eq_bernstein_sum_eight]
    _ = ∑ power : Fin 9, ∑ index : Fin 9,
          powerCoefficient power * bernsteinRatio 8 power index *
            bernsteinBasis 8 index x := by
            refine Finset.sum_congr rfl fun power _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun index _ => by ring
    _ = ∑ index : Fin 9, ∑ power : Fin 9,
          powerCoefficient power * bernsteinRatio 8 power index *
            bernsteinBasis 8 index x := Finset.sum_comm
    _ = ∑ index : Fin 9, bernsteinCoefficient index * bernsteinFamily8 x index := by
            refine Finset.sum_congr rfl fun index _ => ?_
            rw [htransform index, Finset.sum_mul]
            rfl

lemma cubeEval_transform_third
    (source target : Fin 9 → Fin 9 → Fin 9 → ℝ)
    (htransform : ∀ i j index,
      target i j index =
        ∑ power : Fin 9, source i j power * bernsteinRatio 8 power index)
    (f g : Fin 9 → ℝ) (x : ℝ) :
    cubeEval source f g (powerFamily x) =
      cubeEval target f g (bernsteinFamily8 x) := by
  unfold cubeEval
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  calc
    (∑ k, source i j k * f i * g j * powerFamily x k) =
        f i * g j * ∑ k, source i j k * powerFamily x k := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => by ring
    _ = f i * g j * ∑ k, target i j k * bernsteinFamily8 x k := by
          rw [powerSum_eq_bernsteinSum_eight _ _ (htransform i j) x]
    _ = ∑ k, target i j k * f i * g j * bernsteinFamily8 x k := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => by ring

set_option maxRecDepth 4000 in
lemma cubeEval_transform_second
    (source target : Fin 9 → Fin 9 → Fin 9 → ℝ)
    (htransform : ∀ i index k,
      target i index k =
        ∑ power : Fin 9, source i power k * bernsteinRatio 8 power index)
    (f h : Fin 9 → ℝ) (x : ℝ) :
    cubeEval source f (powerFamily x) h =
      cubeEval target f (bernsteinFamily8 x) h := by
  have transformed := cubeEval_transform_third
    (fun i k j => source i j k) (fun i k j => target i j k)
    (fun i k index => htransform i index k) f h x
  calc
    cubeEval source f (powerFamily x) h =
        cubeEval (fun i k j => source i j k) f h (powerFamily x) := by
          unfold cubeEval
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ =>
            Finset.sum_congr rfl fun j _ => by ring
    _ = cubeEval (fun i k j => target i j k) f h (bernsteinFamily8 x) := transformed
    _ = cubeEval target f (bernsteinFamily8 x) h := by
          unfold cubeEval
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ =>
            Finset.sum_congr rfl fun k _ => by ring

set_option maxRecDepth 4000 in
lemma cubeEval_transform_first
    (source target : Fin 9 → Fin 9 → Fin 9 → ℝ)
    (htransform : ∀ index j k,
      target index j k =
        ∑ power : Fin 9, source power j k * bernsteinRatio 8 power index)
    (g h : Fin 9 → ℝ) (x : ℝ) :
    cubeEval source (powerFamily x) g h =
      cubeEval target (bernsteinFamily8 x) g h := by
  have transformed := cubeEval_transform_third
    (fun j k i => source i j k) (fun j k i => target i j k)
    (fun j k index => htransform index j k) g h x
  calc
    cubeEval source (powerFamily x) g h =
        cubeEval (fun j k i => source i j k) g h (powerFamily x) := by
          unfold cubeEval
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ =>
            Finset.sum_congr rfl fun i _ => by ring
    _ = cubeEval (fun j k i => target i j k) g h (bernsteinFamily8 x) := transformed
    _ = cubeEval target (bernsteinFamily8 x) g h := by
          symm
          unfold cubeEval
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ =>
            Finset.sum_congr rfl fun i _ => by ring

theorem bernsteinCube8_staged_sound
    (power stageTwo stageOne bernstein : Fin 9 → Fin 9 → Fin 9 → ℝ)
    (hTwo : ∀ i j index,
      stageTwo i j index =
        ∑ powerIndex : Fin 9, power i j powerIndex * bernsteinRatio 8 powerIndex index)
    (hOne : ∀ i index k,
      stageOne i index k =
        ∑ powerIndex : Fin 9, stageTwo i powerIndex k * bernsteinRatio 8 powerIndex index)
    (hZero : ∀ index j k,
      bernstein index j k =
        ∑ powerIndex : Fin 9, stageOne powerIndex j k * bernsteinRatio 8 powerIndex index)
    (point : Fin 3 → ℝ) :
    cubeEval power (powerFamily (point 0)) (powerFamily (point 1))
        (powerFamily (point 2)) =
      cubeEval bernstein (bernsteinFamily8 (point 0))
        (bernsteinFamily8 (point 1)) (bernsteinFamily8 (point 2)) := by
  rw [cubeEval_transform_third power stageTwo hTwo]
  rw [cubeEval_transform_second stageTwo stageOne hOne]
  rw [cubeEval_transform_first stageOne bernstein hZero]

lemma cubeEval_bernstein_nonneg
    {coefficient : Fin 9 → Fin 9 → Fin 9 → ℝ}
    (hcoefficient : ∀ i j k, 0 ≤ coefficient i j k)
    {point : Fin 3 → ℝ} (hpoint : ∀ i, 0 ≤ point i ∧ point i ≤ 1) :
    0 ≤ cubeEval coefficient (bernsteinFamily8 (point 0))
      (bernsteinFamily8 (point 1)) (bernsteinFamily8 (point 2)) := by
  unfold cubeEval
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun k _ =>
      mul_nonneg (mul_nonneg (mul_nonneg (hcoefficient i j k)
        (bernsteinBasis_nonneg (hpoint 0).1 (hpoint 0).2))
        (bernsteinBasis_nonneg (hpoint 1).1 (hpoint 1).2))
        (bernsteinBasis_nonneg (hpoint 2).1 (hpoint 2).2)

end OddCycleBound.RegionII.Certificate
