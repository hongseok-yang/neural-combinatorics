import Taeyoung.Methods.RootedSOS.Induced.Six.Data
import Taeyoung.Methods.RootedSOS.Induced.Relabeling
namespace Taeyoung.Methods.RootedSOS.Induced.Six
def bits (code : Fin 32768) : Fin 15 → Fin 2 := finFunctionFinEquiv.symm code
def permutationCheck (p : Fin 720) : Prop :=
  (∀ i : Fin 6, vertex (inverse p) (vertex p i) = i ∧ vertex p (vertex (inverse p) i) = i) ∧
  (∀ i : Fin 15, edge (inverse p) (edge p i) = i ∧ edge p (edge (inverse p) i) = i) ∧
  (∀ i : Fin 15,
    (vertex p (pairs i).1 = (pairs (edge p i)).1 ∧ vertex p (pairs i).2 = (pairs (edge p i)).2) ∨
    (vertex p (pairs i).1 = (pairs (edge p i)).2 ∧ vertex p (pairs i).2 = (pairs (edge p i)).1))
instance (p : Fin 720) : Decidable (permutationCheck p) := by unfold permutationCheck; infer_instance
def classificationCheck (code : Fin 32768) : Prop :=
  ∀ i : Fin 15, bits code i = bits (hostCode (host code)) (edge (permutation code) i)
instance (code : Fin 32768) : Decidable (classificationCheck code) := by
  unfold classificationCheck; infer_instance
end Taeyoung.Methods.RootedSOS.Induced.Six
