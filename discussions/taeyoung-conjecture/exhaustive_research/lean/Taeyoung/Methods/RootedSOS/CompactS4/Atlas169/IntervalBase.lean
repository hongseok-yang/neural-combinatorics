import Taeyoung.Methods.RootedSOS.CompactS4.Atlas169.GroupData
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas169.Coloring
import Taeyoung.Methods.RootedSOS.CompactS4.Groups
import Taeyoung.Methods.RootedSOS.ThirdIntervalCoefficients

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas169
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def representativeData : PackedTable := (.node 71 (.node 35 (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (4))
(.leaf (4)))
(.node 1 (.leaf (6))
(.leaf (6)))))
(.node 4 (.node 2 (.node 1 (.leaf (8))
(.leaf (8)))
(.node 1 (.leaf (10))
(.leaf (10))))
(.node 2 (.node 1 (.leaf (12))
(.leaf (12)))
(.node 1 (.leaf (14))
(.node 1 (.leaf (14))
(.leaf (16)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (16))
(.leaf (18)))
(.node 1 (.leaf (18))
(.leaf (20))))
(.node 2 (.node 1 (.leaf (21))
(.leaf (22)))
(.node 1 (.leaf (23))
(.node 1 (.leaf (24))
(.leaf (25))))))
(.node 4 (.node 2 (.node 1 (.leaf (26))
(.leaf (27)))
(.node 1 (.leaf (28))
(.leaf (29))))
(.node 2 (.node 1 (.leaf (30))
(.leaf (31)))
(.node 1 (.leaf (32))
(.node 1 (.leaf (33))
(.leaf (34))))))))
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (35))
(.leaf (36)))
(.node 1 (.leaf (37))
(.leaf (38))))
(.node 2 (.node 1 (.leaf (39))
(.leaf (40)))
(.node 1 (.leaf (41))
(.node 1 (.leaf (42))
(.leaf (43))))))
(.node 4 (.node 2 (.node 1 (.leaf (44))
(.leaf (45)))
(.node 1 (.leaf (46))
(.leaf (47))))
(.node 2 (.node 1 (.leaf (48))
(.leaf (49)))
(.node 1 (.leaf (50))
(.node 1 (.leaf (51))
(.leaf (52)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (53))
(.leaf (54)))
(.node 1 (.leaf (55))
(.leaf (56))))
(.node 2 (.node 1 (.leaf (57))
(.leaf (58)))
(.node 1 (.leaf (59))
(.node 1 (.leaf (60))
(.leaf (61))))))
(.node 4 (.node 2 (.node 1 (.leaf (62))
(.leaf (63)))
(.node 1 (.leaf (64))
(.leaf (65))))
(.node 2 (.node 1 (.leaf (66))
(.leaf (67)))
(.node 1 (.leaf (68))
(.node 1 (.leaf (69))
(.leaf (70)))))))))
(.node 36 (.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (71))
(.leaf (72)))
(.node 1 (.leaf (73))
(.leaf (74))))
(.node 2 (.node 1 (.leaf (75))
(.leaf (76)))
(.node 1 (.leaf (77))
(.node 1 (.leaf (78))
(.leaf (79))))))
(.node 4 (.node 2 (.node 1 (.leaf (80))
(.leaf (81)))
(.node 1 (.leaf (82))
(.leaf (83))))
(.node 2 (.node 1 (.leaf (84))
(.leaf (85)))
(.node 1 (.leaf (86))
(.node 1 (.leaf (87))
(.leaf (88)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (89))
(.leaf (90)))
(.node 1 (.leaf (91))
(.leaf (92))))
(.node 2 (.node 1 (.leaf (93))
(.leaf (94)))
(.node 1 (.leaf (95))
(.node 1 (.leaf (96))
(.leaf (97))))))
(.node 4 (.node 2 (.node 1 (.leaf (98))
(.leaf (99)))
(.node 1 (.leaf (100))
(.leaf (101))))
(.node 2 (.node 1 (.leaf (102))
(.leaf (103)))
(.node 1 (.leaf (104))
(.node 1 (.leaf (105))
(.leaf (106))))))))
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (107))
(.leaf (108)))
(.node 1 (.leaf (109))
(.leaf (110))))
(.node 2 (.node 1 (.leaf (111))
(.leaf (112)))
(.node 1 (.leaf (113))
(.node 1 (.leaf (114))
(.leaf (115))))))
(.node 4 (.node 2 (.node 1 (.leaf (116))
(.leaf (117)))
(.node 1 (.leaf (118))
(.leaf (119))))
(.node 2 (.node 1 (.leaf (120))
(.leaf (121)))
(.node 1 (.leaf (122))
(.node 1 (.leaf (123))
(.leaf (124)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (125))
(.leaf (126)))
(.node 1 (.leaf (127))
(.leaf (128))))
(.node 2 (.node 1 (.leaf (129))
(.leaf (130)))
(.node 1 (.leaf (131))
(.node 1 (.leaf (132))
(.leaf (133))))))
(.node 4 (.node 2 (.node 1 (.leaf (134))
(.leaf (135)))
(.node 1 (.leaf (136))
(.leaf (137))))
(.node 2 (.node 1 (.leaf (138))
(.leaf (139)))
(.node 1 (.leaf (140))
(.node 1 (.leaf (141))
(.leaf (142))))))))))
def representative (g : Fin 143) : Fin 143 :=
  ⟨(representativeData.get g).toNat % 143, Nat.mod_lt _ (by decide)⟩

theorem isolated_bound : ∀ g : Fin 143, (S4Classification.groupKey g).2 ≤ 3 := by decide +kernel

private theorem core_codes : ∀ g : Fin 143,
    adjacencyCode (S4Classification.coreGraph6 g) =
      adjacencyCode (S4Classification.coreGraph6 (representative g)) := by decide +kernel

theorem core_eq (g : Fin 143) : S4Classification.coreGraph6 g =
    S4Classification.coreGraph6 (representative g) := (adjacencyCode_eq_iff _ _).mp (core_codes g)

theorem target_core : S4Classification.coreGraph6 115 = graph169 :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)

theorem empty_core : S4Classification.coreGraph6 0 = (⊥ : SimpleGraph (Fin 6)) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)

def polynomialCoefficient (g : Fin 143) (j : Fin 6) : Int :=
  thirdIntervalCoefficient (S4Classification.groupKey g).2
    (groupTotal g 0) (groupTotal g 1 + groupTotal g 3)
    (groupTotal g 2 - groupTotal g 3) j

def targetCoefficient (r : Fin 143) (j : Fin 6) : Int :=
  (if r = 115 then (if j = 0 then 81*1296000000000000 else 0) else 0) -
  (if r = 0 then 1296000000000000 *
    (if j = 0 then (0) else if j = 1 then (6) else if j = 2 then (21) else if j = 3 then (27) else if j = 4 then (21) else (6)) else 0)

def polynomialCheck (r : Fin 143) : Prop := ∀ j : Fin 6,
  (∑ g : Fin 143, if representative g = r then polynomialCoefficient g j else 0) =
    targetCoefficient r j

instance (r : Fin 143) : Decidable (polynomialCheck r) := by unfold polynomialCheck; infer_instance

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas169
