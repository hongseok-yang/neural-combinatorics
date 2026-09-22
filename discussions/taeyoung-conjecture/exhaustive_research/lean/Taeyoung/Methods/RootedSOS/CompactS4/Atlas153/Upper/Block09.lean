import Taeyoung.Methods.RootedSOS.PackedMatrix
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Upper.Block09
set_option maxRecDepth 1000000
private def GData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (17338631061600))
(.leaf (-24109965652464)))
(.node 1 (.leaf (1478025781632))
(.leaf (2962206166176))))
(.node 2 (.node 1 (.leaf (771792078384))
(.leaf (6437726916480)))
(.node 1 (.leaf (-24109965652464))
(.node 1 (.leaf (63483139782288))
(.leaf (-7992123099696))))))
(.node 4 (.node 2 (.node 1 (.leaf (17596172379888))
(.leaf (-19094305812768)))
(.node 1 (.leaf (-2494241598960))
(.leaf (1478025781632))))
(.node 2 (.node 1 (.leaf (-7992123099696))
(.leaf (71589711496320)))
(.node 1 (.leaf (-15246846334800))
(.node 1 (.leaf (-12394490764176))
(.leaf (-2109919902336)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (2962206166176))
(.leaf (17596172379888)))
(.node 1 (.leaf (-15246846334800))
(.leaf (33808430253744))))
(.node 2 (.node 1 (.leaf (5366287716192))
(.leaf (-15833744289360)))
(.node 1 (.leaf (771792078384))
(.node 1 (.leaf (-19094305812768))
(.leaf (-12394490764176))))))
(.node 4 (.node 2 (.node 1 (.leaf (5366287716192))
(.leaf (31923839620800)))
(.node 1 (.leaf (-27553352106096))
(.leaf (6437726916480))))
(.node 2 (.node 1 (.leaf (-2494241598960))
(.leaf (-2109919902336)))
(.node 1 (.leaf (-15833744289360))
(.node 1 (.leaf (-27553352106096))
(.leaf (39021534308016))))))))

def G (i j : Nat) : Int := GData.get (i * 6 + j)

private def PData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (25936798))
(.leaf (27438065)))
(.node 1 (.leaf (2451816))
(.leaf (-31226200))))
(.node 2 (.node 1 (.leaf (164954891))
(.leaf (62422885)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (19732027))
(.leaf (2552935))))))
(.node 4 (.node 2 (.node 1 (.leaf (-18850247))
(.leaf (111438598)))
(.node 1 (.leaf (75230479))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (12882073)))
(.node 1 (.leaf (4330887))
(.node 1 (.leaf (5756868))
(.leaf (32000047)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.leaf (27189053))))
(.node 2 (.node 1 (.leaf (-83071335))
(.leaf (-8294144)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (0))))))
(.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (83253523)))
(.node 1 (.leaf (138043224))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (93543624))))))))

def P (i j : Nat) : Int := PData.get (i * 6 + j)

private def KData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (449708571441244756800))
(.leaf (-7144292460528)))
(.node 1 (.leaf (-6093179833104))
(.leaf (-10452850422480))))
(.node 2 (.node 1 (.leaf (14821639110576))
(.leaf (10934427122640)))
(.node 1 (.leaf (-625335308914896970272))
(.node 1 (.leaf (591120223508806295616))
(.leaf (16718663590848))))))
(.node 4 (.node 2 (.node 1 (.leaf (25624354187376))
(.leaf (-18604181453472)))
(.node 1 (.leaf (-34154607859344))
(.leaf (38335256136981294336))))
(.node 2 (.node 1 (.leaf (-117146621322430541712))
(.leaf (905444366018828907312)))
(.node 1 (.leaf (3594707957952))
(.node 1 (.leaf (-34663764612384))
(.leaf (37082824103088)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (76830142966461344448))
(.leaf (428485353827542162416)))
(.node 1 (.leaf (-144226318696497693504))
(.leaf (428996195631754453296))))
(.node 2 (.node 1 (.leaf (16048109993616))
(.leaf (-21752145824256)))
(.node 1 (.leaf (20017815235045974432))
(.node 1 (.leaf (-355592876630609833776))
(.leaf (-206520964265604745584))))))
(.node 4 (.node 2 (.node 1 (.leaf (428057389272781434960))
(.leaf (140102192890212918192)))
(.node 1 (.leaf (-10453906656))
(.leaf (166974022611904631040))))
(.node 2 (.node 1 (.leaf (127422327011425919280))
(.leaf (-17763657025029842448)))
(.node 1 (.leaf (-593651015369241460992))
(.node 1 (.leaf (-206750132560177678656))
(.leaf (124690492370958037488))))))))

def K (i j : Nat) : Int := KData.get (i * 6 + j)

private def BData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (11664000376340134125680726400))
(.leaf (-185300070401637709344)))
(.node 1 (.leaf (-158037574508892160992))
(.leaf (-271113469932078419040))))
(.node 2 (.node 1 (.leaf (384425859639909375648))
(.leaf (283604027525634906720)))
(.node 1 (.leaf (-185300070401637709344))
(.node 1 (.leaf (11664000014496239651887695312))
(.leaf (162708057061132985136))))))
(.node 4 (.node 2 (.node 1 (.leaf (218814459355582589952))
(.leaf (39578886569717727696)))
(.node 1 (.leaf (-373920122326228718688))
(.leaf (-158037574508892160992))))
(.node 2 (.node 1 (.leaf (162708057061132985136))
(.leaf (11664000448235578987123239792)))
(.node 1 (.leaf (86096135073924119376))
(.node 1 (.leaf (-457696480252930926336))
(.leaf (417318356696867481024)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-271113469932078419040))
(.leaf (218814459355582589952)))
(.node 1 (.leaf (86096135073924119376))
(.leaf (11664000158775806492464926240))))
(.node 2 (.node 1 (.leaf (174078014071519097424))
(.leaf (-128436538728280100544)))
(.node 1 (.leaf (384425859639909375648))
(.node 1 (.leaf (39578886569717727696))
(.leaf (-457696480252930926336))))))
(.node 4 (.node 2 (.node 1 (.leaf (174078014071519097424))
(.leaf (11663999977121104820385454704)))
(.node 1 (.leaf (17136010683540433584))
(.leaf (283604027525634906720))))
(.node 2 (.node 1 (.leaf (-373920122326228718688))
(.leaf (417318356696867481024)))
(.node 1 (.leaf (-128436538728280100544))
(.node 1 (.leaf (17136010683540433584))
(.leaf (11664000013439197669116750192))))))))

def B (i j : Nat) : Int := BData.get (i * 6 + j)

def Pt (i j : Nat) : Int := P j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Upper.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Upper.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (3567213588232399608796478347872222736348331317697494379250764293259626185161312147050804120008754244603132346398815077793295))
(.node 1 (.leaf (4299115411567923941502695373715876067105350577240851761544476926588617273445396625569016756852380239128704220738612975836912))
(.leaf (1828672328785755967611348575673114776627669164051025826548028195620045680709635773346816696002142551203447372384377444297235))))
(.node 1 (.leaf (-473976542089591466669686886833992707109928287931194994378391442341089308015503709112737706964351104009555895265446820551466))
(.node 1 (.leaf (7888607910643811212099497548906264593656389485576855379952890007341784642094182994863786257398186620596182287003102512414827))
(.leaf (5345637046818685384743089662689415952987057314626004026263606554167932914549610977836447027073418915695354882787562523700424)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 71589711496320 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 164954891 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 70854438339581475006720 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (141708876679162950013441 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 141708876679162950013441 70854438339581475006720 (List.ofFn fun j : Fin 6 => K i j) =
      70854438339581475006720 * geometricEncoding 141708876679162950013441 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    71589711496320 164954891 70854438339581475006720 141708876679162950013441 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (202226052321412924756253314112325009917101592616544983556558021423569571261465680927956302733967461974934918312488200641767093105933261293399881252555520864628485360))
(.node 1 (.leaf (-631670177002691620535083439238837569894168070721168971237750302232773959448062079118292582206554582625129658737457030466531192463385291244167464404144999066085242592))
(.leaf (685825882159818709630695196446843042033481040761628583414783533109029019486286867081422347452618745078618047830612589007131735095637695436196444547702149875622209776))))
(.node 1 (.leaf (-402293648329419044572769275132808524565530305955237610020119162869793363919755476005867736966297217555351945810309947338094632113467324124993376374195990756973950672))
(.node 1 (.leaf (-193339097756866077803250232428160095848920824322755906514823528676109360651050067336606641519172784199285049248564490118197474907563399372474393653398218568468448))
(.leaf (2306080213565321880100537102180299007352144994487547005540620720322093443818542622450658204011937160344402925465108620544412115009420749369861261150141706206508064464012240)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 164954891 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 905444366018828907312 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 896144860219200158119800377952 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (1792289720438400316239600755905 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 1792289720438400316239600755905 896144860219200158119800377952 (List.ofFn fun j : Fin 6 => B i j) =
      896144860219200158119800377952 * geometricEncoding 1792289720438400316239600755905 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    164954891 905444366018828907312 896144860219200158119800377952 1792289720438400316239600755905 (fun i => PKEnc.get i)
    PK_left_bound PK_right_bound PK_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    PK_encoded PK_product i j

private theorem upper : ∀ i j : Fin 6, j < i → P i j = 0 := by decide +kernel
private theorem diagonal : ∀ i : Fin 6, P i i ≠ 0 := by decide +kernel
private theorem symm : ∀ i j : Fin 6, B i j = B j i := by decide +kernel
private theorem dominant : ∀ i : Fin 6,
    (∑ j : Fin 6, if i = j then 0 else (B i j).natAbs : Nat) ≤ (B i i).toNat := by decide +kernel
private theorem positive : ∀ i : Fin 6, 0 ≤ B i i := by decide +kernel

theorem gram_nonneg (x : Fin 6 → Real) :
    0 ≤ matrixQuadratic (fun i j => (G i j : Real)) x :=
  matrixQuadratic_nonneg_of_integer_congruence
    (fun i j => G i j) (fun i j => P i j) (fun i j => K i j) (fun i j => B i j)
    upper diagonal GP_exact PK_exact symm dominant positive x

#print axioms gram_nonneg
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Upper.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Upper.Block09
set_option maxRecDepth 1000000
private def NData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (1))
(.leaf (0)))
(.node 1 (.leaf (0))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (1))
(.leaf (0))))))
(.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (1)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (0)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.leaf (1))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (0))))))
(.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (1)))
(.node 1 (.leaf (0))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (1))))))))

def N (i j : Nat) : Int := NData.get (i * 6 + j)

private def NGData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (17338631061600))
(.leaf (-24109965652464)))
(.node 1 (.leaf (1478025781632))
(.leaf (2962206166176))))
(.node 2 (.node 1 (.leaf (771792078384))
(.leaf (6437726916480)))
(.node 1 (.leaf (-24109965652464))
(.node 1 (.leaf (63483139782288))
(.leaf (-7992123099696))))))
(.node 4 (.node 2 (.node 1 (.leaf (17596172379888))
(.leaf (-19094305812768)))
(.node 1 (.leaf (-2494241598960))
(.leaf (1478025781632))))
(.node 2 (.node 1 (.leaf (-7992123099696))
(.leaf (71589711496320)))
(.node 1 (.leaf (-15246846334800))
(.node 1 (.leaf (-12394490764176))
(.leaf (-2109919902336)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (2962206166176))
(.leaf (17596172379888)))
(.node 1 (.leaf (-15246846334800))
(.leaf (33808430253744))))
(.node 2 (.node 1 (.leaf (5366287716192))
(.leaf (-15833744289360)))
(.node 1 (.leaf (771792078384))
(.node 1 (.leaf (-19094305812768))
(.leaf (-12394490764176))))))
(.node 4 (.node 2 (.node 1 (.leaf (5366287716192))
(.leaf (31923839620800)))
(.node 1 (.leaf (-27553352106096))
(.leaf (6437726916480))))
(.node 2 (.node 1 (.leaf (-2494241598960))
(.leaf (-2109919902336)))
(.node 1 (.leaf (-15833744289360))
(.node 1 (.leaf (-27553352106096))
(.leaf (39021534308016))))))))

def NG (i j : Nat) : Int := NGData.get (i * 6 + j)

private def HData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (17338631061600))
(.leaf (-24109965652464)))
(.node 1 (.leaf (1478025781632))
(.leaf (2962206166176))))
(.node 2 (.node 1 (.leaf (771792078384))
(.leaf (6437726916480)))
(.node 1 (.leaf (-24109965652464))
(.node 1 (.leaf (63483139782288))
(.leaf (-7992123099696))))))
(.node 4 (.node 2 (.node 1 (.leaf (17596172379888))
(.leaf (-19094305812768)))
(.node 1 (.leaf (-2494241598960))
(.leaf (1478025781632))))
(.node 2 (.node 1 (.leaf (-7992123099696))
(.leaf (71589711496320)))
(.node 1 (.leaf (-15246846334800))
(.node 1 (.leaf (-12394490764176))
(.leaf (-2109919902336)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (2962206166176))
(.leaf (17596172379888)))
(.node 1 (.leaf (-15246846334800))
(.leaf (33808430253744))))
(.node 2 (.node 1 (.leaf (5366287716192))
(.leaf (-15833744289360)))
(.node 1 (.leaf (771792078384))
(.node 1 (.leaf (-19094305812768))
(.leaf (-12394490764176))))))
(.node 4 (.node 2 (.node 1 (.leaf (5366287716192))
(.leaf (31923839620800)))
(.node 1 (.leaf (-27553352106096))
(.leaf (6437726916480))))
(.node 2 (.node 1 (.leaf (-2494241598960))
(.leaf (-2109919902336)))
(.node 1 (.leaf (-15833744289360))
(.node 1 (.leaf (-27553352106096))
(.leaf (39021534308016))))))))

def H (i j : Nat) : Int := HData.get (i * 6 + j)

def Nt (i j : Nat) : Int := N j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Upper.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Upper.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (3012255747436514507377663799339021137002334628517908918202167468972512064155392646459968))
(.node 1 (.leaf (-1167072429358445468336903323223351936668727197100934017094871520948035195211165733903792))
(.leaf (-987245721183441077567203944589128800672841910633362357237660884002393854746796101882256))))
(.node 1 (.leaf (-7408715507482787597709347133636146302760678570196106627097446892522087997141307984419840))
(.node 1 (.leaf (-12892398873003266216208368977262992489377700110037398974218294982383330640456768323567824))
(.leaf (18258438501361893819232019934307843545870853669951812864937124665608636278119633681039104)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 71589711496320 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 429538268977920 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (859076537955841 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 859076537955841 429538268977920 (List.ofFn fun j : Fin 6 => NG i j) =
      429538268977920 * geometricEncoding 859076537955841 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 71589711496320 429538268977920 859076537955841 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (859076537955841))
(.leaf (738012498066193522318866017281))))
(.node 1 (.leaf (634009221806847332089612110459530848720888321))
(.node 1 (.leaf (544662447301903297520311706278702169437560044340646990632961))
(.leaf (467906729582674776634128617595580878215947280959096295395043934109657075201)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 71589711496320 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 429538268977920 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (859076537955841 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 859076537955841 429538268977920 (List.ofFn fun j : Fin 6 => H i j) =
      429538268977920 * geometricEncoding 859076537955841 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    71589711496320 1 429538268977920 859076537955841 (fun i => FullProductEnc.get i)
    FullProduct_left_bound FullProduct_right_bound FullProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    FullProduct_encoded FullProduct_product i j

theorem expanded_entries_exact (i j : Fin 6) :
    H i j = ∑ k : Fin 6, (∑ l : Fin 6, N i l * G l k) * N j k := by
  rw [FullProduct_exact]
  apply Finset.sum_congr rfl
  intro k _
  rw [NGProduct_exact]
  rfl

#print axioms expanded_entries_exact
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Upper.Block09
