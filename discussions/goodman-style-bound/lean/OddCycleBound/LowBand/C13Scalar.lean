import OddCycleBound.Kernel

/-!
# C13 near-bipartite scalar arithmetic

This file contains the scalar comparison for the rational near-bipartite
`C13` triangle/spectral interval `1 / 2 < p <= 51 / 100`.  The endpoint
estimates themselves are the exact Sturm-certified inequalities recorded in
`c13_near_bipartite_checker.py`; this module proves the final real-variable
step once those estimates are available.
-/

open MeasureTheory

namespace OddCycleBound
namespace LowBand
namespace C13

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
variable {W : Omega -> Omega -> Real}

/-- The final scalar comparison for the C13 rational near-bipartite interval.

Here `B` abbreviates `p^3 - alpha_0^3`, `Delta` abbreviates
`p*q - alpha_0^2`, and `theta` is the Razborov/Reiher triangle-density lower
bound.  The two endpoint estimates are the rational bounds checked in
`c13_near_bipartite_checker.py`.
-/
lemma scalar_final {eps theta B Delta : Real}
    (heps0 : 0 <= eps)
    (htheta :
      (3 / 2) * ((97 / 98) ^ 2) * (eps + (3 / 2) * eps ^ 2) <= theta)
    (hB : B <= (7 / 5) * eps)
    (hDelta0 : 0 <= Delta)
    (hDelta : Delta <= (11 / 13) * eps) :
    B + Real.sqrt Delta * Delta <= theta := by
  let t := Real.sqrt eps
  let a : Real := (3 / 2) * ((97 / 98) ^ 2)
  let b : Real := (132 / 169)
  have ht0 : 0 <= t := Real.sqrt_nonneg eps
  have ht2 : t ^ 2 = eps := by
    dsimp [t]
    exact Real.sq_sqrt heps0
  have hsqrtDelta : Real.sqrt Delta <= (12 / 13) * t := by
    have hright0 : 0 <= (12 / 13) * t := by
      exact mul_nonneg (by norm_num) ht0
    rw [Real.sqrt_le_left hright0]
    calc
      Delta <= (11 / 13) * eps := hDelta
      _ <= ((12 / 13) * t) ^ 2 := by
        rw [mul_pow, ht2]
        nlinarith [heps0]
  have hDelta' : Delta <= (11 / 13) * eps := hDelta
  have hrootTerm :
      Real.sqrt Delta * Delta <= b * t * eps := by
    calc
      Real.sqrt Delta * Delta <= ((12 / 13) * t) * ((11 / 13) * eps) := by
        exact mul_le_mul hsqrtDelta hDelta' hDelta0
          (mul_nonneg (by norm_num) ht0)
      _ = b * t * eps := by
        dsimp [b]
        ring
  have hyoung : b * t <= (3 * a / 2) * t ^ 2 + b ^ 2 / (6 * a) := by
    have hsq : 0 <= (3 * a * t - b) ^ 2 := sq_nonneg _
    have ha : 0 < a := by
      dsimp [a]
      norm_num
    have hden : 0 < 6 * a := by nlinarith
    have hmul :
        (6 * a) * (b * t) <=
          (6 * a) * ((3 * a / 2) * t ^ 2 + b ^ 2 / (6 * a)) := by
      field_simp [ne_of_gt hden]
      nlinarith [hsq]
    nlinarith [hmul, hden]
  have hmargin : (7 / 5) + b ^ 2 / (6 * a) <= a := by
    dsimp [a, b]
    norm_num
  have hquad :
      (7 / 5) * eps + b * t * eps <=
        a * (eps + (3 / 2) * eps ^ 2) := by
    have hyoung_mul := mul_le_mul_of_nonneg_right hyoung heps0
    rw [ht2] at hyoung_mul
    nlinarith [hmargin]
  nlinarith


private lemma razborov_parameter_le_one_ninetyeight
    {c eps : Real}
    (_hc0 : 0 <= c) (hc13 : c <= 1 / 3)
    (heps : eps = c - (3 / 2) * c ^ 2) (hepsle : eps <= 1 / 100) :
    c <= 1 / 98 := by
  by_contra h
  have hcge : 1 / 98 <= c := by linarith
  have hdif : 0 <= c - 1 / 98 := by linarith
  have hfactor : 0 <= 1 - (3 / 2) * (c + 1 / 98) := by nlinarith
  have hmono :
      (1 / 98 : Real) - (3 / 2) * (1 / 98) ^ 2 <=
        c - (3 / 2) * c ^ 2 := by
    have hm := mul_nonneg hdif hfactor
    nlinarith
  rw [heps] at hepsle
  norm_num at hmono
  linarith

private lemma eps_plus_quadratic_le_c
    {c eps : Real}
    (hc0 : 0 <= c) (hc13 : c <= 1 / 3)
    (heps : eps = c - (3 / 2) * c ^ 2) :
    eps + (3 / 2) * eps ^ 2 <= c := by
  rw [heps]
  nlinarith [mul_nonneg hc0 (by linarith : 0 <= 1 - (3 / 2) * c)]

/-- In the rational C13 near-bipartite band, the Razborov parameterized
triangle lower bound dominates the quadratic epsilon slack used by the
endpoint scalar proof. -/
lemma theta_quadratic_lower_of_razborov
    {c eps theta : Real}
    (hc0 : 0 <= c) (hc13 : c <= 1 / 3)
    (heps : eps = c - (3 / 2) * c ^ 2)
    (hepsle : eps <= 1 / 100)
    (htheta : theta = (3 / 2) * c * (1 - c) ^ 2) :
    (3 / 2) * ((97 / 98) ^ 2) * (eps + (3 / 2) * eps ^ 2) <= theta := by
  have hc98 : c <= 1 / 98 :=
    razborov_parameter_le_one_ninetyeight hc0 hc13 heps hepsle
  have hceps : eps + (3 / 2) * eps ^ 2 <= c :=
    eps_plus_quadratic_le_c hc0 hc13 heps
  have hsq :
      (97 / 98 : Real) ^ 2 <= (1 - c) ^ 2 := by
    have hprod : 0 <= ((1 - c) - (97 / 98)) * ((1 - c) + (97 / 98)) := by
      exact mul_nonneg (by nlinarith) (by nlinarith)
    nlinarith
  rw [htheta]
  nlinarith [mul_nonneg (by norm_num : (0 : Real) <= 3 / 2)
    (mul_nonneg hc0 (sq_nonneg (1 - c)))]

private lemma endpoint_F_quotient_nonneg {eps : Real}
    (he0 : 0 <= eps) (he1 : eps <= 1 / 100) :
    0 <=
        ((1/343597383680 : Real)) * 1 +
        ((-129/429496729600 : Real)) * eps ^ 1 +
        ((13649/1073741824000 : Real)) * eps ^ 2 +
        ((-86183/268435456000 : Real)) * eps ^ 3 +
        ((75357429/13421772800000 : Real)) * eps ^ 4 +
        ((-1232523593/16777216000000 : Real)) * eps ^ 5 +
        ((3948785973/5242880000000 : Real)) * eps ^ 6 +
        ((-40831115259/6553600000000 : Real)) * eps ^ 7 +
        ((1111025073609/26214400000000 : Real)) * eps ^ 8 +
        ((-39306288480877/163840000000000 : Real)) * eps ^ 9 +
        ((465673158792723/409600000000000 : Real)) * eps ^ 10 +
        ((-2310908048842477/512000000000000 : Real)) * eps ^ 11 +
        ((76437279162497533/5120000000000000 : Real)) * eps ^ 12 +
        ((-10384045074268257/256000000000000 : Real)) * eps ^ 13 +
        ((5623762648562003/64000000000000 : Real)) * eps ^ 14 +
        ((-454103619761553/3200000000000 : Real)) * eps ^ 15 +
        ((3536742083706687/25600000000000 : Real)) * eps ^ 16 +
        ((33793905550889/1280000000000 : Real)) * eps ^ 17 +
        ((-243740145223729/640000000000 : Real)) * eps ^ 18 +
        ((4849511428839/6400000000 : Real)) * eps ^ 19 +
        ((-13044492756977/12800000000 : Real)) * eps ^ 20 +
        ((1086630591981/640000000 : Real)) * eps ^ 21 +
        ((-1500726399993/400000000 : Real)) * eps ^ 22 +
        ((116530677927/20000000 : Real)) * eps ^ 23 +
        ((-153583336263/80000000 : Real)) * eps ^ 24 +
        ((-52547130657/4000000 : Real)) * eps ^ 25 +
        ((66282675263/2000000 : Real)) * eps ^ 26 +
        ((-4479057569/100000 : Real)) * eps ^ 27 +
        ((9555199401/200000 : Real)) * eps ^ 28 +
        ((-102623433/2000 : Real)) * eps ^ 29 +
        ((23458633/500 : Real)) * eps ^ 30 +
        ((-130911/5 : Real)) * eps ^ 31 +
        ((24085873/2000 : Real)) * eps ^ 32 +
        ((-1117977/100 : Real)) * eps ^ 33 +
        ((1581/50 : Real)) * eps ^ 34 +
        ((-7422/5 : Real)) * eps ^ 35 +
        ((-179/5 : Real)) * eps ^ 36 +
        ((-36 : Real)) * eps ^ 37 := by
  let tt : Real := 100 * eps
  have htt0 : 0 <= tt := by
    dsimp [tt]
    positivity
  have htt1 : tt <= 1 := by
    dsimp [tt]
    nlinarith
  have h1tt0 : 0 <= 1 - tt := by linarith
  have hbern : 0 <=
        ((1/343597383680 : Real)) * 1 * (1 - tt) ^ 37 +
        ((281/2684354560000 : Real)) * tt ^ 1 * (1 - tt) ^ 36 +
        ((19665149/10737418240000000 : Real)) * tt ^ 2 * (1 - tt) ^ 35 +
        ((1393557923/67108864000000000 : Real)) * tt ^ 3 * (1 - tt) ^ 34 +
        ((230205724872429/1342177280000000000000 : Real)) * tt ^ 4 * (1 - tt) ^ 33 +
        ((23065456199140129/20971520000000000000000 : Real)) * tt ^ 5 * (1 - tt) ^ 32 +
        ((29875906577528755473/5242880000000000000000000 : Real)) * tt ^ 6 * (1 - tt) ^ 31 +
        ((4015983392052362101279/163840000000000000000000000 : Real)) * tt ^ 7 * (1 - tt) ^ 30 +
        ((23401062008355276701715609/262144000000000000000000000000 : Real)) * tt ^ 8 * (1 - tt) ^ 29 +
        ((5720146367553068903418522781/20480000000000000000000000000000 : Real)) * tt ^ 9 * (1 - tt) ^ 28 +
        ((31099484230372247617984926091223/40960000000000000000000000000000000 : Real)) * tt ^ 10 * (1 - tt) ^ 27 +
        ((1157797273333417259098362790215331/640000000000000000000000000000000000 : Real)) * tt ^ 11 * (1 - tt) ^ 26 +
        ((19477411409327430575628537112573470533/5120000000000000000000000000000000000000 : Real)) * tt ^ 12 * (1 - tt) ^ 25 +
        ((22717003424147053711672599074977771671/3200000000000000000000000000000000000000 : Real)) * tt ^ 13 * (1 - tt) ^ 24 +
        ((7556695414124644458141404537970001345303/640000000000000000000000000000000000000000 : Real)) * tt ^ 14 * (1 - tt) ^ 23 +
        ((439054766643393342897445682524896786639/25000000000000000000000000000000000000000 : Real)) * tt ^ 15 * (1 - tt) ^ 22 +
        ((59955894083244638397664312095527350035609887/2560000000000000000000000000000000000000000000 : Real)) * tt ^ 16 * (1 - tt) ^ 21 +
        ((5610750622766682480025129532615399069531891/200000000000000000000000000000000000000000000 : Real)) * tt ^ 17 * (1 - tt) ^ 20 +
        ((19340733821091660399035011030496704562547732771/640000000000000000000000000000000000000000000000 : Real)) * tt ^ 18 * (1 - tt) ^ 19 +
        ((4686740320667369540497665812848204141766762747/160000000000000000000000000000000000000000000000 : Real)) * tt ^ 19 * (1 - tt) ^ 18 +
        ((3270184281442145921318616649498750411871338881623/128000000000000000000000000000000000000000000000000 : Real)) * tt ^ 20 * (1 - tt) ^ 17 +
        ((1603093990481547787667926384318470571906383276867/80000000000000000000000000000000000000000000000000 : Real)) * tt ^ 21 * (1 - tt) ^ 16 +
        ((564688492420801394647304373508529868455397307808507/40000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 22 * (1 - tt) ^ 15 +
        ((445828345557420789169000121827108051741655812975863/50000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 23 * (1 - tt) ^ 14 +
        ((402892712442589451152179347548276131471446412597024937/80000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 24 * (1 - tt) ^ 13 +
        ((126751830512608767709721254337210116319559403575072031/50000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 25 * (1 - tt) ^ 12 +
        ((22646276755799509847146418404404393754233737789517452563/20000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 26 * (1 - tt) ^ 11 +
        ((2789588816120971117101718780112728400970515788013388681/6250000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 27 * (1 - tt) ^ 10 +
        ((3083775220806964618402159517712015493926592906869741276401/20000000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 28 * (1 - tt) ^ 9 +
        ((115683159359395995648311696945515841939587585061251680647/2500000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 29 * (1 - tt) ^ 8 +
        ((5964583164510083000634739933233979656777651482916951582933/500000000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 30 * (1 - tt) ^ 7 +
        ((32541817348393118796337599619828050822515673173589415463/12500000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 31 * (1 - tt) ^ 6 +
        ((9432310730688341999597673754407601390104806853960464535165873/20000000000000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 32 * (1 - tt) ^ 5 +
        ((431364352370316043342013455031762155411980090203481211189303/6250000000000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 33 * (1 - tt) ^ 4 +
        ((39200850115924442529824288322290742771121524056953508341088681/5000000000000000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 34 * (1 - tt) ^ 3 +
        ((4054093778661102606532918114088022227667809893154142699116751/6250000000000000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 35 * (1 - tt) ^ 2 +
        ((173858439046037600830864261080996081324214824037315783749108421/5000000000000000000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 36 * (1 - tt) ^ 1 +
        ((2832710483263226586542376007340566807695612290359490981399137/3125000000000000000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 37 * 1 := by
    positivity
  have hident :
      (((1/343597383680 : Real)) * 1 +
        ((-129/429496729600 : Real)) * eps ^ 1 +
        ((13649/1073741824000 : Real)) * eps ^ 2 +
        ((-86183/268435456000 : Real)) * eps ^ 3 +
        ((75357429/13421772800000 : Real)) * eps ^ 4 +
        ((-1232523593/16777216000000 : Real)) * eps ^ 5 +
        ((3948785973/5242880000000 : Real)) * eps ^ 6 +
        ((-40831115259/6553600000000 : Real)) * eps ^ 7 +
        ((1111025073609/26214400000000 : Real)) * eps ^ 8 +
        ((-39306288480877/163840000000000 : Real)) * eps ^ 9 +
        ((465673158792723/409600000000000 : Real)) * eps ^ 10 +
        ((-2310908048842477/512000000000000 : Real)) * eps ^ 11 +
        ((76437279162497533/5120000000000000 : Real)) * eps ^ 12 +
        ((-10384045074268257/256000000000000 : Real)) * eps ^ 13 +
        ((5623762648562003/64000000000000 : Real)) * eps ^ 14 +
        ((-454103619761553/3200000000000 : Real)) * eps ^ 15 +
        ((3536742083706687/25600000000000 : Real)) * eps ^ 16 +
        ((33793905550889/1280000000000 : Real)) * eps ^ 17 +
        ((-243740145223729/640000000000 : Real)) * eps ^ 18 +
        ((4849511428839/6400000000 : Real)) * eps ^ 19 +
        ((-13044492756977/12800000000 : Real)) * eps ^ 20 +
        ((1086630591981/640000000 : Real)) * eps ^ 21 +
        ((-1500726399993/400000000 : Real)) * eps ^ 22 +
        ((116530677927/20000000 : Real)) * eps ^ 23 +
        ((-153583336263/80000000 : Real)) * eps ^ 24 +
        ((-52547130657/4000000 : Real)) * eps ^ 25 +
        ((66282675263/2000000 : Real)) * eps ^ 26 +
        ((-4479057569/100000 : Real)) * eps ^ 27 +
        ((9555199401/200000 : Real)) * eps ^ 28 +
        ((-102623433/2000 : Real)) * eps ^ 29 +
        ((23458633/500 : Real)) * eps ^ 30 +
        ((-130911/5 : Real)) * eps ^ 31 +
        ((24085873/2000 : Real)) * eps ^ 32 +
        ((-1117977/100 : Real)) * eps ^ 33 +
        ((1581/50 : Real)) * eps ^ 34 +
        ((-7422/5 : Real)) * eps ^ 35 +
        ((-179/5 : Real)) * eps ^ 36 +
        ((-36 : Real)) * eps ^ 37) =
        (((1/343597383680 : Real)) * 1 * (1 - tt) ^ 37 +
        ((281/2684354560000 : Real)) * tt ^ 1 * (1 - tt) ^ 36 +
        ((19665149/10737418240000000 : Real)) * tt ^ 2 * (1 - tt) ^ 35 +
        ((1393557923/67108864000000000 : Real)) * tt ^ 3 * (1 - tt) ^ 34 +
        ((230205724872429/1342177280000000000000 : Real)) * tt ^ 4 * (1 - tt) ^ 33 +
        ((23065456199140129/20971520000000000000000 : Real)) * tt ^ 5 * (1 - tt) ^ 32 +
        ((29875906577528755473/5242880000000000000000000 : Real)) * tt ^ 6 * (1 - tt) ^ 31 +
        ((4015983392052362101279/163840000000000000000000000 : Real)) * tt ^ 7 * (1 - tt) ^ 30 +
        ((23401062008355276701715609/262144000000000000000000000000 : Real)) * tt ^ 8 * (1 - tt) ^ 29 +
        ((5720146367553068903418522781/20480000000000000000000000000000 : Real)) * tt ^ 9 * (1 - tt) ^ 28 +
        ((31099484230372247617984926091223/40960000000000000000000000000000000 : Real)) * tt ^ 10 * (1 - tt) ^ 27 +
        ((1157797273333417259098362790215331/640000000000000000000000000000000000 : Real)) * tt ^ 11 * (1 - tt) ^ 26 +
        ((19477411409327430575628537112573470533/5120000000000000000000000000000000000000 : Real)) * tt ^ 12 * (1 - tt) ^ 25 +
        ((22717003424147053711672599074977771671/3200000000000000000000000000000000000000 : Real)) * tt ^ 13 * (1 - tt) ^ 24 +
        ((7556695414124644458141404537970001345303/640000000000000000000000000000000000000000 : Real)) * tt ^ 14 * (1 - tt) ^ 23 +
        ((439054766643393342897445682524896786639/25000000000000000000000000000000000000000 : Real)) * tt ^ 15 * (1 - tt) ^ 22 +
        ((59955894083244638397664312095527350035609887/2560000000000000000000000000000000000000000000 : Real)) * tt ^ 16 * (1 - tt) ^ 21 +
        ((5610750622766682480025129532615399069531891/200000000000000000000000000000000000000000000 : Real)) * tt ^ 17 * (1 - tt) ^ 20 +
        ((19340733821091660399035011030496704562547732771/640000000000000000000000000000000000000000000000 : Real)) * tt ^ 18 * (1 - tt) ^ 19 +
        ((4686740320667369540497665812848204141766762747/160000000000000000000000000000000000000000000000 : Real)) * tt ^ 19 * (1 - tt) ^ 18 +
        ((3270184281442145921318616649498750411871338881623/128000000000000000000000000000000000000000000000000 : Real)) * tt ^ 20 * (1 - tt) ^ 17 +
        ((1603093990481547787667926384318470571906383276867/80000000000000000000000000000000000000000000000000 : Real)) * tt ^ 21 * (1 - tt) ^ 16 +
        ((564688492420801394647304373508529868455397307808507/40000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 22 * (1 - tt) ^ 15 +
        ((445828345557420789169000121827108051741655812975863/50000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 23 * (1 - tt) ^ 14 +
        ((402892712442589451152179347548276131471446412597024937/80000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 24 * (1 - tt) ^ 13 +
        ((126751830512608767709721254337210116319559403575072031/50000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 25 * (1 - tt) ^ 12 +
        ((22646276755799509847146418404404393754233737789517452563/20000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 26 * (1 - tt) ^ 11 +
        ((2789588816120971117101718780112728400970515788013388681/6250000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 27 * (1 - tt) ^ 10 +
        ((3083775220806964618402159517712015493926592906869741276401/20000000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 28 * (1 - tt) ^ 9 +
        ((115683159359395995648311696945515841939587585061251680647/2500000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 29 * (1 - tt) ^ 8 +
        ((5964583164510083000634739933233979656777651482916951582933/500000000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 30 * (1 - tt) ^ 7 +
        ((32541817348393118796337599619828050822515673173589415463/12500000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 31 * (1 - tt) ^ 6 +
        ((9432310730688341999597673754407601390104806853960464535165873/20000000000000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 32 * (1 - tt) ^ 5 +
        ((431364352370316043342013455031762155411980090203481211189303/6250000000000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 33 * (1 - tt) ^ 4 +
        ((39200850115924442529824288322290742771121524056953508341088681/5000000000000000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 34 * (1 - tt) ^ 3 +
        ((4054093778661102606532918114088022227667809893154142699116751/6250000000000000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 35 * (1 - tt) ^ 2 +
        ((173858439046037600830864261080996081324214824037315783749108421/5000000000000000000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 36 * (1 - tt) ^ 1 +
        ((2832710483263226586542376007340566807695612290359490981399137/3125000000000000000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 37 * 1) := by
    dsimp [tt]
    ring_nf
  rwa [hident]

private lemma endpoint_Delta_quotient_nonneg {eps : Real}
    (he0 : 0 <= eps) (he1 : eps <= 1 / 100) :
    0 <=
        ((121/109051904 : Real)) * 1 +
        ((-3949/88604672 : Real)) * eps ^ 1 +
        ((462583/575930368 : Real)) * eps ^ 2 +
        ((-7953099/935886848 : Real)) * eps ^ 3 +
        ((5633000483/97332232192 : Real)) * eps ^ 4 +
        ((-41201982569/158164877312 : Real)) * eps ^ 5 +
        ((778326149073/1028071702528 : Real)) * eps ^ 6 +
        ((-528337386841/417654129152 : Real)) * eps ^ 7 +
        ((176146768187291/347488235454464 : Real)) * eps ^ 8 +
        ((496263738734403/141167095653376 : Real)) * eps ^ 9 +
        ((-14627220614788221/917586121746944 : Real)) * eps ^ 10 +
        ((974184399690961539/19384006821904192 : Real)) * eps ^ 11 +
        ((-87944672781156719/917586121746944 : Real)) * eps ^ 12 +
        ((496263738734403/8822943478336 : Real)) * eps ^ 13 +
        ((43152644754681/339343979936 : Real)) * eps ^ 14 +
        ((-528337386841/1631461442 : Real)) * eps ^ 15 +
        ((4933779292519/8031810176 : Real)) * eps ^ 16 +
        ((-41201982569/38614472 : Real)) * eps ^ 17 +
        ((1386379467/1485172 : Real)) * eps ^ 18 +
        ((-15906198/28561 : Real)) * eps ^ 19 +
        ((5678787/8788 : Real)) * eps ^ 20 +
        ((-7898/169 : Real)) * eps ^ 21 +
        ((1428/13 : Real)) * eps ^ 22 +
        ((2 : Real)) * eps ^ 24 := by
  let tt : Real := 100 * eps
  have htt0 : 0 <= tt := by
    dsimp [tt]
    positivity
  have htt1 : tt <= 1 := by
    dsimp [tt]
    nlinarith
  have h1tt0 : 0 <= 1 - tt := by linarith
  have hbern : 0 <=
        ((121/109051904 : Real)) * 1 * (1 - tt) ^ 24 +
        ((232001/8860467200 : Real)) * tt ^ 1 * (1 - tt) ^ 23 +
        ((1705151283/5759303680000 : Real)) * tt ^ 2 * (1 - tt) ^ 22 +
        ((1997889941751/935886848000000 : Real)) * tt ^ 3 * (1 - tt) ^ 21 +
        ((107253148528298883/9733223219200000000 : Real)) * tt ^ 4 * (1 - tt) ^ 20 +
        ((68542706906625737181/1581648773120000000000 : Real)) * tt ^ 5 * (1 - tt) ^ 19 +
        ((138709691340291820878173/1028071702528000000000000 : Real)) * tt ^ 6 * (1 - tt) ^ 18 +
        ((14246116654569693751344509/41765412915200000000000000 : Real)) * tt ^ 7 * (1 - tt) ^ 17 +
        ((2476239335540740137291501996891/3474882354544640000000000000000 : Real)) * tt ^ 8 * (1 - tt) ^ 16 +
        ((175820430896171973737500283093553/141167095653376000000000000000000 : Real)) * tt ^ 9 * (1 - tt) ^ 15 +
        ((168527915126368763978513468226497279/91758612174694400000000000000000000 : Real)) * tt ^ 10 * (1 - tt) ^ 14 +
        ((445444735446906215569743860079763891089/193840068219041920000000000000000000000 : Real)) * tt ^ 11 * (1 - tt) ^ 13 +
        ((29193388850676486900814194068446208513853/11928619582710272000000000000000000000000 : Real)) * tt ^ 12 * (1 - tt) ^ 12 +
        ((331135993728931061325299856160558592602057/149107744783878400000000000000000000000000 : Real)) * tt ^ 13 * (1 - tt) ^ 11 +
        ((12788130240415281566263392770507900820979257/7455387239193920000000000000000000000000000 : Real)) * tt ^ 14 * (1 - tt) ^ 10 +
        ((52378596328365985532297843192455413153329949/46596170244962000000000000000000000000000000 : Real)) * tt ^ 15 * (1 - tt) ^ 9 +
        ((185355914403309897277107972438442580176934719467/298215489567756800000000000000000000000000000000 : Real)) * tt ^ 16 * (1 - tt) ^ 8 +
        ((535882620727243559719616205880835670027662521029/1863846809798480000000000000000000000000000000000 : Real)) * tt ^ 17 * (1 - tt) ^ 7 +
        ((10242345181793386764594739868221944645630447524339/93192340489924000000000000000000000000000000000000 : Real)) * tt ^ 18 * (1 - tt) ^ 6 +
        ((39740499975013338480640521288977685722860077771671/1164904256124050000000000000000000000000000000000000 : Real)) * tt ^ 19 * (1 - tt) ^ 5 +
        ((7812349132230852157262394084710034281271465217984551/931923404899240000000000000000000000000000000000000000 : Real)) * tt ^ 20 * (1 - tt) ^ 4 +
        ((18282801533979546414369852219557649461623875364065849/11649042561240500000000000000000000000000000000000000000 : Real)) * tt ^ 21 * (1 - tt) ^ 3 +
        ((122521919097564425245366767828453166061955266252232309/582452128062025000000000000000000000000000000000000000000 : Real)) * tt ^ 22 * (1 - tt) ^ 2 +
        ((81808895565005537984371789426434162984722088503631/4550407250484570312500000000000000000000000000000000000 : Real)) * tt ^ 23 * (1 - tt) ^ 1 +
        ((111495988330416076218996232973290813830201529729545432253/151437553296126500000000000000000000000000000000000000000000000 : Real)) * tt ^ 24 * 1 := by
    positivity
  have hident :
      (((121/109051904 : Real)) * 1 +
        ((-3949/88604672 : Real)) * eps ^ 1 +
        ((462583/575930368 : Real)) * eps ^ 2 +
        ((-7953099/935886848 : Real)) * eps ^ 3 +
        ((5633000483/97332232192 : Real)) * eps ^ 4 +
        ((-41201982569/158164877312 : Real)) * eps ^ 5 +
        ((778326149073/1028071702528 : Real)) * eps ^ 6 +
        ((-528337386841/417654129152 : Real)) * eps ^ 7 +
        ((176146768187291/347488235454464 : Real)) * eps ^ 8 +
        ((496263738734403/141167095653376 : Real)) * eps ^ 9 +
        ((-14627220614788221/917586121746944 : Real)) * eps ^ 10 +
        ((974184399690961539/19384006821904192 : Real)) * eps ^ 11 +
        ((-87944672781156719/917586121746944 : Real)) * eps ^ 12 +
        ((496263738734403/8822943478336 : Real)) * eps ^ 13 +
        ((43152644754681/339343979936 : Real)) * eps ^ 14 +
        ((-528337386841/1631461442 : Real)) * eps ^ 15 +
        ((4933779292519/8031810176 : Real)) * eps ^ 16 +
        ((-41201982569/38614472 : Real)) * eps ^ 17 +
        ((1386379467/1485172 : Real)) * eps ^ 18 +
        ((-15906198/28561 : Real)) * eps ^ 19 +
        ((5678787/8788 : Real)) * eps ^ 20 +
        ((-7898/169 : Real)) * eps ^ 21 +
        ((1428/13 : Real)) * eps ^ 22 +
        ((2 : Real)) * eps ^ 24) =
        (((121/109051904 : Real)) * 1 * (1 - tt) ^ 24 +
        ((232001/8860467200 : Real)) * tt ^ 1 * (1 - tt) ^ 23 +
        ((1705151283/5759303680000 : Real)) * tt ^ 2 * (1 - tt) ^ 22 +
        ((1997889941751/935886848000000 : Real)) * tt ^ 3 * (1 - tt) ^ 21 +
        ((107253148528298883/9733223219200000000 : Real)) * tt ^ 4 * (1 - tt) ^ 20 +
        ((68542706906625737181/1581648773120000000000 : Real)) * tt ^ 5 * (1 - tt) ^ 19 +
        ((138709691340291820878173/1028071702528000000000000 : Real)) * tt ^ 6 * (1 - tt) ^ 18 +
        ((14246116654569693751344509/41765412915200000000000000 : Real)) * tt ^ 7 * (1 - tt) ^ 17 +
        ((2476239335540740137291501996891/3474882354544640000000000000000 : Real)) * tt ^ 8 * (1 - tt) ^ 16 +
        ((175820430896171973737500283093553/141167095653376000000000000000000 : Real)) * tt ^ 9 * (1 - tt) ^ 15 +
        ((168527915126368763978513468226497279/91758612174694400000000000000000000 : Real)) * tt ^ 10 * (1 - tt) ^ 14 +
        ((445444735446906215569743860079763891089/193840068219041920000000000000000000000 : Real)) * tt ^ 11 * (1 - tt) ^ 13 +
        ((29193388850676486900814194068446208513853/11928619582710272000000000000000000000000 : Real)) * tt ^ 12 * (1 - tt) ^ 12 +
        ((331135993728931061325299856160558592602057/149107744783878400000000000000000000000000 : Real)) * tt ^ 13 * (1 - tt) ^ 11 +
        ((12788130240415281566263392770507900820979257/7455387239193920000000000000000000000000000 : Real)) * tt ^ 14 * (1 - tt) ^ 10 +
        ((52378596328365985532297843192455413153329949/46596170244962000000000000000000000000000000 : Real)) * tt ^ 15 * (1 - tt) ^ 9 +
        ((185355914403309897277107972438442580176934719467/298215489567756800000000000000000000000000000000 : Real)) * tt ^ 16 * (1 - tt) ^ 8 +
        ((535882620727243559719616205880835670027662521029/1863846809798480000000000000000000000000000000000 : Real)) * tt ^ 17 * (1 - tt) ^ 7 +
        ((10242345181793386764594739868221944645630447524339/93192340489924000000000000000000000000000000000000 : Real)) * tt ^ 18 * (1 - tt) ^ 6 +
        ((39740499975013338480640521288977685722860077771671/1164904256124050000000000000000000000000000000000000 : Real)) * tt ^ 19 * (1 - tt) ^ 5 +
        ((7812349132230852157262394084710034281271465217984551/931923404899240000000000000000000000000000000000000000 : Real)) * tt ^ 20 * (1 - tt) ^ 4 +
        ((18282801533979546414369852219557649461623875364065849/11649042561240500000000000000000000000000000000000000000 : Real)) * tt ^ 21 * (1 - tt) ^ 3 +
        ((122521919097564425245366767828453166061955266252232309/582452128062025000000000000000000000000000000000000000000 : Real)) * tt ^ 22 * (1 - tt) ^ 2 +
        ((81808895565005537984371789426434162984722088503631/4550407250484570312500000000000000000000000000000000000 : Real)) * tt ^ 23 * (1 - tt) ^ 1 +
        ((111495988330416076218996232973290813830201529729545432253/151437553296126500000000000000000000000000000000000000000000000 : Real)) * tt ^ 24 * 1) := by
    dsimp [tt]
    ring_nf
  rwa [hident]

/-- Endpoint bound `p^3 - alpha^3 <= 7/5 eps` for the C13 scalar proof. -/
lemma endpoint_F_bound {eps p q alpha : Real}
    (he0 : 0 <= eps) (he1 : eps <= 1 / 100)
    (hp : p = 1 / 2 + eps) (hq : q = 1 / 2 - eps)
    (halpha13 : alpha ^ 13 = p * q ^ 12) :
    p ^ 3 - alpha ^ 3 <= (7 / 5) * eps := by
  have hbase0 : 0 <= p ^ 3 - (7 / 5) * eps := by
    rw [hp]
    ring_nf
    nlinarith [he0, he1]
  have hpow :
      (p ^ 3 - (7 / 5) * eps) ^ 13 <= (alpha ^ 3) ^ 13 := by
    rw [show (alpha ^ 3) ^ 13 = (alpha ^ 13) ^ 3 by ring, halpha13]
    have hb := endpoint_F_quotient_nonneg he0 he1
    rw [hp, hq]
    ring_nf
    nlinarith [mul_nonneg he0 hb]
  have hle : p ^ 3 - (7 / 5) * eps <= alpha ^ 3 :=
    (show Odd (13 : Nat) by norm_num).pow_le_pow.mp hpow
  linarith

/-- Endpoint bound `pq - alpha^2 <= 11/13 eps` for the C13 scalar proof. -/
lemma endpoint_Delta_upper {eps p q alpha : Real}
    (he0 : 0 <= eps) (he1 : eps <= 1 / 100)
    (hp : p = 1 / 2 + eps) (hq : q = 1 / 2 - eps)
    (halpha13 : alpha ^ 13 = p * q ^ 12) :
    p * q - alpha ^ 2 <= (11 / 13) * eps := by
  have hpq0 : 0 <= p * q - (11 / 13) * eps := by
    rw [hp, hq]
    ring_nf
    nlinarith [he0, he1]
  have hpow :
      (p * q - (11 / 13) * eps) ^ 13 <= (alpha ^ 2) ^ 13 := by
    rw [show (alpha ^ 2) ^ 13 = (alpha ^ 13) ^ 2 by ring, halpha13]
    have hb := endpoint_Delta_quotient_nonneg he0 he1
    rw [hp, hq]
    ring_nf
    nlinarith [mul_nonneg (sq_nonneg eps) hb]
  have hle : p * q - (11 / 13) * eps <= alpha ^ 2 :=
    (show Odd (13 : Nat) by norm_num).pow_le_pow.mp hpow
  linarith

/-- The endpoint `Delta = pq - alpha^2` is nonnegative for
`alpha^13 = p q^12` in the C13 near-bipartite band. -/
lemma endpoint_Delta_nonneg {eps p q alpha : Real}
    (he0 : 0 <= eps) (he1 : eps <= 1 / 100)
    (hp : p = 1 / 2 + eps) (hq : q = 1 / 2 - eps)
    (halpha13 : alpha ^ 13 = p * q ^ 12) :
    0 <= p * q - alpha ^ 2 := by
  have hp0 : 0 <= p := by rw [hp]; nlinarith
  have hq0 : 0 <= q := by rw [hq]; nlinarith
  have hqle : q <= p := by rw [hp, hq]; nlinarith
  have hpq0 : 0 <= p * q := mul_nonneg hp0 hq0
  have hqpow : q ^ 11 <= p ^ 11 :=
    (show Odd (11 : Nat) by norm_num).pow_le_pow.mpr hqle
  have hpow_nonneg : 0 <= p ^ 2 * q ^ 13 * (p ^ 11 - q ^ 11) :=
    mul_nonneg (mul_nonneg (sq_nonneg p) (pow_nonneg hq0 13)) (by linarith)
  have hpow :
      (alpha ^ 2) ^ 13 <= (p * q) ^ 13 := by
    rw [show (alpha ^ 2) ^ 13 = (alpha ^ 13) ^ 2 by ring, halpha13]
    nlinarith
  have hle : alpha ^ 2 <= p * q :=
    (show Odd (13 : Nat) by norm_num).pow_le_pow.mp hpow
  linarith

/-- The full one-variable endpoint estimate at `ell = p` used by the C13
near-bipartite scalar proof. -/
lemma endpoint_scalar_bound {eps p q alpha theta : Real}
    (he0 : 0 <= eps) (he1 : eps <= 1 / 100)
    (hp : p = 1 / 2 + eps) (hq : q = 1 / 2 - eps)
    (halpha13 : alpha ^ 13 = p * q ^ 12)
    (htheta :
      (3 / 2) * ((97 / 98) ^ 2) * (eps + (3 / 2) * eps ^ 2) <= theta) :
    p ^ 3 - alpha ^ 3 +
        Real.sqrt (p * q - alpha ^ 2) * (p * q - alpha ^ 2) <= theta := by
  have hF := endpoint_F_bound he0 he1 hp hq halpha13
  have hD := endpoint_Delta_upper he0 he1 hp hq halpha13
  have hD0 := endpoint_Delta_nonneg he0 he1 hp hq halpha13
  exact scalar_final he0 htheta hF hD0 hD

private lemma sqrt_mul_self_mono {x y : Real}
    (hx0 : 0 <= x) (hxy : x <= y) :
    Real.sqrt x * x <= Real.sqrt y * y := by
  have hy0 : 0 <= y := hx0.trans hxy
  exact mul_le_mul (Real.sqrt_le_sqrt hxy) hxy hx0 (Real.sqrt_nonneg y)

private lemma p_pow_add_le_mul_pow {p x y : Real} (hp0 : 0 <= p)
    (hpx : p <= x) (hpy : p <= y) (a b : Nat) :
    p ^ (a + b) <= x ^ a * y ^ b := by
  have hx0 : 0 <= x := hp0.trans hpx
  have hpa : p ^ a <= x ^ a := pow_le_pow_left₀ hp0 hpx a
  have hpb : p ^ b <= y ^ b := pow_le_pow_left₀ hp0 hpy b
  have hm := mul_le_mul hpa hpb (pow_nonneg hp0 b) (pow_nonneg hx0 a)
  simpa [pow_add] using hm

private lemma mul_pow_le_p_pow_add {p x y : Real} (hx0 : 0 <= x) (hy0 : 0 <= y)
    (hxp : x <= p) (hyp : y <= p) (a b : Nat) :
    x ^ a * y ^ b <= p ^ (a + b) := by
  have hp0 : 0 <= p := hx0.trans hxp
  have hxa : x ^ a <= p ^ a := pow_le_pow_left₀ hx0 hxp a
  have hyb : y ^ b <= p ^ b := pow_le_pow_left₀ hy0 hyp b
  have hm := mul_le_mul hxa hyb (pow_nonneg hy0 b) (pow_nonneg hp0 a)
  simpa [pow_add] using hm

private lemma thirteenth_sub_ge_scale_cubic_sub_high
    {p y x : Real} (hp0 : 0 <= p) (hpy : p <= y) (hyx : y <= x) :
    13 * p ^ 10 * (x ^ 3 - y ^ 3) <= 3 * (x ^ 13 - y ^ 13) := by
  have hx0 : 0 <= x := hp0.trans (hpy.trans hyx)
  have hy0 : 0 <= y := hp0.trans hpy
  have hpx : p <= x := hpy.trans hyx
  have hxy : 0 <= x - y := by linarith
  have hmargin : 0 <= p ^ 10 * (2 * x ^ 2 - x * y - y ^ 2) := by
    have hquad : 0 <= 2 * x ^ 2 - x * y - y ^ 2 := by
      have hfactor := mul_nonneg (sub_nonneg.mpr hyx)
        (by nlinarith : 0 <= 2 * x + y)
      nlinarith
    exact mul_nonneg (pow_nonneg hp0 10) hquad
  have t0 : p ^ 10 * x ^ 2 <= x ^ 12 := by
    have h : p ^ 10 <= x ^ 10 := pow_le_pow_left₀ hp0 hpx 10
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg x)
    nlinarith
  have t1 : p ^ 10 * x ^ 2 <= x ^ 11 * y := by
    have h : p ^ 10 <= x ^ 9 * y := by
      simpa using p_pow_add_le_mul_pow hp0 hpx hpy 9 1
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg x)
    nlinarith
  have t2 : p ^ 10 * x ^ 2 <= x ^ 10 * y ^ 2 := by
    have h : p ^ 10 <= x ^ 8 * y ^ 2 := by
      simpa using p_pow_add_le_mul_pow hp0 hpx hpy 8 2
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg x)
    nlinarith
  have t3 : p ^ 10 * x ^ 2 <= x ^ 9 * y ^ 3 := by
    have h : p ^ 10 <= x ^ 7 * y ^ 3 := by
      simpa using p_pow_add_le_mul_pow hp0 hpx hpy 7 3
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg x)
    nlinarith
  have t4 : p ^ 10 * x ^ 2 <= x ^ 8 * y ^ 4 := by
    have h : p ^ 10 <= x ^ 6 * y ^ 4 := by
      simpa using p_pow_add_le_mul_pow hp0 hpx hpy 6 4
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg x)
    nlinarith
  have t5 : p ^ 10 * x ^ 2 <= x ^ 7 * y ^ 5 := by
    have h : p ^ 10 <= x ^ 5 * y ^ 5 := by
      simpa using p_pow_add_le_mul_pow hp0 hpx hpy 5 5
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg x)
    nlinarith
  have t6 : p ^ 10 * x ^ 2 <= x ^ 6 * y ^ 6 := by
    have h : p ^ 10 <= x ^ 4 * y ^ 6 := by
      simpa using p_pow_add_le_mul_pow hp0 hpx hpy 4 6
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg x)
    nlinarith
  have t7 : p ^ 10 * x ^ 2 <= x ^ 5 * y ^ 7 := by
    have h : p ^ 10 <= x ^ 3 * y ^ 7 := by
      simpa using p_pow_add_le_mul_pow hp0 hpx hpy 3 7
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg x)
    nlinarith
  have t8 : p ^ 10 * x ^ 2 <= x ^ 4 * y ^ 8 := by
    have h : p ^ 10 <= x ^ 2 * y ^ 8 := by
      simpa using p_pow_add_le_mul_pow hp0 hpx hpy 2 8
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg x)
    nlinarith
  have t9 : p ^ 10 * x ^ 2 <= x ^ 3 * y ^ 9 := by
    have h : p ^ 10 <= x * y ^ 9 := by
      simpa using p_pow_add_le_mul_pow hp0 hpx hpy 1 9
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg x)
    nlinarith
  have t10 : p ^ 10 * x ^ 2 <= x ^ 2 * y ^ 10 := by
    have h : p ^ 10 <= y ^ 10 := pow_le_pow_left₀ hp0 hpy 10
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg x)
    nlinarith
  have t11 : p ^ 10 * (x * y) <= x * y ^ 11 := by
    have h : p ^ 10 <= y ^ 10 := pow_le_pow_left₀ hp0 hpy 10
    have hm := mul_le_mul_of_nonneg_right h (mul_nonneg hx0 hy0)
    nlinarith
  have t12 : p ^ 10 * y ^ 2 <= y ^ 12 := by
    have h : p ^ 10 <= y ^ 10 := pow_le_pow_left₀ hp0 hpy 10
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg y)
    nlinarith
  have hsum :
      13 * p ^ 10 * (x ^ 2 + x * y + y ^ 2) <=
        3 * (x ^ 12 + x ^ 11 * y + x ^ 10 * y ^ 2 +
          x ^ 9 * y ^ 3 + x ^ 8 * y ^ 4 + x ^ 7 * y ^ 5 +
          x ^ 6 * y ^ 6 + x ^ 5 * y ^ 7 + x ^ 4 * y ^ 8 +
          x ^ 3 * y ^ 9 + x ^ 2 * y ^ 10 + x * y ^ 11 + y ^ 12) := by
    nlinarith [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12,
      hmargin]
  have hfac13 :
      x ^ 13 - y ^ 13 = (x - y) *
        (x ^ 12 + x ^ 11 * y + x ^ 10 * y ^ 2 +
          x ^ 9 * y ^ 3 + x ^ 8 * y ^ 4 + x ^ 7 * y ^ 5 +
          x ^ 6 * y ^ 6 + x ^ 5 * y ^ 7 + x ^ 4 * y ^ 8 +
          x ^ 3 * y ^ 9 + x ^ 2 * y ^ 10 + x * y ^ 11 + y ^ 12) := by
    ring
  have hfac3 : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by
    ring
  nlinarith [mul_le_mul_of_nonneg_left hsum hxy]

private lemma thirteenth_sub_le_scale_cubic_sub_low
    {p y x : Real} (hy0 : 0 <= y) (hyx : y <= x) (hxp : x <= p) :
    3 * (x ^ 13 - y ^ 13) <= 13 * p ^ 10 * (x ^ 3 - y ^ 3) := by
  have hx0 : 0 <= x := hy0.trans hyx
  have hp0 : 0 <= p := hx0.trans hxp
  have hyp : y <= p := hyx.trans hxp
  have hxy : 0 <= x - y := by linarith
  have hmargin : 0 <= p ^ 10 * (x ^ 2 + x * y - 2 * y ^ 2) := by
    have hquad : 0 <= x ^ 2 + x * y - 2 * y ^ 2 := by
      have hfactor := mul_nonneg (sub_nonneg.mpr hyx)
        (by nlinarith : 0 <= x + 2 * y)
      nlinarith
    exact mul_nonneg (pow_nonneg hp0 10) hquad
  have t0 : x ^ 12 <= p ^ 10 * x ^ 2 := by
    have h : x ^ 10 <= p ^ 10 := pow_le_pow_left₀ hx0 hxp 10
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg x)
    nlinarith
  have t1 : x ^ 11 * y <= p ^ 10 * (x * y) := by
    have h : x ^ 10 <= p ^ 10 := pow_le_pow_left₀ hx0 hxp 10
    have hm := mul_le_mul_of_nonneg_right h (mul_nonneg hx0 hy0)
    nlinarith
  have t2 : x ^ 10 * y ^ 2 <= p ^ 10 * y ^ 2 := by
    have h : x ^ 10 <= p ^ 10 := pow_le_pow_left₀ hx0 hxp 10
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg y)
    nlinarith
  have t3 : x ^ 9 * y ^ 3 <= p ^ 10 * y ^ 2 := by
    have h : x ^ 9 * y <= p ^ 10 := by
      simpa using mul_pow_le_p_pow_add hx0 hy0 hxp hyp 9 1
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg y)
    nlinarith
  have t4 : x ^ 8 * y ^ 4 <= p ^ 10 * y ^ 2 := by
    have h : x ^ 8 * y ^ 2 <= p ^ 10 := by
      simpa using mul_pow_le_p_pow_add hx0 hy0 hxp hyp 8 2
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg y)
    nlinarith
  have t5 : x ^ 7 * y ^ 5 <= p ^ 10 * y ^ 2 := by
    have h : x ^ 7 * y ^ 3 <= p ^ 10 := by
      simpa using mul_pow_le_p_pow_add hx0 hy0 hxp hyp 7 3
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg y)
    nlinarith
  have t6 : x ^ 6 * y ^ 6 <= p ^ 10 * y ^ 2 := by
    have h : x ^ 6 * y ^ 4 <= p ^ 10 := by
      simpa using mul_pow_le_p_pow_add hx0 hy0 hxp hyp 6 4
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg y)
    nlinarith
  have t7 : x ^ 5 * y ^ 7 <= p ^ 10 * y ^ 2 := by
    have h : x ^ 5 * y ^ 5 <= p ^ 10 := by
      simpa using mul_pow_le_p_pow_add hx0 hy0 hxp hyp 5 5
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg y)
    nlinarith
  have t8 : x ^ 4 * y ^ 8 <= p ^ 10 * y ^ 2 := by
    have h : x ^ 4 * y ^ 6 <= p ^ 10 := by
      simpa using mul_pow_le_p_pow_add hx0 hy0 hxp hyp 4 6
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg y)
    nlinarith
  have t9 : x ^ 3 * y ^ 9 <= p ^ 10 * y ^ 2 := by
    have h : x ^ 3 * y ^ 7 <= p ^ 10 := by
      simpa using mul_pow_le_p_pow_add hx0 hy0 hxp hyp 3 7
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg y)
    nlinarith
  have t10 : x ^ 2 * y ^ 10 <= p ^ 10 * y ^ 2 := by
    have h : x ^ 2 * y ^ 8 <= p ^ 10 := by
      simpa using mul_pow_le_p_pow_add hx0 hy0 hxp hyp 2 8
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg y)
    nlinarith
  have t11 : x * y ^ 11 <= p ^ 10 * y ^ 2 := by
    have h : x * y ^ 9 <= p ^ 10 := by
      simpa using mul_pow_le_p_pow_add hx0 hy0 hxp hyp 1 9
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg y)
    nlinarith
  have t12 : y ^ 12 <= p ^ 10 * y ^ 2 := by
    have h : y ^ 10 <= p ^ 10 := pow_le_pow_left₀ hy0 hyp 10
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg y)
    nlinarith
  have hsum :
      3 * (x ^ 12 + x ^ 11 * y + x ^ 10 * y ^ 2 +
          x ^ 9 * y ^ 3 + x ^ 8 * y ^ 4 + x ^ 7 * y ^ 5 +
          x ^ 6 * y ^ 6 + x ^ 5 * y ^ 7 + x ^ 4 * y ^ 8 +
          x ^ 3 * y ^ 9 + x ^ 2 * y ^ 10 + x * y ^ 11 + y ^ 12) <=
        13 * p ^ 10 * (x ^ 2 + x * y + y ^ 2) := by
    nlinarith [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12,
      hmargin]
  have hfac13 :
      x ^ 13 - y ^ 13 = (x - y) *
        (x ^ 12 + x ^ 11 * y + x ^ 10 * y ^ 2 +
          x ^ 9 * y ^ 3 + x ^ 8 * y ^ 4 + x ^ 7 * y ^ 5 +
          x ^ 6 * y ^ 6 + x ^ 5 * y ^ 7 + x ^ 4 * y ^ 8 +
          x ^ 3 * y ^ 9 + x ^ 2 * y ^ 10 + x * y ^ 11 + y ^ 12) := by
    ring
  have hfac3 : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by
    ring
  nlinarith [mul_le_mul_of_nonneg_left hsum hxy]

/-- Algebraic reduction from the principal root `ell` to the endpoint
`ell = p` for the C13 scalar comparison. -/
lemma ell_reduction_bound
    {p q ell alpha0 alpha : Real}
    (hp0 : 0 <= p) (hp_half : 1 / 2 <= p)
    (ha00 : 0 <= alpha0) (hpell : p <= ell)
    (ha013 : alpha0 ^ 13 = p * q ^ 12)
    (ha13 : alpha ^ 13 = ell ^ 13 - p ^ 13 + p * q ^ 12)
    (hDelta : 0 <= p - ell ^ 2 - alpha ^ 2) :
    ell ^ 3 - alpha ^ 3 +
        Real.sqrt (p - ell ^ 2 - alpha ^ 2) *
          (p - ell ^ 2 - alpha ^ 2) <=
      p ^ 3 - alpha0 ^ 3 +
        Real.sqrt (p - p ^ 2 - alpha0 ^ 2) *
          (p - p ^ 2 - alpha0 ^ 2) := by
  have hp_pos : 0 < p := by nlinarith
  have hell0 : 0 <= ell := hp0.trans hpell
  have ha0a : alpha0 <= alpha := by
    have hpow : alpha0 ^ 13 <= alpha ^ 13 := by
      rw [ha013, ha13]
      have hpell13 : p ^ 13 <= ell ^ 13 := pow_le_pow_left₀ hp0 hpell 13
      nlinarith
    exact (show Odd (13 : Nat) by norm_num).pow_le_pow.mp hpow
  have halpha_le_p : alpha <= p := by
    have hpell2 : p ^ 2 <= ell ^ 2 := pow_le_pow_left₀ hp0 hpell 2
    have hp_le_one : p <= 1 := by nlinarith
    have halpha_sq : alpha ^ 2 <= p ^ 2 := by nlinarith
    by_contra hnot
    have hlt : p < alpha := lt_of_not_ge hnot
    have hslt : p ^ 2 < alpha ^ 2 :=
      pow_lt_pow_left₀ hlt hp0 (by norm_num : (2 : Nat) ≠ 0)
    nlinarith
  have hdiff : alpha ^ 13 - alpha0 ^ 13 = ell ^ 13 - p ^ 13 := by
    rw [ha013, ha13]
    ring
  have hhigh :=
    thirteenth_sub_ge_scale_cubic_sub_high (p := p) (y := p) (x := ell)
      hp0 le_rfl hpell
  have hlow :=
    thirteenth_sub_le_scale_cubic_sub_low (p := p) (y := alpha0) (x := alpha)
      ha00 ha0a halpha_le_p
  have hcubic :
      ell ^ 3 - p ^ 3 <= alpha ^ 3 - alpha0 ^ 3 := by
    have hscale_pos : 0 < 13 * p ^ 10 := by positivity
    nlinarith
  have hDelta_le :
      p - ell ^ 2 - alpha ^ 2 <= p - p ^ 2 - alpha0 ^ 2 := by
    have hp2 : p ^ 2 <= ell ^ 2 := pow_le_pow_left₀ hp0 hpell 2
    have ha2 : alpha0 ^ 2 <= alpha ^ 2 := pow_le_pow_left₀ ha00 ha0a 2
    nlinarith
  have hsqrt := sqrt_mul_self_mono hDelta hDelta_le
  nlinarith

/-- The cubic capacity
`sqrt (S - z^2) * (S - z^2) - z^3` is strictly decreasing in the
nonnegative root parameter `z`, as long as the remaining square budget is
nonnegative. -/
lemma cubic_capacity_strict_decreases
    {S alpha z : Real}
    (halpha0 : 0 <= alpha) (_hz0 : 0 <= z)
    (hlt : alpha < z)
    (hbudget : 0 <= S - z ^ 2) :
    Real.sqrt (S - z ^ 2) * (S - z ^ 2) - z ^ 3 <
      Real.sqrt (S - alpha ^ 2) * (S - alpha ^ 2) - alpha ^ 3 := by
  have hsq_lt : alpha ^ 2 < z ^ 2 := by
    exact pow_lt_pow_left₀ hlt halpha0 (by norm_num : (2 : Nat) ≠ 0)
  have hbudget_le : S - z ^ 2 <= S - alpha ^ 2 := by
    nlinarith
  have hbudget_mono :
      Real.sqrt (S - z ^ 2) * (S - z ^ 2) <=
        Real.sqrt (S - alpha ^ 2) * (S - alpha ^ 2) :=
    sqrt_mul_self_mono hbudget hbudget_le
  have hcube_lt : alpha ^ 3 < z ^ 3 := by
    exact pow_lt_pow_left₀ hlt halpha0 (by norm_num : (3 : Nat) ≠ 0)
  nlinarith

/-- Same monotonicity step, phrased in the thirteenth-power comparison that
arises from `alpha^13 < z^13`. -/
lemma cubic_capacity_strict_decreases_of_thirteenth
    {S alpha z : Real}
    (halpha0 : 0 <= alpha) (hz0 : 0 <= z)
    (hthirteenth : alpha ^ 13 < z ^ 13)
    (hbudget : 0 <= S - z ^ 2) :
    Real.sqrt (S - z ^ 2) * (S - z ^ 2) - z ^ 3 <
      Real.sqrt (S - alpha ^ 2) * (S - alpha ^ 2) - alpha ^ 3 := by
  have hlt : alpha < z := by
    exact (show Odd (13 : Nat) by norm_num).pow_lt_pow.mp hthirteenth
  exact cubic_capacity_strict_decreases halpha0 hz0 hlt hbudget

/-- The C13 target follows from the spectral negative-mass estimate.

This is the same final algebraic step as in the C9/C11 low-band arguments,
with exponent `13`.
-/
theorem cycle_bound_of_negative_mass_bound
    {ell N13 q : Real}
    (hq : q = 1 - edgeDensity W mu)
    (htrace : ell ^ 13 - N13 <= trace mu (compPow mu W 12))
    (hN13 :
      N13 <= ell ^ 13 - edgeDensity W mu ^ 13 +
        edgeDensity W mu * q ^ 12) :
    trace mu (compPow mu W 12) >=
      edgeDensity W mu ^ 13 - edgeDensity W mu * (1 - edgeDensity W mu) ^ 12 := by
  rw [hq] at hN13
  nlinarith

end C13
end LowBand
end OddCycleBound
