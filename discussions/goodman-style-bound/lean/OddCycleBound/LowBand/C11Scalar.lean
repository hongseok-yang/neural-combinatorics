import OddCycleBound.Kernel

/-!
# C11 low-band scalar arithmetic

This file contains the real-variable part of the `C11` near-bipartite
triangle/spectral argument.  It does not construct the spectral decomposition;
it proves the scalar comparison consumed once the analytic input has produced
the endpoint estimates for the principal root and the negative eleventh-power
mass bound.
-/

open MeasureTheory

namespace OddCycleBound
namespace LowBand
namespace C11

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
variable {W : Omega -> Omega -> Real}

/-- The final scalar comparison for the C11 low-band proof.

Here `B` abbreviates `p^3 - alpha_0^3`, `Delta` abbreviates
`p*q - alpha_0^2`, and `theta` is the Razborov/Reiher triangle-density lower
bound.  The two endpoint estimates are the rational bounds checked in
`odd_cycle_c11_checker.py`.
-/
lemma scalar_final {eps theta B Delta : Real}
    (heps0 : 0 <= eps)
    (htheta :
      (3 / 2) * ((64 / 65) ^ 2) * (eps + (3 / 2) * eps ^ 2) <= theta)
    (hB : B <= (139 / 100) * eps)
    (hDelta0 : 0 <= Delta)
    (hDelta : Delta <= (9 / 11) * eps) :
    B + Real.sqrt Delta * Delta <= theta := by
  let t := Real.sqrt eps
  let a : Real := (3 / 2) * ((64 / 65) ^ 2)
  let b : Real := (90 / 121)
  have ht0 : 0 <= t := Real.sqrt_nonneg eps
  have ht2 : t ^ 2 = eps := by
    dsimp [t]
    exact Real.sq_sqrt heps0
  have hsqrtDelta : Real.sqrt Delta <= (10 / 11) * t := by
    have hright0 : 0 <= (10 / 11) * t := by
      exact mul_nonneg (by norm_num) ht0
    rw [Real.sqrt_le_left hright0]
    calc
      Delta <= (9 / 11) * eps := hDelta
      _ <= ((10 / 11) * t) ^ 2 := by
        rw [mul_pow, ht2]
        nlinarith [heps0]
  have hDelta' : Delta <= (9 / 11) * eps := hDelta
  have hrootTerm :
      Real.sqrt Delta * Delta <= b * t * eps := by
    calc
      Real.sqrt Delta * Delta <= ((10 / 11) * t) * ((9 / 11) * eps) := by
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
  have hmargin : (139 / 100) + b ^ 2 / (6 * a) <= a := by
    dsimp [a, b]
    norm_num
  have hquad :
      (139 / 100) * eps + b * t * eps <=
        a * (eps + (3 / 2) * eps ^ 2) := by
    have hyoung_mul := mul_le_mul_of_nonneg_right hyoung heps0
    rw [ht2] at hyoung_mul
    nlinarith [hmargin]
  nlinarith

private lemma razborov_parameter_le_one_sixtyfive
    {c eps : Real}
    (_hc0 : 0 <= c) (hc13 : c <= 1 / 3)
    (heps : eps = c - (3 / 2) * c ^ 2) (hepsle : eps <= 3 / 200) :
    c <= 1 / 65 := by
  by_contra h
  have hcge : 1 / 65 <= c := by linarith
  have hdif : 0 <= c - 1 / 65 := by linarith
  have hfactor : 0 <= 1 - (3 / 2) * (c + 1 / 65) := by nlinarith
  have hmono :
      (1 / 65 : Real) - (3 / 2) * (1 / 65) ^ 2 <=
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

/-- In the C11 low band, the Razborov parameterized triangle lower bound
dominates the quadratic epsilon slack used by the endpoint scalar proof. -/
lemma theta_quadratic_lower_of_razborov
    {c eps theta : Real}
    (hc0 : 0 <= c) (hc13 : c <= 1 / 3)
    (heps : eps = c - (3 / 2) * c ^ 2)
    (hepsle : eps <= 3 / 200)
    (htheta : theta = (3 / 2) * c * (1 - c) ^ 2) :
    (3 / 2) * ((64 / 65) ^ 2) * (eps + (3 / 2) * eps ^ 2) <= theta := by
  have hc65 : c <= 1 / 65 :=
    razborov_parameter_le_one_sixtyfive hc0 hc13 heps hepsle
  have hceps : eps + (3 / 2) * eps ^ 2 <= c :=
    eps_plus_quadratic_le_c hc0 hc13 heps
  have hsq :
      (64 / 65 : Real) ^ 2 <= (1 - c) ^ 2 := by
    have hleft0 : 0 <= (64 / 65 : Real) := by norm_num
    have hright0 : 0 <= 1 - c := by nlinarith
    have hle : (64 / 65 : Real) <= 1 - c := by nlinarith
    exact pow_le_pow_left₀ hleft0 hle 2
  rw [htheta]
  nlinarith [mul_nonneg (by norm_num : (0 : Real) <= 3 / 2)
    (mul_nonneg hc0 (sq_nonneg (1 - c)))]


private lemma endpoint_F_quotient_nonneg {eps : Real}
    (he0 : 0 <= eps) (he1 : eps <= 3 / 200) :
    0 <=
        ((29/107374182400 : Real)) * 1 +
        ((-5681/268435456000 : Real)) * eps ^ 1 +
        ((2368877/3355443200000 : Real)) * eps ^ 2 +
        ((-595225631/41943040000000 : Real)) * eps ^ 3 +
        ((258935451969/1310720000000000 : Real)) * eps ^ 4 +
        ((-33546960416641/16384000000000000 : Real)) * eps ^ 5 +
        ((1350259593171489/81920000000000000 : Real)) * eps ^ 6 +
        ((-108246451098533523/1024000000000000000 : Real)) * eps ^ 7 +
        ((7012950307174891199/12800000000000000000 : Real)) * eps ^ 8 +
        ((-922764260847477786493/400000000000000000000 : Real)) * eps ^ 9 +
        ((39292417171488147375107/5000000000000000000000 : Real)) * eps ^ 10 +
        ((-532241809388443771151/25000000000000000000 : Real)) * eps ^ 11 +
        ((1099346323466677961941/25000000000000000000 : Real)) * eps ^ 12 +
        ((-12349579143109161903/200000000000000000 : Real)) * eps ^ 13 +
        ((809295380439780553/25000000000000000 : Real)) * eps ^ 14 +
        ((362740068438042993/4000000000000000 : Real)) * eps ^ 15 +
        ((-4259019242061291/15625000000000 : Real)) * eps ^ 16 +
        ((14001817943812743/40000000000000 : Real)) * eps ^ 17 +
        ((-4614070990342161/20000000000000 : Real)) * eps ^ 18 +
        ((75347710892769/400000000000 : Real)) * eps ^ 19 +
        ((-113793627698133/250000000000 : Real)) * eps ^ 20 +
        ((277240021173/2500000000 : Real)) * eps ^ 21 +
        ((22880882334063/10000000000 : Real)) * eps ^ 22 +
        ((-54733116969/10000000 : Real)) * eps ^ 23 +
        ((116261530719/20000000 : Real)) * eps ^ 24 +
        ((-1573597377/400000 : Real)) * eps ^ 25 +
        ((764084027/200000 : Real)) * eps ^ 26 +
        ((-13371137/4000 : Real)) * eps ^ 27 +
        ((3784/125 : Real)) * eps ^ 28 +
        ((-16163/20 : Real)) * eps ^ 29 +
        ((-2971/100 : Real)) * eps ^ 30 +
        ((-30 : Real)) * eps ^ 31 := by
  let tt : Real := (200 / 3) * eps
  have htt0 : 0 <= tt := by
    dsimp [tt]
    positivity
  have htt1 : tt <= 1 := by
    dsimp [tt]
    nlinarith
  have h1tt0 : 0 <= 1 - tt := by linarith
  have hbern : 0 <=
        ((29/107374182400 : Real)) * 1 * (1 - tt) ^ 31 +
        ((432457/53687091200000 : Real)) * tt ^ 1 * (1 - tt) ^ 30 +
        ((15599344893/134217728000000000 : Real)) * tt ^ 2 * (1 - tt) ^ 29 +
        ((362553339900463/335544320000000000000 : Real)) * tt ^ 3 * (1 - tt) ^ 28 +
        ((15251515978883884489/2097152000000000000000000 : Real)) * tt ^ 4 * (1 - tt) ^ 27 +
        ((197934538531031853013737/5242880000000000000000000000 : Real)) * tt ^ 5 * (1 - tt) ^ 26 +
        ((824380344872266407681677481/5242880000000000000000000000000 : Real)) * tt ^ 6 * (1 - tt) ^ 25 +
        ((7072940056701906630859787247699/13107200000000000000000000000000000 : Real)) * tt ^ 7 * (1 - tt) ^ 24 +
        ((50963023487179092326914832448096639/32768000000000000000000000000000000000 : Real)) * tt ^ 8 * (1 - tt) ^ 23 +
        ((781834919925393902994379034525432814531/204800000000000000000000000000000000000000 : Real)) * tt ^ 9 * (1 - tt) ^ 22 +
        ((4129236451504885745732661855383518105023243/512000000000000000000000000000000000000000000 : Real)) * tt ^ 10 * (1 - tt) ^ 21 +
        ((3784012430438988227154062479673020769437203/256000000000000000000000000000000000000000000 : Real)) * tt ^ 11 * (1 - tt) ^ 20 +
        ((2421242207481306438161199973239757908038304981/102400000000000000000000000000000000000000000000 : Real)) * tt ^ 12 * (1 - tt) ^ 19 +
        ((27164552680003432632477795327675445149740653767/819200000000000000000000000000000000000000000000 : Real)) * tt ^ 13 * (1 - tt) ^ 18 +
        ((167519155138547434348070176310015790755192450847/4096000000000000000000000000000000000000000000000 : Real)) * tt ^ 14 * (1 - tt) ^ 17 +
        ((5826381649127370345632994312386947698893704309179/131072000000000000000000000000000000000000000000000 : Real)) * tt ^ 15 * (1 - tt) ^ 16 +
        ((8728124837461481236387615179275903606276369372253/204800000000000000000000000000000000000000000000000 : Real)) * tt ^ 16 * (1 - tt) ^ 15 +
        ((1889626675954826641059352316631716573418250579180629/52428800000000000000000000000000000000000000000000000 : Real)) * tt ^ 17 * (1 - tt) ^ 14 +
        ((140821968863783138760635281474305814322095367461679871/5242880000000000000000000000000000000000000000000000000 : Real)) * tt ^ 18 * (1 - tt) ^ 13 +
        ((73832950164482112712504095037510757054147543197397163/4194304000000000000000000000000000000000000000000000000 : Real)) * tt ^ 19 * (1 - tt) ^ 12 +
        ((26511700092754015500668291143413640193516053052074330167/2621440000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 20 * (1 - tt) ^ 11 +
        ((26585668754067384947883119530487194422925770533658289293/5242880000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 21 * (1 - tt) ^ 10 +
        ((9250522376785107594667249209200919431911303692754401809367/4194304000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 22 * (1 - tt) ^ 9 +
        ((108198417976852286145456389019087595765802186438466448359/131072000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 23 * (1 - tt) ^ 8 +
        ((88279865069339566233747352737397930094404094891732056235199/335544320000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 24 * (1 - tt) ^ 7 +
        ((94498929683876288868400726425807187123845037919791061815041/1342177280000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 25 * (1 - tt) ^ 6 +
        ((2083386356208563425782904511981697140188800995691372873905883/134217728000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 26 * (1 - tt) ^ 5 +
        ((1473706730588485299482216406472937630121266406840210976891441/536870912000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 27 * (1 - tt) ^ 4 +
        ((1255942411118709467874968979437300823934548303970617027787699/3355443200000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 28 * (1 - tt) ^ 3 +
        ((158661809773582697449820571267663758948304614785713952529199/4294967296000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 29 * (1 - tt) ^ 2 +
        ((252158650844040385301495228153931264057368663608560934528443821/107374182400000000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 30 * (1 - tt) ^ 1 +
        ((484527035065747935142394950574056217806801367085593673673601/6710886400000000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 31 * 1 := by
    positivity
  have hident :
      (((29/107374182400 : Real)) * 1 +
        ((-5681/268435456000 : Real)) * eps ^ 1 +
        ((2368877/3355443200000 : Real)) * eps ^ 2 +
        ((-595225631/41943040000000 : Real)) * eps ^ 3 +
        ((258935451969/1310720000000000 : Real)) * eps ^ 4 +
        ((-33546960416641/16384000000000000 : Real)) * eps ^ 5 +
        ((1350259593171489/81920000000000000 : Real)) * eps ^ 6 +
        ((-108246451098533523/1024000000000000000 : Real)) * eps ^ 7 +
        ((7012950307174891199/12800000000000000000 : Real)) * eps ^ 8 +
        ((-922764260847477786493/400000000000000000000 : Real)) * eps ^ 9 +
        ((39292417171488147375107/5000000000000000000000 : Real)) * eps ^ 10 +
        ((-532241809388443771151/25000000000000000000 : Real)) * eps ^ 11 +
        ((1099346323466677961941/25000000000000000000 : Real)) * eps ^ 12 +
        ((-12349579143109161903/200000000000000000 : Real)) * eps ^ 13 +
        ((809295380439780553/25000000000000000 : Real)) * eps ^ 14 +
        ((362740068438042993/4000000000000000 : Real)) * eps ^ 15 +
        ((-4259019242061291/15625000000000 : Real)) * eps ^ 16 +
        ((14001817943812743/40000000000000 : Real)) * eps ^ 17 +
        ((-4614070990342161/20000000000000 : Real)) * eps ^ 18 +
        ((75347710892769/400000000000 : Real)) * eps ^ 19 +
        ((-113793627698133/250000000000 : Real)) * eps ^ 20 +
        ((277240021173/2500000000 : Real)) * eps ^ 21 +
        ((22880882334063/10000000000 : Real)) * eps ^ 22 +
        ((-54733116969/10000000 : Real)) * eps ^ 23 +
        ((116261530719/20000000 : Real)) * eps ^ 24 +
        ((-1573597377/400000 : Real)) * eps ^ 25 +
        ((764084027/200000 : Real)) * eps ^ 26 +
        ((-13371137/4000 : Real)) * eps ^ 27 +
        ((3784/125 : Real)) * eps ^ 28 +
        ((-16163/20 : Real)) * eps ^ 29 +
        ((-2971/100 : Real)) * eps ^ 30 +
        ((-30 : Real)) * eps ^ 31) =
        (((29/107374182400 : Real)) * 1 * (1 - tt) ^ 31 +
        ((432457/53687091200000 : Real)) * tt ^ 1 * (1 - tt) ^ 30 +
        ((15599344893/134217728000000000 : Real)) * tt ^ 2 * (1 - tt) ^ 29 +
        ((362553339900463/335544320000000000000 : Real)) * tt ^ 3 * (1 - tt) ^ 28 +
        ((15251515978883884489/2097152000000000000000000 : Real)) * tt ^ 4 * (1 - tt) ^ 27 +
        ((197934538531031853013737/5242880000000000000000000000 : Real)) * tt ^ 5 * (1 - tt) ^ 26 +
        ((824380344872266407681677481/5242880000000000000000000000000 : Real)) * tt ^ 6 * (1 - tt) ^ 25 +
        ((7072940056701906630859787247699/13107200000000000000000000000000000 : Real)) * tt ^ 7 * (1 - tt) ^ 24 +
        ((50963023487179092326914832448096639/32768000000000000000000000000000000000 : Real)) * tt ^ 8 * (1 - tt) ^ 23 +
        ((781834919925393902994379034525432814531/204800000000000000000000000000000000000000 : Real)) * tt ^ 9 * (1 - tt) ^ 22 +
        ((4129236451504885745732661855383518105023243/512000000000000000000000000000000000000000000 : Real)) * tt ^ 10 * (1 - tt) ^ 21 +
        ((3784012430438988227154062479673020769437203/256000000000000000000000000000000000000000000 : Real)) * tt ^ 11 * (1 - tt) ^ 20 +
        ((2421242207481306438161199973239757908038304981/102400000000000000000000000000000000000000000000 : Real)) * tt ^ 12 * (1 - tt) ^ 19 +
        ((27164552680003432632477795327675445149740653767/819200000000000000000000000000000000000000000000 : Real)) * tt ^ 13 * (1 - tt) ^ 18 +
        ((167519155138547434348070176310015790755192450847/4096000000000000000000000000000000000000000000000 : Real)) * tt ^ 14 * (1 - tt) ^ 17 +
        ((5826381649127370345632994312386947698893704309179/131072000000000000000000000000000000000000000000000 : Real)) * tt ^ 15 * (1 - tt) ^ 16 +
        ((8728124837461481236387615179275903606276369372253/204800000000000000000000000000000000000000000000000 : Real)) * tt ^ 16 * (1 - tt) ^ 15 +
        ((1889626675954826641059352316631716573418250579180629/52428800000000000000000000000000000000000000000000000 : Real)) * tt ^ 17 * (1 - tt) ^ 14 +
        ((140821968863783138760635281474305814322095367461679871/5242880000000000000000000000000000000000000000000000000 : Real)) * tt ^ 18 * (1 - tt) ^ 13 +
        ((73832950164482112712504095037510757054147543197397163/4194304000000000000000000000000000000000000000000000000 : Real)) * tt ^ 19 * (1 - tt) ^ 12 +
        ((26511700092754015500668291143413640193516053052074330167/2621440000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 20 * (1 - tt) ^ 11 +
        ((26585668754067384947883119530487194422925770533658289293/5242880000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 21 * (1 - tt) ^ 10 +
        ((9250522376785107594667249209200919431911303692754401809367/4194304000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 22 * (1 - tt) ^ 9 +
        ((108198417976852286145456389019087595765802186438466448359/131072000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 23 * (1 - tt) ^ 8 +
        ((88279865069339566233747352737397930094404094891732056235199/335544320000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 24 * (1 - tt) ^ 7 +
        ((94498929683876288868400726425807187123845037919791061815041/1342177280000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 25 * (1 - tt) ^ 6 +
        ((2083386356208563425782904511981697140188800995691372873905883/134217728000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 26 * (1 - tt) ^ 5 +
        ((1473706730588485299482216406472937630121266406840210976891441/536870912000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 27 * (1 - tt) ^ 4 +
        ((1255942411118709467874968979437300823934548303970617027787699/3355443200000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 28 * (1 - tt) ^ 3 +
        ((158661809773582697449820571267663758948304614785713952529199/4294967296000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 29 * (1 - tt) ^ 2 +
        ((252158650844040385301495228153931264057368663608560934528443821/107374182400000000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 30 * (1 - tt) ^ 1 +
        ((484527035065747935142394950574056217806801367085593673673601/6710886400000000000000000000000000000000000000000000000000000000000000 : Real)) * tt ^ 31 * 1) := by
    dsimp [tt]
    ring_nf
  rwa [hident]

private lemma endpoint_Delta_quotient_nonneg {eps : Real}
    (he0 : 0 <= eps) (he1 : eps <= 3 / 200) :
    0 <=
        ((81/5767168 : Real)) * 1 +
        ((-3585/7929856 : Real)) * eps ^ 1 +
        ((276075/43614208 : Real)) * eps ^ 2 +
        ((-744321/14992384 : Real)) * eps ^ 3 +
        ((1220198247/5277319168 : Real)) * eps ^ 4 +
        ((-1083772155/1814078464 : Real)) * eps ^ 5 +
        ((4817011455/9977431552 : Real)) * eps ^ 6 +
        ((23810826425/13718968384 : Real)) * eps ^ 7 +
        ((-14879292531579/2414538435584 : Real)) * eps ^ 8 +
        ((435640385589263/36519893838208 : Real)) * eps ^ 9 +
        ((-3705943632987/150908652224 : Real)) * eps ^ 10 +
        ((23810826425/857435524 : Real)) * eps ^ 11 +
        ((55879251855/1247178944 : Real)) * eps ^ 12 +
        ((-1083772155/7086244 : Real)) * eps ^ 13 +
        ((50535075/322102 : Real)) * eps ^ 14 +
        ((-2977284/14641 : Real)) * eps ^ 15 +
        ((2562605/10648 : Real)) * eps ^ 16 +
        ((-3585/121 : Real)) * eps ^ 17 +
        ((790/11 : Real)) * eps ^ 18 +
        ((2 : Real)) * eps ^ 20 := by
  let tt : Real := (200 / 3) * eps
  have htt0 : 0 <= tt := by
    dsimp [tt]
    positivity
  have htt1 : tt <= 1 := by
    dsimp [tt]
    nlinarith
  have h1tt0 : 0 <= 1 - tt := by linarith
  have hbern : 0 <=
        ((81/5767168 : Real)) * 1 * (1 - tt) ^ 20 +
        ((86949/317194240 : Real)) * tt ^ 1 * (1 - tt) ^ 19 +
        ((177327207/69782732800 : Real)) * tt ^ 2 * (1 - tt) ^ 18 +
        ((3568711621041/239878144000000 : Real)) * tt ^ 3 * (1 - tt) ^ 17 +
        ((520910151395992407/8443710668800000000 : Real)) * tt ^ 4 * (1 - tt) ^ 16 +
        ((22362118214284218807/116101021696000000000 : Real)) * tt ^ 5 * (1 - tt) ^ 15 +
        ((59995788470533523880639/127711123865600000000000 : Real)) * tt ^ 6 * (1 - tt) ^ 14 +
        ((6438227165636146628670189/7024111812608000000000000 : Real)) * tt ^ 7 * (1 - tt) ^ 13 +
        ((8981169981273673460154650870181/6181218395095040000000000000000 : Real)) * tt ^ 8 * (1 - tt) ^ 12 +
        ((35335022706812639871042868297033929/18698185645162496000000000000000000 : Real)) * tt ^ 9 * (1 - tt) ^ 11 +
        ((344660491628398332837442276698134907/169983505865113600000000000000000000 : Real)) * tt ^ 10 * (1 - tt) ^ 10 +
        ((19100413738596587749301377092283893/10623969116569600000000000000000000 : Real)) * tt ^ 11 * (1 - tt) ^ 9 +
        ((1788363446044777133538385444562852663241/1359868046920908800000000000000000000000 : Real)) * tt ^ 12 * (1 - tt) ^ 8 +
        ((13416278749199924946186565595761100910567/16998350586511360000000000000000000000000 : Real)) * tt ^ 13 * (1 - tt) ^ 7 +
        ((130836707374198991473585739486265797580237/339967011730227200000000000000000000000000 : Real)) * tt ^ 14 * (1 - tt) ^ 6 +
        ((31896649702212086936516990547238600638654783/212479382331392000000000000000000000000000000 : Real)) * tt ^ 15 * (1 - tt) ^ 5 +
        ((12441090937369329674107240161625164225241190811/271973609384181760000000000000000000000000000000 : Real)) * tt ^ 16 * (1 - tt) ^ 4 +
        ((71357713899019384302884172107693891414243959749/6799340234604544000000000000000000000000000000000 : Real)) * tt ^ 17 * (1 - tt) ^ 3 +
        ((1159575615259092107405079802655856440329589390721/679934023460454400000000000000000000000000000000000 : Real)) * tt ^ 18 * (1 - tt) ^ 2 +
        ((59502184835041846022052551075929229202685483371/339967011730227200000000000000000000000000000000000 : Real)) * tt ^ 19 * (1 - tt) ^ 1 +
        ((12762069607208234027338823371920814776995981211139011/1495854851612999680000000000000000000000000000000000000000 : Real)) * tt ^ 20 * 1 := by
    positivity
  have hident :
      (((81/5767168 : Real)) * 1 +
        ((-3585/7929856 : Real)) * eps ^ 1 +
        ((276075/43614208 : Real)) * eps ^ 2 +
        ((-744321/14992384 : Real)) * eps ^ 3 +
        ((1220198247/5277319168 : Real)) * eps ^ 4 +
        ((-1083772155/1814078464 : Real)) * eps ^ 5 +
        ((4817011455/9977431552 : Real)) * eps ^ 6 +
        ((23810826425/13718968384 : Real)) * eps ^ 7 +
        ((-14879292531579/2414538435584 : Real)) * eps ^ 8 +
        ((435640385589263/36519893838208 : Real)) * eps ^ 9 +
        ((-3705943632987/150908652224 : Real)) * eps ^ 10 +
        ((23810826425/857435524 : Real)) * eps ^ 11 +
        ((55879251855/1247178944 : Real)) * eps ^ 12 +
        ((-1083772155/7086244 : Real)) * eps ^ 13 +
        ((50535075/322102 : Real)) * eps ^ 14 +
        ((-2977284/14641 : Real)) * eps ^ 15 +
        ((2562605/10648 : Real)) * eps ^ 16 +
        ((-3585/121 : Real)) * eps ^ 17 +
        ((790/11 : Real)) * eps ^ 18 +
        ((2 : Real)) * eps ^ 20) =
        (((81/5767168 : Real)) * 1 * (1 - tt) ^ 20 +
        ((86949/317194240 : Real)) * tt ^ 1 * (1 - tt) ^ 19 +
        ((177327207/69782732800 : Real)) * tt ^ 2 * (1 - tt) ^ 18 +
        ((3568711621041/239878144000000 : Real)) * tt ^ 3 * (1 - tt) ^ 17 +
        ((520910151395992407/8443710668800000000 : Real)) * tt ^ 4 * (1 - tt) ^ 16 +
        ((22362118214284218807/116101021696000000000 : Real)) * tt ^ 5 * (1 - tt) ^ 15 +
        ((59995788470533523880639/127711123865600000000000 : Real)) * tt ^ 6 * (1 - tt) ^ 14 +
        ((6438227165636146628670189/7024111812608000000000000 : Real)) * tt ^ 7 * (1 - tt) ^ 13 +
        ((8981169981273673460154650870181/6181218395095040000000000000000 : Real)) * tt ^ 8 * (1 - tt) ^ 12 +
        ((35335022706812639871042868297033929/18698185645162496000000000000000000 : Real)) * tt ^ 9 * (1 - tt) ^ 11 +
        ((344660491628398332837442276698134907/169983505865113600000000000000000000 : Real)) * tt ^ 10 * (1 - tt) ^ 10 +
        ((19100413738596587749301377092283893/10623969116569600000000000000000000 : Real)) * tt ^ 11 * (1 - tt) ^ 9 +
        ((1788363446044777133538385444562852663241/1359868046920908800000000000000000000000 : Real)) * tt ^ 12 * (1 - tt) ^ 8 +
        ((13416278749199924946186565595761100910567/16998350586511360000000000000000000000000 : Real)) * tt ^ 13 * (1 - tt) ^ 7 +
        ((130836707374198991473585739486265797580237/339967011730227200000000000000000000000000 : Real)) * tt ^ 14 * (1 - tt) ^ 6 +
        ((31896649702212086936516990547238600638654783/212479382331392000000000000000000000000000000 : Real)) * tt ^ 15 * (1 - tt) ^ 5 +
        ((12441090937369329674107240161625164225241190811/271973609384181760000000000000000000000000000000 : Real)) * tt ^ 16 * (1 - tt) ^ 4 +
        ((71357713899019384302884172107693891414243959749/6799340234604544000000000000000000000000000000000 : Real)) * tt ^ 17 * (1 - tt) ^ 3 +
        ((1159575615259092107405079802655856440329589390721/679934023460454400000000000000000000000000000000000 : Real)) * tt ^ 18 * (1 - tt) ^ 2 +
        ((59502184835041846022052551075929229202685483371/339967011730227200000000000000000000000000000000000 : Real)) * tt ^ 19 * (1 - tt) ^ 1 +
        ((12762069607208234027338823371920814776995981211139011/1495854851612999680000000000000000000000000000000000000000 : Real)) * tt ^ 20 * 1) := by
    dsimp [tt]
    ring_nf
  rwa [hident]

/-- Endpoint bound `p^3 - alpha^3 <= 139/100 eps` for the C11 scalar proof. -/
lemma endpoint_F_bound {eps p q alpha : Real}
    (he0 : 0 <= eps) (he1 : eps <= 3 / 200)
    (hp : p = 1 / 2 + eps) (hq : q = 1 / 2 - eps)
    (halpha11 : alpha ^ 11 = p * q ^ 10) :
    p ^ 3 - alpha ^ 3 <= (139 / 100) * eps := by
  have hbase0 : 0 <= p ^ 3 - (139 / 100) * eps := by
    rw [hp]
    ring_nf
    nlinarith [he0, he1]
  have hpow :
      (p ^ 3 - (139 / 100) * eps) ^ 11 <= (alpha ^ 3) ^ 11 := by
    rw [show (alpha ^ 3) ^ 11 = (alpha ^ 11) ^ 3 by ring, halpha11]
    have hb := endpoint_F_quotient_nonneg he0 he1
    rw [hp, hq]
    ring_nf
    nlinarith [mul_nonneg he0 hb]
  have hle : p ^ 3 - (139 / 100) * eps <= alpha ^ 3 :=
    (show Odd (11 : Nat) by norm_num).pow_le_pow.mp hpow
  linarith

/-- Endpoint bound `pq - alpha^2 <= 9/11 eps` for the C11 scalar proof. -/
lemma endpoint_Delta_upper {eps p q alpha : Real}
    (he0 : 0 <= eps) (he1 : eps <= 3 / 200)
    (hp : p = 1 / 2 + eps) (hq : q = 1 / 2 - eps)
    (halpha11 : alpha ^ 11 = p * q ^ 10) :
    p * q - alpha ^ 2 <= (9 / 11) * eps := by
  have hpq0 : 0 <= p * q - (9 / 11) * eps := by
    rw [hp, hq]
    ring_nf
    nlinarith [he0, he1]
  have hpow :
      (p * q - (9 / 11) * eps) ^ 11 <= (alpha ^ 2) ^ 11 := by
    rw [show (alpha ^ 2) ^ 11 = (alpha ^ 11) ^ 2 by ring, halpha11]
    have hb := endpoint_Delta_quotient_nonneg he0 he1
    rw [hp, hq]
    ring_nf
    nlinarith [mul_nonneg (sq_nonneg eps) hb]
  have hle : p * q - (9 / 11) * eps <= alpha ^ 2 :=
    (show Odd (11 : Nat) by norm_num).pow_le_pow.mp hpow
  linarith

/-- The endpoint `Delta = pq - alpha^2` is nonnegative for
`alpha^11 = p q^10` in the C11 band. -/
lemma endpoint_Delta_nonneg {eps p q alpha : Real}
    (he0 : 0 <= eps) (he1 : eps <= 3 / 200)
    (hp : p = 1 / 2 + eps) (hq : q = 1 / 2 - eps)
    (halpha11 : alpha ^ 11 = p * q ^ 10) :
    0 <= p * q - alpha ^ 2 := by
  have hp0 : 0 <= p := by rw [hp]; nlinarith
  have hq0 : 0 <= q := by rw [hq]; nlinarith
  have hqle : q <= p := by rw [hp, hq]; nlinarith
  have hpq0 : 0 <= p * q := mul_nonneg hp0 hq0
  have hqpow : q ^ 9 <= p ^ 9 :=
    (show Odd (9 : Nat) by norm_num).pow_le_pow.mpr hqle
  have hpow_nonneg : 0 <= p ^ 2 * q ^ 11 * (p ^ 9 - q ^ 9) :=
    mul_nonneg (mul_nonneg (sq_nonneg p) (pow_nonneg hq0 11)) (by linarith)
  have hpow :
      (alpha ^ 2) ^ 11 <= (p * q) ^ 11 := by
    rw [show (alpha ^ 2) ^ 11 = (alpha ^ 11) ^ 2 by ring, halpha11]
    nlinarith
  have hle : alpha ^ 2 <= p * q :=
    (show Odd (11 : Nat) by norm_num).pow_le_pow.mp hpow
  linarith

/-- The full one-variable endpoint estimate at `ell = p` used by the C11
low-band scalar proof. -/
lemma endpoint_scalar_bound {eps p q alpha theta : Real}
    (he0 : 0 <= eps) (he1 : eps <= 3 / 200)
    (hp : p = 1 / 2 + eps) (hq : q = 1 / 2 - eps)
    (halpha11 : alpha ^ 11 = p * q ^ 10)
    (htheta :
      (3 / 2) * ((64 / 65) ^ 2) * (eps + (3 / 2) * eps ^ 2) <= theta) :
    p ^ 3 - alpha ^ 3 +
        Real.sqrt (p * q - alpha ^ 2) * (p * q - alpha ^ 2) <= theta := by
  have hF := endpoint_F_bound he0 he1 hp hq halpha11
  have hD := endpoint_Delta_upper he0 he1 hp hq halpha11
  have hD0 := endpoint_Delta_nonneg he0 he1 hp hq halpha11
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

private lemma eleventh_sub_ge_scale_cubic_sub_high
    {p y x : Real} (hp0 : 0 <= p) (hpy : p <= y) (hyx : y <= x) :
    11 * p ^ 8 * (x ^ 3 - y ^ 3) <= 3 * (x ^ 11 - y ^ 11) := by
  have hx0 : 0 <= x := hp0.trans (hpy.trans hyx)
  have hy0 : 0 <= y := hp0.trans hpy
  have hpx : p <= x := hpy.trans hyx
  have hxy : 0 <= x - y := by linarith
  have hmargin : 0 <= p ^ 8 * (2 * x ^ 2 - x * y - y ^ 2) := by
    have hquad : 0 <= 2 * x ^ 2 - x * y - y ^ 2 := by
      have hfactor := mul_nonneg (sub_nonneg.mpr hyx)
        (by nlinarith : 0 <= 2 * x + y)
      nlinarith
    exact mul_nonneg (pow_nonneg hp0 8) hquad
  have t0 : p ^ 8 * x ^ 2 <= x ^ 10 := by
    have h : p ^ 8 <= x ^ 8 := pow_le_pow_left₀ hp0 hpx 8
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg x)
    nlinarith
  have t1 : p ^ 8 * x ^ 2 <= x ^ 9 * y := by
    have h : p ^ 8 <= x ^ 7 * y := by
      simpa using p_pow_add_le_mul_pow hp0 hpx hpy 7 1
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg x)
    nlinarith
  have t2 : p ^ 8 * x ^ 2 <= x ^ 8 * y ^ 2 := by
    have h : p ^ 8 <= x ^ 6 * y ^ 2 := by
      simpa using p_pow_add_le_mul_pow hp0 hpx hpy 6 2
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg x)
    nlinarith
  have t3 : p ^ 8 * x ^ 2 <= x ^ 7 * y ^ 3 := by
    have h : p ^ 8 <= x ^ 5 * y ^ 3 := by
      simpa using p_pow_add_le_mul_pow hp0 hpx hpy 5 3
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg x)
    nlinarith
  have t4 : p ^ 8 * x ^ 2 <= x ^ 6 * y ^ 4 := by
    have h : p ^ 8 <= x ^ 4 * y ^ 4 := by
      simpa using p_pow_add_le_mul_pow hp0 hpx hpy 4 4
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg x)
    nlinarith
  have t5 : p ^ 8 * x ^ 2 <= x ^ 5 * y ^ 5 := by
    have h : p ^ 8 <= x ^ 3 * y ^ 5 := by
      simpa using p_pow_add_le_mul_pow hp0 hpx hpy 3 5
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg x)
    nlinarith
  have t6 : p ^ 8 * x ^ 2 <= x ^ 4 * y ^ 6 := by
    have h : p ^ 8 <= x ^ 2 * y ^ 6 := by
      simpa using p_pow_add_le_mul_pow hp0 hpx hpy 2 6
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg x)
    nlinarith
  have t7 : p ^ 8 * x ^ 2 <= x ^ 3 * y ^ 7 := by
    have h : p ^ 8 <= x * y ^ 7 := by
      simpa using p_pow_add_le_mul_pow hp0 hpx hpy 1 7
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg x)
    nlinarith
  have t8 : p ^ 8 * x ^ 2 <= x ^ 2 * y ^ 8 := by
    have h : p ^ 8 <= y ^ 8 := pow_le_pow_left₀ hp0 hpy 8
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg x)
    nlinarith
  have t9 : p ^ 8 * (x * y) <= x * y ^ 9 := by
    have h : p ^ 8 <= y ^ 8 := pow_le_pow_left₀ hp0 hpy 8
    have hm := mul_le_mul_of_nonneg_right h (mul_nonneg hx0 hy0)
    nlinarith
  have t10 : p ^ 8 * y ^ 2 <= y ^ 10 := by
    have h : p ^ 8 <= y ^ 8 := pow_le_pow_left₀ hp0 hpy 8
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg y)
    nlinarith
  have hsum :
      11 * p ^ 8 * (x ^ 2 + x * y + y ^ 2) <=
        3 * (x ^ 10 + x ^ 9 * y + x ^ 8 * y ^ 2 + x ^ 7 * y ^ 3 +
          x ^ 6 * y ^ 4 + x ^ 5 * y ^ 5 + x ^ 4 * y ^ 6 +
          x ^ 3 * y ^ 7 + x ^ 2 * y ^ 8 + x * y ^ 9 + y ^ 10) := by
    nlinarith [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, hmargin]
  have hfac11 :
      x ^ 11 - y ^ 11 = (x - y) *
        (x ^ 10 + x ^ 9 * y + x ^ 8 * y ^ 2 + x ^ 7 * y ^ 3 +
          x ^ 6 * y ^ 4 + x ^ 5 * y ^ 5 + x ^ 4 * y ^ 6 +
          x ^ 3 * y ^ 7 + x ^ 2 * y ^ 8 + x * y ^ 9 + y ^ 10) := by
    ring
  have hfac3 : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by
    ring
  nlinarith [mul_le_mul_of_nonneg_left hsum hxy]

private lemma eleventh_sub_le_scale_cubic_sub_low
    {p y x : Real} (hy0 : 0 <= y) (hyx : y <= x) (hxp : x <= p) :
    3 * (x ^ 11 - y ^ 11) <= 11 * p ^ 8 * (x ^ 3 - y ^ 3) := by
  have hx0 : 0 <= x := hy0.trans hyx
  have hp0 : 0 <= p := hx0.trans hxp
  have hyp : y <= p := hyx.trans hxp
  have hxy : 0 <= x - y := by linarith
  have hmargin : 0 <= p ^ 8 * (x ^ 2 + x * y - 2 * y ^ 2) := by
    have hquad : 0 <= x ^ 2 + x * y - 2 * y ^ 2 := by
      have hfactor := mul_nonneg (sub_nonneg.mpr hyx)
        (by nlinarith : 0 <= x + 2 * y)
      nlinarith
    exact mul_nonneg (pow_nonneg hp0 8) hquad
  have t0 : x ^ 10 <= p ^ 8 * x ^ 2 := by
    have h : x ^ 8 <= p ^ 8 := pow_le_pow_left₀ hx0 hxp 8
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg x)
    nlinarith
  have t1 : x ^ 9 * y <= p ^ 8 * (x * y) := by
    have h : x ^ 8 <= p ^ 8 := pow_le_pow_left₀ hx0 hxp 8
    have hm := mul_le_mul_of_nonneg_right h (mul_nonneg hx0 hy0)
    nlinarith
  have t2 : x ^ 8 * y ^ 2 <= p ^ 8 * y ^ 2 := by
    have h : x ^ 8 <= p ^ 8 := pow_le_pow_left₀ hx0 hxp 8
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg y)
    nlinarith
  have t3 : x ^ 7 * y ^ 3 <= p ^ 8 * y ^ 2 := by
    have h : x ^ 7 * y <= p ^ 8 := by
      simpa using mul_pow_le_p_pow_add hx0 hy0 hxp hyp 7 1
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg y)
    nlinarith
  have t4 : x ^ 6 * y ^ 4 <= p ^ 8 * y ^ 2 := by
    have h : x ^ 6 * y ^ 2 <= p ^ 8 := by
      simpa using mul_pow_le_p_pow_add hx0 hy0 hxp hyp 6 2
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg y)
    nlinarith
  have t5 : x ^ 5 * y ^ 5 <= p ^ 8 * y ^ 2 := by
    have h : x ^ 5 * y ^ 3 <= p ^ 8 := by
      simpa using mul_pow_le_p_pow_add hx0 hy0 hxp hyp 5 3
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg y)
    nlinarith
  have t6 : x ^ 4 * y ^ 6 <= p ^ 8 * y ^ 2 := by
    have h : x ^ 4 * y ^ 4 <= p ^ 8 := by
      simpa using mul_pow_le_p_pow_add hx0 hy0 hxp hyp 4 4
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg y)
    nlinarith
  have t7 : x ^ 3 * y ^ 7 <= p ^ 8 * y ^ 2 := by
    have h : x ^ 3 * y ^ 5 <= p ^ 8 := by
      simpa using mul_pow_le_p_pow_add hx0 hy0 hxp hyp 3 5
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg y)
    nlinarith
  have t8 : x ^ 2 * y ^ 8 <= p ^ 8 * y ^ 2 := by
    have h : x ^ 2 * y ^ 6 <= p ^ 8 := by
      simpa using mul_pow_le_p_pow_add hx0 hy0 hxp hyp 2 6
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg y)
    nlinarith
  have t9 : x * y ^ 9 <= p ^ 8 * y ^ 2 := by
    have h : x * y ^ 7 <= p ^ 8 := by
      simpa using mul_pow_le_p_pow_add hx0 hy0 hxp hyp 1 7
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg y)
    nlinarith
  have t10 : y ^ 10 <= p ^ 8 * y ^ 2 := by
    have h : y ^ 8 <= p ^ 8 := pow_le_pow_left₀ hy0 hyp 8
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg y)
    nlinarith
  have hsum :
      3 * (x ^ 10 + x ^ 9 * y + x ^ 8 * y ^ 2 + x ^ 7 * y ^ 3 +
          x ^ 6 * y ^ 4 + x ^ 5 * y ^ 5 + x ^ 4 * y ^ 6 +
          x ^ 3 * y ^ 7 + x ^ 2 * y ^ 8 + x * y ^ 9 + y ^ 10) <=
        11 * p ^ 8 * (x ^ 2 + x * y + y ^ 2) := by
    nlinarith [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, hmargin]
  have hfac11 :
      x ^ 11 - y ^ 11 = (x - y) *
        (x ^ 10 + x ^ 9 * y + x ^ 8 * y ^ 2 + x ^ 7 * y ^ 3 +
          x ^ 6 * y ^ 4 + x ^ 5 * y ^ 5 + x ^ 4 * y ^ 6 +
          x ^ 3 * y ^ 7 + x ^ 2 * y ^ 8 + x * y ^ 9 + y ^ 10) := by
    ring
  have hfac3 : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by
    ring
  nlinarith [mul_le_mul_of_nonneg_left hsum hxy]

/-- Algebraic reduction from the principal root `ell` to the endpoint
`ell = p` for the C11 scalar comparison. -/
lemma ell_reduction_bound
    {p q ell alpha0 alpha : Real}
    (hp0 : 0 <= p) (hp_half : 1 / 2 <= p)
    (ha00 : 0 <= alpha0) (hpell : p <= ell)
    (ha011 : alpha0 ^ 11 = p * q ^ 10)
    (ha11 : alpha ^ 11 = ell ^ 11 - p ^ 11 + p * q ^ 10)
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
    have hpow : alpha0 ^ 11 <= alpha ^ 11 := by
      rw [ha011, ha11]
      have hpell11 : p ^ 11 <= ell ^ 11 := pow_le_pow_left₀ hp0 hpell 11
      nlinarith
    exact (show Odd (11 : Nat) by norm_num).pow_le_pow.mp hpow
  have halpha_le_p : alpha <= p := by
    have hpell2 : p ^ 2 <= ell ^ 2 := pow_le_pow_left₀ hp0 hpell 2
    have hp_le_one : p <= 1 := by nlinarith
    have halpha_sq : alpha ^ 2 <= p ^ 2 := by nlinarith
    by_contra hnot
    have hlt : p < alpha := lt_of_not_ge hnot
    have hslt : p ^ 2 < alpha ^ 2 :=
      pow_lt_pow_left₀ hlt hp0 (by norm_num : (2 : Nat) ≠ 0)
    nlinarith
  have hdiff : alpha ^ 11 - alpha0 ^ 11 = ell ^ 11 - p ^ 11 := by
    rw [ha011, ha11]
    ring
  have hhigh :=
    eleventh_sub_ge_scale_cubic_sub_high (p := p) (y := p) (x := ell)
      hp0 le_rfl hpell
  have hlow :=
    eleventh_sub_le_scale_cubic_sub_low (p := p) (y := alpha0) (x := alpha)
      ha00 ha0a halpha_le_p
  have hcubic :
      ell ^ 3 - p ^ 3 <= alpha ^ 3 - alpha0 ^ 3 := by
    have hscale_pos : 0 < 11 * p ^ 8 := by positivity
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

/-- Same monotonicity step, phrased in the eleventh-power comparison that
arises from `alpha^11 < z^11`. -/
lemma cubic_capacity_strict_decreases_of_eleventh
    {S alpha z : Real}
    (halpha0 : 0 <= alpha) (hz0 : 0 <= z)
    (heleventh : alpha ^ 11 < z ^ 11)
    (hbudget : 0 <= S - z ^ 2) :
    Real.sqrt (S - z ^ 2) * (S - z ^ 2) - z ^ 3 <
      Real.sqrt (S - alpha ^ 2) * (S - alpha ^ 2) - alpha ^ 3 := by
  have hlt : alpha < z := by
    exact (show Odd (11 : Nat) by norm_num).pow_lt_pow.mp heleventh
  exact cubic_capacity_strict_decreases halpha0 hz0 hlt hbudget

/-- The C11 target follows from the spectral negative-mass estimate.

In the paper, `ell` is the principal eigenvalue and `N11` is the eleventh-power
mass of the negative non-principal eigenvalues.  The analytic spectral proof
supplies `trace >= ell^11 - N11` and
`N11 <= ell^11 - p^11 + p*q^10`; this lemma performs the final graphon-level
algebraic step.
-/
theorem cycle_bound_of_negative_mass_bound
    {ell N11 q : Real}
    (hq : q = 1 - edgeDensity W mu)
    (htrace : ell ^ 11 - N11 <= trace mu (compPow mu W 10))
    (hN11 :
      N11 <= ell ^ 11 - edgeDensity W mu ^ 11 +
        edgeDensity W mu * q ^ 10) :
    trace mu (compPow mu W 10) >=
      edgeDensity W mu ^ 11 - edgeDensity W mu * (1 - edgeDensity W mu) ^ 10 := by
  rw [hq] at hN11
  nlinarith

end C11
end LowBand
end OddCycleBound
