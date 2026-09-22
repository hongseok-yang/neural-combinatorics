import Taeyoung.Methods.Atlas126.JunctionPlane

namespace Taeyoung.Methods.Atlas126

/-- Closed cube coverage of the face `a=d`. Zero width intervals are included. -/
theorem highUpperD_cover (P : ℝ → ℝ → ℝ → Prop)
    (h1 : ∀ {x y z : ℝ}, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → 0 ≤ z → z ≤ 1 →
      P ((2+x)/3) (((2+x)/3)*y/2) ((((2+x)/3)*y/2)^2*z))
    (h2 : ∀ {x y z : ℝ}, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → 0 ≤ z → z ≤ 1 →
      P (1-(2*x/3)^2*y) (1-2*x/3)
        (2*(1-2*x/3)-(1-(2*x/3)^2*y)+((2*x/3)^2-(2*x/3)^2*y)*z))
    {p d t : ℝ} (hp0 : (2/3 : ℝ) ≤ p) (hp1 : p ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (ht0 : 0 ≤ t) (htD : t ≤ d^2)
    (hdT : d ≤ (t+p)/2) : P p d t := by
  by_cases hdp : d ≤ p/2
  · obtain ⟨y,hy0,hy1,hy⟩ := exists_unit_scale (by linarith : 0 ≤ p/2) hd0 hdp
    obtain ⟨z,hz0,hz1,hz⟩ := exists_unit_scale (sq_nonneg d) ht0 htD
    have hx0 : 0 ≤ 3*p-2 := by linarith
    have hx1 : 3*p-2 ≤ 1 := by linarith
    have h := h1 hx0 hx1 hy0 hy1 hz0 hz1
    have hpx : (2+(3*p-2))/3 = p := by ring
    have hdy : p*y/2 = d := by linarith only [hy]
    rw [hpx,hdy,hz] at h
    exact h
  · let s := 1-d
    let q := 1-p
    have hs0 : 0 ≤ s := by dsimp only [s]; linarith
    have hs1 : s ≤ (2/3 : ℝ) := by dsimp only [s]; linarith
    have hq0 : 0 ≤ q := by dsimp only [q]; linarith
    have hq1 : q ≤ s^2 := by dsimp only [q,s]; nlinarith only [htD,hdT]
    obtain ⟨x,hx0,hx1,hx⟩ := exists_unit_scale (by norm_num : (0 : ℝ) ≤ 2/3) hs0 hs1
    have hx' : 2*x/3 = s := by linarith only [hx]
    obtain ⟨y,hy0,hy1,hy⟩ := exists_unit_scale (sq_nonneg s) hq0 hq1
    have hgap : 0 ≤ s^2-q := sub_nonneg.mpr hq1
    have htLo : 0 ≤ t-(2*d-p) := by linarith only [hdT]
    have htHi : t-(2*d-p) ≤ s^2-q := by dsimp only [s,q]; nlinarith only [htD]
    obtain ⟨z,hz0,hz1,hz⟩ := exists_unit_scale hgap htLo htHi
    have h := h2 hx0 hx1 hy0 hy1 hz0 hz1
    rw [hx',hy] at h
    have hq : 1-q = p := by dsimp only [q]; ring
    have hs : 1-s = d := by dsimp only [s]; ring
    rw [hq,hs,hz] at h
    have he : 2*d-p+(t-(2*d-p)) = t := by ring
    rwa [he] at h

/-- Six closed cubes cover `a=(t+p)/2` in the high-density range. -/
theorem highUpperT_cover (P : ℝ → ℝ → ℝ → Prop)
    (hL : ∀ {x y z : ℝ}, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → 0 ≤ z → z ≤ 1 →
      let p := (2+x)/3
      let d := p/2+(1-p)*y
      P p d ((2*d-p)*(z/3)))
    (hH : ∀ {x y z : ℝ}, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → 0 ≤ z → z ≤ 1 →
      let p := (2+x)/3
      let d := p/2+(1-p)*y
      P p d ((2*d-p)*((1+2*z)/3)))
    (hLL : ∀ {x y z : ℝ}, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → 0 ≤ z → z ≤ 1 →
      let q := x/3
      let p := 1-q
      let s := q*y
      P p (1-s) (p-2*s+2*q*(q*z)))
    (hLH : ∀ {x y z : ℝ}, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → 0 ≤ z → z ≤ 1 →
      let q := x/3
      let p := 1-q
      let s := q*y
      P p (1-s) (p-2*s+2*q*(q+p*z)))
    (hRL : ∀ {x y z : ℝ}, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → 0 ≤ z → z ≤ 1 →
      let q := x/3
      let p := 1-q
      let s := q+(p/2-q)*y
      P p (1-s) (p-2*s+2*q*(q*z)))
    (hRH : ∀ {x y z : ℝ}, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → 0 ≤ z → z ≤ 1 →
      let q := x/3
      let p := 1-q
      let s := q+(p/2-q)*y
      P p (1-s) (p-2*s+2*q*(q+p*z)))
    {p d t : ℝ} (hp0 : (2/3 : ℝ) ≤ p) (hp1 : p ≤ 1)
    (hd1 : d ≤ 1) (ht0 : 0 ≤ t) (htp : t ≤ p)
    (hTd : (t+p)/2 ≤ d) (hLower : d+p-1 ≤ (t+p)/2) : P p d t := by
  let q := 1-p
  have hq0 : 0 ≤ q := by dsimp only [q]; linarith
  by_cases hdCut : d ≤ 1-p/2
  · have hLo : 0 ≤ d-p/2 := by linarith only [ht0,hTd]
    have hHi : d-p/2 ≤ q := by dsimp only [q]; linarith only [hdCut]
    obtain ⟨y,hy0,hy1,hy⟩ := exists_unit_scale hq0 hLo hHi
    have hgap : 0 ≤ 2*d-p := by linarith only [hLo]
    have htHi : t ≤ 2*d-p := by linarith only [hTd]
    obtain ⟨v,hv0,hv1,hv⟩ := exists_unit_scale hgap ht0 htHi
    have hx0 : 0 ≤ 3*p-2 := by linarith
    have hx1 : 3*p-2 ≤ 1 := by linarith
    have hpx : (2+(3*p-2))/3 = p := by ring
    have hdy : p/2+(1-p)*y = d := by change q*y = d-p/2 at hy; linarith only [hy]
    by_cases hvCut : v ≤ (1/3 : ℝ)
    · have hz0 : 0 ≤ 3*v := by linarith
      have hz1 : 3*v ≤ 1 := by linarith
      have h := hL hx0 hx1 hy0 hy1 hz0 hz1
      dsimp only at h
      rw [hpx,hdy] at h
      have he : 3*v/3 = v := by ring
      rwa [he,hv] at h
    · have hz0 : 0 ≤ (3*v-1)/2 := by linarith
      have hz1 : (3*v-1)/2 ≤ 1 := by linarith
      have h := hH hx0 hx1 hy0 hy1 hz0 hz1
      dsimp only at h
      rw [hpx,hdy] at h
      have he : (1+2*((3*v-1)/2))/3 = v := by ring
      rwa [he,hv] at h
  · let s := 1-d
    have hs0 : 0 ≤ s := by dsimp only [s]; linarith
    have hs1 : s ≤ p/2 := by dsimp only [s]; linarith
    have htLo : 0 ≤ t-(p-2*s) := by dsimp only [s]; linarith only [hLower]
    have htHi : t-(p-2*s) ≤ 2*q := by dsimp only [s,q]; linarith only [hTd]
    obtain ⟨v,hv0,hv1,hv⟩ := exists_unit_scale (by positivity : 0 ≤ 2*q) htLo htHi
    have hx0 : 0 ≤ 3*q := by positivity
    have hx1 : 3*q ≤ 1 := by dsimp only [q]; linarith
    have hxq : 3*q/3 = q := by ring
    have hqp : 1-q = p := by dsimp only [q]; ring
    have hsd : 1-s = d := by dsimp only [s]; ring
    have ht : p-2*s+2*q*v = t := by linarith only [hv]
    have hRight : 0 ≤ p/2-q := by dsimp only [q]; linarith
    have hVRight : v-q ≤ p := by dsimp only [q]; linarith only [hv1]
    rcases le_total s q with hsL | hsR
    · obtain ⟨y,hy0,hy1,hy⟩ := exists_unit_scale hq0 hs0 hsL
      rcases le_total v q with hvL | hvR
      · obtain ⟨z,hz0,hz1,hz⟩ := exists_unit_scale hq0 hv0 hvL
        have h := hLL hx0 hx1 hy0 hy1 hz0 hz1
        dsimp only at h
        rwa [hxq,hqp,hy,hz,hsd,ht] at h
      · obtain ⟨z,hz0,hz1,hz⟩ := exists_unit_scale (by linarith : 0 ≤ p)
          (sub_nonneg.mpr hvR) hVRight
        have hz' : q+p*z = v := by linarith only [hz]
        have h := hLH hx0 hx1 hy0 hy1 hz0 hz1
        dsimp only at h
        rwa [hxq,hqp,hy,hz',hsd,ht] at h
    · obtain ⟨y,hy0,hy1,hy⟩ := exists_unit_scale hRight (sub_nonneg.mpr hsR)
        (by linarith only [hs1] : s-q ≤ p/2-q)
      have hy' : q+(p/2-q)*y = s := by linarith only [hy]
      rcases le_total v q with hvL | hvR
      · obtain ⟨z,hz0,hz1,hz⟩ := exists_unit_scale hq0 hv0 hvL
        have h := hRL hx0 hx1 hy0 hy1 hz0 hz1
        dsimp only at h
        rwa [hxq,hqp,hy',hz,hsd,ht] at h
      · obtain ⟨z,hz0,hz1,hz⟩ := exists_unit_scale (by linarith : 0 ≤ p)
          (sub_nonneg.mpr hvR) hVRight
        have hz' : q+p*z = v := by linarith only [hz]
        have h := hRH hx0 hx1 hy0 hy1 hz0 hz1
        dsimp only at h
        rwa [hxq,hqp,hy',hz',hsd,ht] at h

end Taeyoung.Methods.Atlas126
