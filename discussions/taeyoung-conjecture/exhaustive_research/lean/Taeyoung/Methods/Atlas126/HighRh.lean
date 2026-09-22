import Taeyoung.Methods.Atlas126.Convex

/-! The right/high high-density upper face, including its collapsed endpoints.
`x,d,u` here parameterize a unit cube; `degree` is the actual rooted degree. -/
namespace Taeyoung.Methods.Atlas126

noncomputable def highRhTarget (x d u : ℝ) : ℝ :=
  let q := x/3
  let p := 1-q
  let s := q+(p/2-q)*d
  let degree := 1-s
  let v := q+p*u
  let t := p-2*s+2*q*v
  scalarResidual p (target p) (betaHigh p) (gammaHigh p) 0 0 degree ((t+p)/2) t

end Taeyoung.Methods.Atlas126
