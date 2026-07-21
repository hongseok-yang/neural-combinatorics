import sympy as sp

q,p,lam,y = sp.symbols('q p lambda y')

print("=== m=3 identity ===")
g3 = p**3 - p*(1-p)**2
print("p^3-p(1-p)^2 - p(2p-1) =", sp.simplify(g3 - p*(2*p-1)))

print("\n=== C5 ===")
# Phi5 collected coefficient of ||g||^2 after square completion
# Phi5 = 4||Tg||^2 + (8q-5)<g,Tg> + (12q^2-15q+5)||g||^2
# complete square: 4(Tg + (8q-5)/8 g)^2 = 4||Tg||^2 + (8q-5)<g,Tg> + 4*((8q-5)/8)^2||g||^2
resid = (12*q**2-15*q+5) - 4*((8*q-5)/8)**2
print("residual coeff:", sp.simplify(resid), " expected 8q^2-10q+55/16:", sp.simplify(resid-(8*q**2-10*q+sp.Rational(55,16))))
disc = (-10)**2 - 4*8*sp.Rational(55,16)
print("discriminant of 8q^2-10q+55/16 =", disc)

print("\n=== C7 SOS identity ===")
D = 288*q**2-336*q+119
C = 24*q**3-42*q**2+28*q-7
N = 5184*q**6-18144*q**5+28602*q**4-25802*q**3+13874*q**2-4165*q+539
Pq = (6*lam**4+(12*q-7)*lam**3+(18*q**2-21*q+7)*lam**2
      +(24*q**3-42*q**2+28*q-7)*lam+30*q**4-70*q**3+70*q**2-35*q+7)
RHS = (6*(lam**2+(q-sp.Rational(7,12))*lam)**2
       + D/24*(lam+12*C/D)**2 + N/D)
print("P_q - RHS simplifies to:", sp.simplify(Pq-RHS))

print("\n=== D, 8N in y=1/2-q ===")
Dy = sp.expand(D.subs(q, sp.Rational(1,2)-y))
print("D(y) =", Dy)
N8y = sp.expand((8*N).subs(q, sp.Rational(1,2)-y))
print("8N(y) =", N8y)
print("D coeffs all >0:", all(c>0 for c in sp.Poly(Dy,y).all_coeffs()))
print("8N coeffs all >0:", all(c>0 for c in sp.Poly(N8y,y).all_coeffs()))

print("\n=== B_q min check ===")
Bq = 12*lam**2+(36*q-21)*lam+36*q**2-42*q+14
lstar = (7-12*q)/8
Bmin = sp.simplify(Bq.subs(lam,lstar))
print("B_q(lambda*) =", Bmin, " expected (144q^2-168q+77)/16:", sp.simplify(Bmin-(144*q**2-168*q+77)/16))
num = 144*q**2-168*q+77
print("144q^2-168q+77-29 =", sp.factor(num-29))
