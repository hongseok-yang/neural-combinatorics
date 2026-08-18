import sympy as sp

q, s0, s1, s2, s3, s4 = sp.symbols('q s0 s1 s2 s3 s4')

# Path moments (Lemma 2.4)
x2 = q**2 + s0
x3 = q**3 + 2*q*s0 + s1
x4 = q**4 + 3*q**2*s0 + 2*q*s1 + s0**2 + s2
x5 = q**5 + 4*q**3*s0 + 3*q**2*s1 + 3*q*s0**2 + 2*q*s2 + 2*s0*s1 + s3
x6 = (q**6 + 5*q**4*s0 + 4*q**3*s1 + 6*q**2*s0**2 + 3*q**2*s2
      + 6*q*s0*s1 + 2*q*s3 + s0**3 + 2*s0*s2 + s1**2 + s4)

# Phi7 path-form (eq Phi7-path)
Phi7_path = (6*x6 - 7*x5 + 7*(1-q)*x4 + 7*(2*q-1)*x3 + 7*(q**2-3*q+1)*x2
             + 7*x2**2 - 7*x2*x3 - 6*q**6 + 21*q**5 - 35*q**4 + 28*q**3 - 7*q**2)

# Phi7 in s (eq Phi7-s)
Phi7_s = (6*s4 + (12*q-7)*s3 + (18*q**2-21*q+7)*s2 + (24*q**3-42*q**2+28*q-7)*s1
          + (30*q**4-70*q**3+70*q**2-35*q+7)*s0 + 12*s0*s2 + (36*q-21)*s0*s1
          + (36*q**2-42*q+14)*s0**2 + 6*s0**3 + 6*s1**2)

print('Phi7_path == Phi7_s :', sp.expand(Phi7_path - Phi7_s) == 0)

# Decomposition Phi7 = Lpart + 6 s1^2 + s0*B + 6 s0^3
Lpart = (6*s4 + (12*q-7)*s3 + (18*q**2-21*q+7)*s2 + (24*q**3-42*q**2+28*q-7)*s1
         + (30*q**4-70*q**3+70*q**2-35*q+7)*s0)
B = 12*s2 + (36*q-21)*s1 + (36*q**2-42*q+14)*s0
print('Phi7 = Lpart+6s1^2+s0*B+6s0^3 :',
      sp.expand(Phi7_s - (Lpart + 6*s1**2 + s0*B + 6*s0**3)) == 0)

# Star identity: 24 D Lpart == D Sq1 + Sq2 + 24 N s0
D = 288*q**2 - 336*q + 119
C = 24*q**3 - 42*q**2 + 28*q - 7
N_paper = 5184*q**6 - 18144*q**5 + 28602*q**4 - 25802*q**3 + 13874*q**2 - 4165*q + 539
N_def = D*(30*q**4-70*q**3+70*q**2-35*q+7) - 6*C**2
print('N_paper == N_def :', sp.expand(N_paper - N_def) == 0)

Sq1 = 144*s4 + 24*(12*q-7)*s3 + (12*q-7)**2*s2
Sq2 = D**2*s2 + 24*D*C*s1 + 144*C**2*s0
print('star 24 D Lpart == D Sq1 + Sq2 + 24 N s0 :',
      sp.expand(24*D*Lpart - (D*Sq1 + Sq2 + 24*N_paper*s0)) == 0)

# B positivity SOS: 48 B == SqB + 3*(144q^2-168q+77) s0
SqB = 576*s2 + 48*(36*q-21)*s1 + (36*q-21)**2*s0
print('48 B == SqB + 3(144q^2-168q+77) s0 :',
      sp.expand(48*B - (SqB + 3*(144*q**2-168*q+77)*s0)) == 0)

# 8N in y = 1/2 - q (should have all positive coeffs)
y = sp.symbols('y')
print('8N(y) =', sp.expand(8*N_paper.subs(q, sp.Rational(1, 2)-y)))

# small algebra facts
print('144q^2-168q+77 - ((12q-7)^2+28) :', sp.expand(144*q**2-168*q+77 - ((12*q-7)**2+28)))
print('D as (12q-7)^2 + ... :', sp.expand(288*q**2-336*q+119 - (144*q**2-168*q+49)), '+ leftover',
      sp.expand(288*q**2-336*q+119 - (144*q**2-168*q+49)))
