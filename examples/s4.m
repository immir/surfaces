
SetEchoInput(true);
Attach("surf.m");

P2111<D,a,b,c> := ProjectiveSpace(Rationals(), [2,1,1,1]);
S4 := Scheme(P2111, 16*D^2 - (a+b+c)*(-a+b+c)*(a-b+c)*(a+b-c));

S := Veronese(S4);

time C := Conics(S);
#C;
[ MinimalBasis(X) : X in C ];
[ Dimension(X) : X in C ];
[ Degree(Curve(X)) : X in C ];

R := BaseRing(C[1]);
R.4, MinimalPolynomial(R.4);
