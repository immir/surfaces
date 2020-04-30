
SetEchoInput(true);
Attach("surf.m");

P1112<a,b,c,D> := ProjectiveSpace(Rationals(), [1,1,1,2]);
S4 := Scheme(P1112, 16*D^2 - (a+b+c)*(-a+b+c)*(a-b+c)*(a+b-c));

S := Veronese(S4);

time C := Conics(S);
#C;
[ MinimalBasis(X) : X in C ];
[ Dimension(X) : X in C ];
[ Degree(Curve(X)) : X in C ];
