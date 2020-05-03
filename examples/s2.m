
SetEchoInput(true);
Attach("surf.m");

P4<a,b,c,k,l> := ProjectiveSpace(Rationals(), 4);
S2 := Scheme(P4, [
    4*k^2 - (2*b^2 + 2*c^2 - a^2),
    4*l^2 - (2*c^2 + 2*a^2 - b^2) ]);


time C := Conics(S2);
#C;
[ MinimalBasis(X) : X in C ];
[ Dimension(X) : X in C ];
[ Degree(Curve(X)) : X in C ];

