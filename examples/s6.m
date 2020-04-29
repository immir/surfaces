
SetEchoInput(true);
Attach("surf.m");

P211111<D,a,b,c,k,l> := ProjectiveSpace(Rationals(), [2,1,1,1,1,1]);
S6 := Scheme(P211111, [
   16*D^2 - (a+b+c)*(-a+b+c)*(a-b+c)*(a+b-c),
   4*k^2 - (2*b^2 + 2*c^2 - a^2),
   4*l^2 - (2*a^2 + 2*c^2 - b^2)] );

S := Veronese(S6);

time C := Conics(S);
#C;
[ MinimalBasis(X) : X in C ];
[ Dimension(X) : X in C ];
[ Degree(Curve(X)) : X in C ];



