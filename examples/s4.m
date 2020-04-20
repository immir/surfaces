
SetEchoInput(true);
Attach("surf.m");

P21111<D,a,b,c,k> := ProjectiveSpace(Rationals(), [2,1,1,1,1]);
S4 := Scheme(P21111, [
   16*D^2 - (a+b+c)*(-a+b+c)*(a-b+c)*(a+b-c),
   4*k^2 - (2*b^2 + 2*c^2 - a^2)] );

S := Veronese(S4);

time C := Conics(S);
#C;
[ MinimalBasis(X) : X in C ];
[ Dimension(X) : X in C ];
[ Degree(Curve(X)) : X in C ];



