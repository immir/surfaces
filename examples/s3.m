
SetEchoInput(true);
Attach("surf.m");

P5<a,b,c,k,l,m> := ProjectiveSpace(Rationals(), 5);
S3 := Scheme(P5, [
   4*k^2 - (2*b^2 + 2*c^2 - a^2),
   4*l^2 - (2*c^2 + 2*a^2 - b^2),
   4*m^2 - (2*a^2 + 2*b^2 - c^2) ]);

time C := Conics(S3);
#C;
[ MinimalBasis(X) : X in C ];
[ Dimension(X) : X in C ];
[ Degree(Curve(X)) : X in C ];

QQ := BaseField(C[1]);
QQ.1, MinimalPolynomial(QQ.1);
QQ.2, MinimalPolynomial(QQ.2);
QQ.10, MinimalPolynomial(QQ.10);



