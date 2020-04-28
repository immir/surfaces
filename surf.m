/*

*/

declare verbose Surf, 3;

// ----------------------------------------------------------------------
// functional programming

intrinsic car (xs::SeqEnum) -> . {} return xs[1]; end intrinsic;
intrinsic cdr (xs::SeqEnum) -> . {} return xs[2..#xs]; end intrinsic;
intrinsic map (f, xs::SeqEnum) -> SeqEnum
  {} return [ f(x) : x in xs ]; end intrinsic;
intrinsic compose(fs::List) -> UserProgram
  {} return func< x | #fs eq 0
       select x else fs[1](compose(fs[2..#fs])(x)) >; end intrinsic;  
intrinsic compose(f, ...) -> UserProgram
  {} return compose(f); end intrinsic;
intrinsic filter(f, xs) -> . {} return [ x : x in xs | f(x) ]; end intrinsic;

// ----------------------------------------------------------------------
// Seq

intrinsic Seq (s) -> SeqEnum { }
  try return Eltseq(s); catch e; end try;
  try return [ x : x in s ]; catch e; end try;
  try return [ s[i] : i in [1..#s] ]; catch e; end try;
  error "cannot convert to sequence", s;
  try return Eltseq(s); catch e; end try;
end intrinsic;

// ----------------------------------------------------------------------
// Veronese map

intrinsic Veronese(X::Sch) -> Sch
  {}
  P := AmbientSpace(X);
  A := CoordinateRing(P);
  lcm := LCM(Gradings(P)[1]);
  monos := [ x : x in MonomialsOfWeightedDegree(A, lcm) ];
  R2 := PolynomialRing(BaseRing(A), #monos);
  AssignNames(~R2, [ Sprintf("{%o}",x) : x in monos ]);
  P2 := ProjectiveSpace(R2);
  h := map< P -> P2 | monos >;
  return h(X), h;
end intrinsic;


// ----------------------------------------------------------------------
// Lines

intrinsic Lines(S::Sch :
                Qbar := AlgebraicClosure(Rationals()))
                -> List

  { Return a sequence of lines as subschemes of the projective 
    variety S. }

  schemes, params := LinesInScheme(S);
  lines := [];

  n := Rank(CoordinateRing(S));

  SS := ChangeRing(S, Qbar);
  RR := CoordinateRing(SS);
  AssignNames(~RR, Names(CoordinateRing(S)));

  for j in [1..#schemes] do
    scheme := schemes[j];
    param  := params[j];

    points := RationalPoints(scheme, Qbar);

    for pt in points do

      planes := Basis(Kernel(Transpose(Matrix(
        [[ Evaluate(Evaluate(x,s), pt) : x in param ]
          : s in [0,1]] ))));

      eqns := [ &+ [ SS.i * Eltseq(v)[i] : i in [1..n]] : v in planes ];
      Append(~lines, Scheme(SS, eqns));
    end for;
      
  end for;

  return lines;

end intrinsic;


// ----------------------------------------------------------------------
// Conics

intrinsic Conics(PX::Sch :
                 Qbar := AlgebraicClosure(Rationals()))
           -> List, FldAC
  { }
  X := AffinePatch(PX, 1);
  F := BaseField(X);
  n := Dimension(AmbientSpace(X));
  k := n+1;
  AssignNames(~X, Names(CoordinateRing(PX))[1..n]);
  eqns_X := DefiningEquations(X);
  
  H := ChangeRing(PolynomialRing(CoordinateRing(PX), n+1), Qbar);

  // first, any conics at infinity

  solutions := { [H| f : f in DefiningEquations(Y) | Degree(f) eq 1 ]
               : Y in PrimeComponents(Scheme(PX, PX.(n+1)))
               | Dimension(Y) eq 1 and Degree(Curve(Y)) eq 2 };

  vprint Surf,1: "number of solutions at infinity: ", #solutions;

  for i in [1..n-1], j in [i+1..n] do

    pivs := SetToSequence({1..n} diff {i,j});
    ni := #{p : p in pivs | p lt i };
    nj := #{p : p in pivs | p lt j };
    nk := #pivs;
    nvars := ni + nj + nk + 6 + 2;

    AA<q1,q2,q3,q4,q5,q6,x0,y0> := PolynomialRing(F, nvars, "grevlexw",
                                    [3^^6, 2^^2, 4^^(ni+nj+nk)]);

    vi := [ AA.(8+i)       : i in [1..ni]];
    vj := [ AA.(8+ni+i)    : i in [1..nj]];
    vk := [ AA.(8+ni+nj+i) : i in [1..nk]];

    RR<t> := PolynomialRing(AA);

    G := Matrix(AA, n-2, n+1, &cat[
       [ <r, pivs[r], 1>  : r in [1..#pivs] ],
       [ <r, i,   vi[r]>  : r in [1..ni]    ],
       [ <r, j,   vj[r]>  : r in [1..nj]    ],
       [ <r, n+1, vk[r]>  : r in [1..nk]    ]]);

    vprint Surf, 2: G;

    A := q1*t^2 + q2 + q4*t;
    B := 2*q1*x0*t + 2*q2*y0 + q4*x0 + q4*y0*t + q5*t + q6;

    u := Vector([x0,y0,1]);
    Q := Matrix([[  q1,  q4/2, q5/2 ],
                 [ q4/2,  q2,  q6/2 ],
                 [ q5/2, q6/2,  q3  ]]);

    v := [Parent(A/B)| 0^^n ];
    v[i] := x0 - t*B/A;
    v[j] := y0 - B/A;
    for r in [1..#pivs] do
      p := pivs[r];
      v[p] := v[i] * G[r][i] + v[j] * G[r][j] + G[r][n+1];
    end for;

    w := Vector([Parent(A/B)| 0^^(n+1)]);
    w[i] := x0 - t*B/A;
    w[j] := y0 - B/A;
    w[k] := 1;

    ww := w * Transpose(ChangeRing(G,Parent(B/A)));
    assert &and [ ww[k] eq v[pivs[k]] : k in [1..#pivs]];
    // assert &and [ ww[i] eq v[i] : i in [1..#Eltseq(ww)] ];
    // assert &and [ ww[i] eq v[i] : i in [1..#v] ];

    eqns_t := [ Evaluate(e,v) : e in eqns_X ] cat
              [ (u*Q, u), Determinant(Q) - 1, x0 ];

    eqns := &cat [ Eltseq(Numerator(e)) : e in eqns_t ];

    vprint Surf, 2: #Set(eqns), " equations, ", nvars, " variables";

    tm := Cputime();
    eqns_g := GroebnerBasis(eqns);
    tm := Cputime(tm);


    Y := Scheme(AffineSpace(AA), eqns_g);
    dim := Dimension(Y);

    vprint Surf, 1: "Groebner complete, dim ", dim, " in ", tm, " seconds";

    if dim eq -1 then
      vprint Surf, 2: "dimension -1: no solutions";
      continue;
    end if;

    if dim eq 0 then

      pts := RationalPoints(Y, Qbar);
      vprint Surf, 2: "dimension 0, number of points:", #pts;

      // now, extract the Grassmanian component to get the hyperplanes

      pt := pts[1]; r := 1; p := pivs[r];

      // it's multiplying H.i by the evaluation that is the costly
      // part of this: it's a once off cost though, so it's something
      // to do with changing/extending the definition of H to the new
      // version of Qbar (it changes as we find new points)

      // TODO: defer this product / generation of equations until
      // later somehow, and redefine H then with the current Qbar
      // might eliminate this cost;

      // perhaps keep track seqs of <l, coeff[l]> pairs for
      // H.l * coeff[l] for the equations

/*      time H.i * Eltseq(pt)[4];
      time H.i * Evaluate(G[r][i], pt);
      time H.j * Evaluate(G[r][j], pt);
      time H.k * Evaluate(G[r][k], pt);
*/

/* build the equations more explicitly...!?!?! */

      solutions join:= {
           [ H.p - H.i     * Evaluate(G[r][i],   pt)
                 - H.j     * Evaluate(G[r][j],   pt)
                 - H.(n+1) * Evaluate(G[r][n+1], pt)
              where p is pivs[r] : r in [1..#pivs] ]
           cat
            [ (v*QH,v) // the actual conic equation recovered
                  where QH is ChangeRing(Evaluate(Q, Eltseq(pt)), H)
                  where v is Vector([H.i, H.j, H.k]) ]
           : pt in pts };

    end if;

    if dim gt 0 then
      printf "dimension %o: infinite\n", dim;
    end if;

  end for;

  // our conics are defined over Qbar now

  PPX := ChangeRing(PX, Qbar);
  old := true;
  if old then
    RRX := CoordinateRing(PPX);
    AssignNames(~RRX, Names(CoordinateRing(PX)));
    rho := hom< H -> RRX | [ RRX.i : i in [1..n+1] ]>;
    ret := SetToSequence({ Scheme(PPX, [ rho(e) : e in s ])
      : s in solutions });
  else    
    ret := SetToSequence({ Scheme(ProjectiveSpace(H), s)
                         : s in solutions});
  end if;
  return ret, PPX;
end intrinsic;



// ----------------------------------------------------------------------
// Singular elliptic curves (cubics!)

intrinsic Cubics(PX::Sch :
                 Qbar := AlgebraicClosure(Rationals()))
           -> List, FldAC
  { }
  X := AffinePatch(PX, 1);
  F := BaseField(X);
  n := Dimension(AmbientSpace(X));
  k := n+1;
  AssignNames(~X, Names(CoordinateRing(PX))[1..n]);
  eqns_X := DefiningEquations(X);
  
  H := ChangeRing(PolynomialRing(CoordinateRing(PX), n+1), Qbar);

  // first, any conics at infinity

  solutions := { [H| f : f in DefiningEquations(Y) | Degree(f) eq 1 ]
               : Y in PrimeComponents(Scheme(PX, PX.(n+1)))
               | Dimension(Y) eq 1 and Degree(Curve(Y)) eq 3 };

  vprint Surf,1: "number of solutions at infinity: ", #solutions;

  for i in [1..n-1], j in [i+1..n] do

    pivs := SetToSequence({1..n} diff {i,j});
    ni := #{p : p in pivs | p lt i };
    nj := #{p : p in pivs | p lt j };
    nk := #pivs;
    nvars := ni + nj + nk + 7 + 2;

    AA<q1,q2,q3,q4,q5,q6,q7,x0,y0> := PolynomialRing(F, nvars, "grevlexw",
                                    [3^^7, 2^^2, 4^^(ni+nj+nk)]);

    vi := [ AA.(9+i)       : i in [1..ni]];
    vj := [ AA.(9+ni+i)    : i in [1..nj]];
    vk := [ AA.(9+ni+nj+i) : i in [1..nk]];

    RR<t> := PolynomialRing(AA);

    G := Matrix(AA, n-2, n+1, &cat[
       [ <r, pivs[r], 1>  : r in [1..#pivs] ],
       [ <r, i,   vi[r]>  : r in [1..ni]    ],
       [ <r, j,   vj[r]>  : r in [1..nj]    ],
       [ <r, n+1, vk[r]>  : r in [1..nk]    ]]);

    vprint Surf, 2: G;

    A := 2; // q1*t^2 + q2 + q4*t;
    B := 2; // q1*x0*t + 2*q2*y0 + q4*x0 + q4*y0*t + q5*t + q6;

    u := Vector([x0,y0,1]);
    Q := Matrix([[  q1,  q4/2, q5/2 ],
                 [ q4/2,  q2,  q6/2 ],
                 [ q5/2, q6/2,  q3  ]]);

    v := [Parent(A/B)| 0^^n ];
    v[i] := x0 - t*B/A;
    v[j] := y0 - B/A;
    for r in [1..#pivs] do
      p := pivs[r];
      v[p] := v[i] * G[r][i] + v[j] * G[r][j] + G[r][n+1];
    end for;

    w := Vector([Parent(A/B)| 0^^(n+1)]);
    w[i] := x0 - t*B/A;
    w[j] := y0 - B/A;
    w[k] := 1;

    ww := w * Transpose(ChangeRing(G,Parent(B/A)));
    assert &and [ ww[k] eq v[pivs[k]] : k in [1..#pivs]];
    // assert &and [ ww[i] eq v[i] : i in [1..#Eltseq(ww)] ];
    // assert &and [ ww[i] eq v[i] : i in [1..#v] ];

    eqns_t := [ Evaluate(e,v) : e in eqns_X ] cat
              [ (u*Q, u), Determinant(Q) - 1, x0 ];

    eqns := &cat [ Eltseq(Numerator(e)) : e in eqns_t ];

    vprint Surf, 2: #Set(eqns), " equations, ", nvars, " variables";

    tm := Cputime();
    eqns_g := GroebnerBasis(eqns);
    tm := Cputime(tm);


    Y := Scheme(AffineSpace(AA), eqns_g);
    dim := Dimension(Y);

    vprint Surf, 1: "Groebner complete, dim ", dim, " in ", tm, " seconds";

    if dim eq -1 then
      vprint Surf, 2: "dimension -1: no solutions";
      continue;
    end if;

    if dim eq 0 then

      pts := RationalPoints(Y, Qbar);
      vprint Surf, 2: "dimension 0, number of points:", #pts;

      // now, extract the Grassmanian component to get the hyperplanes

      pt := pts[1]; r := 1; p := pivs[r];

      // it's multiplying H.i by the evaluation that is the costly
      // part of this: it's a once off cost though, so it's something
      // to do with changing/extending the definition of H to the new
      // version of Qbar (it changes as we find new points)

      // TODO: defer this product / generation of equations until
      // later somehow, and redefine H then with the current Qbar
      // might eliminate this cost;

      // perhaps keep track seqs of <l, coeff[l]> pairs for
      // H.l * coeff[l] for the equations

/*      time H.i * Eltseq(pt)[4];
      time H.i * Evaluate(G[r][i], pt);
      time H.j * Evaluate(G[r][j], pt);
      time H.k * Evaluate(G[r][k], pt);
*/

/* build the equations more explicitly...!?!?! */

      solutions join:= {
           [ H.p - H.i     * Evaluate(G[r][i],   pt)
                 - H.j     * Evaluate(G[r][j],   pt)
                 - H.(n+1) * Evaluate(G[r][n+1], pt)
              where p is pivs[r] : r in [1..#pivs] ]
           cat
            [ (v*QH,v) // the actual conic equation recovered
                  where QH is ChangeRing(Evaluate(Q, Eltseq(pt)), H)
                  where v is Vector([H.i, H.j, H.k]) ]
           : pt in pts };

    end if;

    if dim gt 0 then
      printf "dimension %o: infinite\n", dim;
    end if;

  end for;

  // our conics are defined over Qbar now

  PPX := ChangeRing(PX, Qbar);
  //RRX := CoordinateRing(PPX);
  //AssignNames(~RRX, Names(CoordinateRing(PX)));
  //rho := hom< H -> RRX | [ RRX.i : i in [1..n+1] ]>;
  ret := SetToSequence({ Scheme(ProjectiveSpace(H), s)
                       : s in solutions});
  return ret, PPX;
end intrinsic;

