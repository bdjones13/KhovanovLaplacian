BeginPackage["Categorification`"]; Print["Loading Categorification`..."]

Link; X; S; V; c; vp; vm; KhBracket; v; d; q; np; nm; CC; t; Betti; qBetti; Kh

Begin["`Private`"]

np[L_Link] := Count[L, X[i_,j_,k_,l_] /; j-l==1 || l-j>1];
nm[L_Link] := Count[L, X[i_,j_,k_,l_] /; l-j==1 || j-l>1];

SetAttributes[p, Orderless]
S[L_Link, s_String] := S[L, Characters[s] /. {"0"->0, "1"->1}]
S[L_Link, a_List] := Times @@ (Thread[{List @@ L, a}] /. {
  {X[i_,j_,k_,l_], 0} :> p[i,j][Min[i,j]] p[k,l][Min[k,l]],
  {X[i_,j_,k_,l_], 1} :> p[i,l][Min[i,l]] p[j,k][Min[j,k]],
  {x_X, "*"} :> x
}) //. p[i_,j_][m_] p[j_,k_][n_] :> p[i,k][Min[m,n]] //. {
  X[i_,j_,k_,l_] p[i_,j_][m_] p[k_,l_][n_] :> (c[m] c[n] -> c[Min[m,n]]),
  X[i_,j_,k_,l_] p[i_,l_][m_] p[j_,k_][n_] :> (c[Min[m,n]] -> c[m] c[n])
} //. p[_,_][m_]^_. :> c[m]

Deg[expr_] := Count[expr, _vp, {0,1}] - Count[expr, _vm, {0,1}]

V[L_Link, s_String, deg___] := V[L, Characters[s] /. {"0"->0, "1"->1}, deg]
V[L_Link, a_List] := List @@ Expand[S[L, a] /. x_c :> ((vp @@ x) + (vm @@ x))]
V[L_Link, a_List, deg_Integer] :=
  Select[V[L, a], (deg == Deg[#] + (Plus @@ a))&]

d[L_Link, s_String] := d[L, Characters[s] /. {"0"->0, "1"->1}]
d[L_Link, a_List] := S[L, a] /. {
  (c[x_]c[y_]->c[z_])*_. :>
    {vp@x vp@y -> vp@z, vp@x vm@y -> vm@z, vm@x vp@y -> vm@z, vm@x vm@y -> 0},
  (c[z_]->c[x_]c[y_])*_. :> {vp@z -> vp@x vm@y + vm@x vp@y, vm@z -> vm@x vm@y}
}

KhBracket[L_Link, r_Integer, deg___] := If[r<0 || r>Length[L], {0},
  Join @@ ( ((v @@ #) V[L, #, deg])& /@
    Permutations[Join[Table[0, {Length[L] - r}], Table[1, {r}]]]
  )
]

CC[L_Link, r_Integer, deg_Integer] := KhBracket[L, r+nm[L], deg-np[L]+2nm[L]]

d[L_Link][expr_] := Expand[expr] /. s_*a_v :> Expand[
  sign=1; Sum[ If[ a[[i]]==0,
    sign * ReplacePart[a, 1, i] * s /.  d[L, List @@ ReplacePart[a, "*", i]],
    sign *= -1; 0
  ], {i, Length[a]} ]
]

Options[Betti] = {Modulus -> Infinity}
Rank[L_Link, r_Integer, deg_Integer, opts___] := Rank[L,r,deg,opts] = (
  modulus = (Modulus /. {opts} /. Options[Betti]);
  Off[Solve::svars];
  b0 = CC[L, r, deg]; l1 = Length[b1 = CC[L, r+1, deg]];
  eqs = (#==0)& /@ d[L][b0] /. MapThread[Rule, {b1, vars = Array[b, l1]}];
  rk = Which[b0 == {} || l1 == 0, 0,
    modulus === Infinity, Length[First[Solve[eqs, vars]]],
    True, Length[First[Solve[
      Append[eqs, Modulus == modulus], vars, Mode -> Modular
    ]]] - 1
  ];
  On[Solve::svars]; rk
)
Betti[L_Link, r_Integer, deg_Integer, opts___] := Betti[L,r,deg,opts] = (
  b = Length[CC[L,r,deg]]-Rank[L,r,deg,opts]-Rank[L,r-1,deg,opts];
  Print[StringForm["Betti[``,``] = ``", r, deg, b]]; b
)

qBetti[L_Link, r_Integer, opts___] := (
  degs = Union[Deg /@ KhBracket[L, r+nm[L]]] + np[L] - nm[L] + r;
  (Betti[L, r, #, opts]& /@ degs) . q^degs
)

Kh[L_Link, opts___] := Kh[L, opts] =
  Expand[Sum[t^r * qBetti[L, r, opts], {r, -nm[L], Length[L]-nm[L]}]]

End[]; EndPackage[]
