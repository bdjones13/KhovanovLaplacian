(* ::Package:: *)

BeginPackage["KhovanovLaplacian`"]; Print["Loading KhovanovLaplacian`..."]
Needs["KnotTheory`"]
(*Link; X; *)S; V; c; vp; vm; KhBracket; v; d; q; np; nm; CC; t; Betti; qBetti; Kh; NewTensorToString; GetDQ; qLapNew; LapBetti; qLapBetti; LapKh; qSpectra; qSpectraAllEigs; checkMirror;
KhSilent; BettiSilent; qBettiSilent; qSpectraAllEigsSilent;

Begin["`Private`"]
(*Begin functions copied from Categorification package*)
np[L_PD] := Count[L, X[i_,j_,k_,l_] /; j-l==1 || l-j>1];
nm[L_PD] := Count[L, X[i_,j_,k_,l_] /; l-j==1 || j-l>1];

SetAttributes[p, Orderless]
S[L_PD, s_String] := S[L, Characters[s] /. {"0"->0, "1"->1}]
S[L_PD, a_List] := Times @@ (Thread[{List @@ L, a}] /. {
  {X[i_,j_,k_,l_], 0} :> p[i,j][Min[i,j]] p[k,l][Min[k,l]],
  {X[i_,j_,k_,l_], 1} :> p[i,l][Min[i,l]] p[j,k][Min[j,k]],
  {x_X, "*"} :> x
}) //. p[i_,j_][m_] p[j_,k_][n_] :> p[i,k][Min[m,n]] //. {
  X[i_,j_,k_,l_] p[i_,j_][m_] p[k_,l_][n_] :> (c[m] c[n] -> c[Min[m,n]]),
  X[i_,j_,k_,l_] p[i_,l_][m_] p[j_,k_][n_] :> (c[Min[m,n]] -> c[m] c[n])
} //. p[_,_][m_]^_. :> c[m]

Deg[expr_] := Count[expr, _vp, {0,1}] - Count[expr, _vm, {0,1}]

V[L_PD, s_String, deg___] := V[L, Characters[s] /. {"0"->0, "1"->1}, deg]
V[L_PD, a_List] := List @@ Expand[S[L, a] /. x_c :> ((vp @@ x) + (vm @@ x))]
V[L_PD, a_List, deg_Integer] :=
  Select[V[L, a], (deg == Deg[#] + (Plus @@ a))&]

d[L_PD, s_String] := d[L, Characters[s] /. {"0"->0, "1"->1}]
d[L_PD, a_List] := S[L, a] /. {
  (c[x_]c[y_]->c[z_])*_. :>
    {vp@x vp@y -> vp@z, vp@x vm@y -> vm@z, vm@x vp@y -> vm@z, vm@x vm@y -> 0},
  (c[z_]->c[x_]c[y_])*_. :> {vp@z -> vp@x vm@y + vm@x vp@y, vm@z -> vm@x vm@y}
}

KhBracket[L_PD, r_Integer, deg___] := If[r<0 || r>Length[L], {0},
  Join @@ ( ((v @@ #) V[L, #, deg])& /@
    Permutations[Join[Table[0, {Length[L] - r}], Table[1, {r}]]]
  )
]

CC[L_PD, r_Integer, deg_Integer] := KhBracket[L, r+nm[L], deg-np[L]+2nm[L]]

d[L_PD][expr_] := Expand[expr] /. s_*a_v :> Expand[
  sign=1; Sum[ If[ a[[i]]==0,
    sign * ReplacePart[a, 1, i] * s /.  d[L, List @@ ReplacePart[a, "*", i]],
    sign *= -1; 0
  ], {i, Length[a]} ]
]

Options[Betti] = {Modulus -> Infinity}
Rank[L_PD, r_Integer, deg_Integer, opts___] := Rank[L,r,deg,opts] = (
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
Betti[L_PD, r_Integer, deg_Integer, opts___] := Betti[L,r,deg,opts] = (
  b = Length[CC[L,r,deg]]-Rank[L,r,deg,opts]-Rank[L,r-1,deg,opts];
  Print[StringForm["Betti[``,``] = ``", r, deg, b]]; b
)

BettiSilent[L_PD, r_Integer, deg_Integer, opts___] := BettiSilent[L,r,deg,opts] = (
  b = Length[CC[L,r,deg]]-Rank[L,r,deg,opts]-Rank[L,r-1,deg,opts];
  b
)


qBetti[L_PD, r_Integer, opts___] := (
  degs = Union[Deg /@ KhBracket[L, r+nm[L]]] + np[L] - nm[L] + r;
  (Betti[L, r, #, opts]& /@ degs) . q^degs
)

qBettiSilent[L_PD, r_Integer, opts___] := (
  degs = Union[Deg /@ KhBracket[L, r+nm[L]]] + np[L] - nm[L] + r;
  (BettiSilent[L, r, #, opts]& /@ degs) . q^degs
)

Kh[L_PD, opts___] := Kh[L, opts] =
  Expand[Sum[t^r * qBetti[L, r, opts], {r, -nm[L], Length[L]-nm[L]}]]

KhSilent[L_PD, opts___] := KhSilent[L, opts] =
  Expand[Sum[t^r * qBettiSilent[L, r, opts], {r, -nm[L], Length[L]-nm[L]}]]

(*End functions copied from Categorification package.*)
(*Begin Laplacian-specific functions*)


NewTensorToString[obj_] := (
Return[StringReplace[ToString[obj], {", "-> "","v["->"v", "]"->"", "vm["-> "m", "vp[" -> "p", " "-> ""}]]
)

GetDQ[L_PD,dim_Integer,deg_Integer] := (
	If[(*dim<0 ||*) dim>Length[L], Return[{0}],
	If[Length[CC[L,dim,deg]]==0 || ToString[First[CC[L,dim,deg]]]==ToString[0],Return[SparseArray[{},{1,Length[CC[L,dim-1,deg]]}]],
	If[(Length[CC[L,dim-1,deg]]==0  )|| (ToString[First[CC[L,dim-1,deg]]]==ToString[0]),Return[SparseArray[{},{Length[CC[L,dim,deg]], 1}]],
	symbstrings = NewTensorToString[#] &/@ CC[L,dim,deg];
	symbs = Symbol[#] &/@ symbstrings;
	newrules = Thread[symbs->ToExpression[symbs]];
	originalrules = Thread[CC[L,dim,deg] -> ToExpression[symbs]];
	ds = d[L][#] &/@ CC[L,dim-1,deg];
	dsymb = ds /. originalrules;
	fulld = CoefficientArrays[dsymb,symbs][[2]];
	Return[Transpose[fulld]]]]]
)

qLapNew[L_,k_,deg_Integer] := 
(dup = GetDQ[L,k+1,deg];
		ddown = GetDQ[L,k,deg];
		dup = Transpose[dup];
		ddown = Transpose[ddown];
		Return[dup . Transpose[dup] + Transpose[ddown] . ddown];
)

LapBetti[L_PD, r_Integer, deg_Integer] := LapBetti[L,r,deg] = (
b = Count[Eigenvalues[qLapNew[L,r,deg]],0]; (*TODO: add tolerance*)
   Print[StringForm["LapBetti[``,``] = ``", r, deg, b]]; b
)

qLapBetti[L_PD, r_Integer] := (
  degs = Union[Deg /@ KhBracket[L, r+nm[L]]] + np[L] - nm[L] + r;
  (LapBetti[L, r, #]& /@ degs) . q^degs
)

LapKh[L_PD] := LapKh[L] =
  Expand[Sum[t^r * qLapBetti[L, r], {r, -nm[L], Length[L]-nm[L]}]]


qSpectra[L_,r_,deg_] := Chop[SetPrecision[Eigenvalues[SetPrecision[qLapNew[L,r, deg],MachinePrecision],-8],MachinePrecision],10^-10]
qSpectraAllEigs[L_,r_, deg_] :=(eigs = SetPrecision[Eigenvalues[SetPrecision[qLapNew[L,r, deg],MachinePrecision]],MachinePrecision];
	Print[StringForm["qSpectraAllEigs[``,``] = ``", r, deg, eigs]]; eigs)

qSpectraAllEigsSilent[L_,r_, deg_] :=(eigs = SetPrecision[Eigenvalues[SetPrecision[qLapNew[L,r, deg],MachinePrecision]],MachinePrecision];
	eigs)


qSpectra[L_,r_] := (
	degs = Union[Deg /@ KhBracket[L, r+nm[L]]] + np[L] - nm[L] + r;
	qSpectra[L,r, #] &/@ degs
)
qSpectra[L_] := qSpectra[L,# ] &/@ Range[-nm[L],Length[L]-nm[L]]
(*qSpectraAllEigs[L_,r_] := qSpectraAllEigs[L,r,#] &/@ Range[-nm[L],Length[L]-nm[L]]
*)
qSpectraAllEigs[L_,r_] := (
	degs = Union[Deg /@ KhBracket[L, r+nm[L]]] + np[L] - nm[L] + r;
	qSpectraAllEigs[L,r, #] &/@ degs
)

qSpectraAllEigsSilent[L_,r_] := (
	degs = Union[Deg /@ KhBracket[L, r+nm[L]]] + np[L] - nm[L] + r;
	qSpectraAllEigsSilent[L,r, #] &/@ degs
)

qSpectraAllEigs[L_] := qSpectraAllEigs[L] = qSpectraAllEigs[L,#] &/@ Range[-nm[L],Length[L]-nm[L]]
qSpectraAllEigsSilent[L_] := qSpectraAllEigsSilent[L] = qSpectraAllEigsSilent[L,#] &/@ Range[-nm[L],Length[L]-nm[L]]

checkMirror[PD_] := (
	mPD = Mirror[PD];
	eigs1 = qSpectraAllEigs[PD];
	eigs2 = qSpectraAllEigs[mPD];
	diffeigs = eigs1-Reverse[eigs2,{1,2}];
	ContainsOnly[Flatten[Chop[diffeigs,0.001]],{0}]
)


End[]
EndPackage[]

