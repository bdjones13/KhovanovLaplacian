(* ::Package:: *)

(************************************************************************)
(* This file was generated automatically by the Mathematica front end.  *)
(* It contains Initialization cells from a Notebook file, which         *)
(* typically will have the same name as this file except ending in      *)
(* ".nb" instead of ".m".                                               *)
(*                                                                      *)
(* This file is intended to be loaded into the Mathematica kernel using *)
(* the package loading commands Get or Needs.  Doing so is equivalent   *)
(* to using the Evaluate Initialization Cells menu command in the front *)
(* end.                                                                 *)
(*                                                                      *)
(* DO NOT EDIT THIS FILE.  This entire file is regenerated              *)
(* automatically each time the parent Notebook file is saved in the     *)
(* Mathematica front end.  Any changes you make to this file will be    *)
(* overwritten.                                                         *)
(************************************************************************)



BeginPackage["QuantumGroups`Steinberg`",{"QuantumGroups`","QuantumGroups`RootsOfUnity`","QuantumGroups`RootsOfUnity`","QuantumGroups`Representations`","QuantumGroups`RootSystems`"}];


SteinbergDecomposeRepresentation;


Begin["`Private`"];


SteinbergFold[\[CapitalGamma]_,i_][c_]/;1<=i<=Rank[\[CapitalGamma]]:=Module[{root,innerproduct},
root=SimpleRoots[\[CapitalGamma]][[i]];
innerproduct[\[Lambda]_]:=innerproduct[\[Lambda]]=KillingForm[\[CapitalGamma]][\[Lambda]+\[Rho][\[CapitalGamma]],root];
c/.{Irrep[\[CapitalGamma]][\[Lambda]_]/;(innerproduct[\[Lambda]]==0):>0,Irrep[\[CapitalGamma]][\[Lambda]_]/;(innerproduct[\[Lambda]]<0):>(f[\[Lambda]];-Irrep[\[CapitalGamma]][\[Lambda]-(2innerproduct[\[Lambda]]/innerproduct[root-\[Rho][\[CapitalGamma]]])root])}
]


SteinbergAlcoveFold[\[CapitalGamma]_,l_][c_]:=Module[{root,innerproduct,wall},
root=-AlcoveDefiningRoot[\[CapitalGamma],l];
innerproduct[\[Lambda]_]:=innerproduct[\[Lambda]]=KillingForm[\[CapitalGamma]][\[Lambda]+\[Rho][\[CapitalGamma]],root];
wall=-If[EvenQ[l],l/2,l];
c/.{Irrep[\[CapitalGamma]][\[Lambda]_]/;(innerproduct[\[Lambda]]==wall):>0,Irrep[\[CapitalGamma]][\[Lambda]_]/;(innerproduct[\[Lambda]]<wall):>-Irrep[\[CapitalGamma]][\[Lambda]-(2(innerproduct[\[Lambda]]-wall)/innerproduct[root-\[Rho][\[CapitalGamma]]])root]}
]


SteinbergFoldAll[\[CapitalGamma]_,l_:0][c_]:=
Fold[#2[#1]&,c,If[l>0,{SteinbergAlcoveFold[\[CapitalGamma],l]},{}]~Join~Table[SteinbergFold[\[CapitalGamma],i],{i,1,Rank[\[CapitalGamma]]}]]


SteinbergDecomposeRepresentation[\[CapitalGamma]_,l_:0][Irrep[\[CapitalGamma]_][\[Lambda]_]\[CircleTimes]Irrep[\[CapitalGamma]_][\[Mu]_]]:=SteinbergDecomposeRepresentation[\[CapitalGamma],l][Irrep[\[CapitalGamma]][\[Lambda]]\[CircleTimes]Irrep[\[CapitalGamma]][\[Mu]]]=FixedPoint[SteinbergFoldAll[\[CapitalGamma],l],
Plus@@(WeightMultiplicities[\[CapitalGamma],Irrep[\[CapitalGamma]][\[Mu]]]/.{\[Kappa]:{___Integer},n_Integer}:>n Irrep[\[CapitalGamma]][\[Kappa]+\[Lambda]])]/.{n_Integer V:Irrep[\[CapitalGamma]][_]/;n>0:>DirectSum@@Table[V,{n}]}/.Plus->DirectSum


End[];


EndPackage[];
