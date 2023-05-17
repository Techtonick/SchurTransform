(* ::Package:: *)

BeginPackage["STPackage`"];


SchurTransform::usage = "SchurTransform[n] outputs a Schur Transform for n qubits.";


Begin["`Private`"];


(* ::Title:: *)
(*Schur Transform*)


(* ::Text:: *)
(*The general idea behind this algorithm is to implement the Schur Transform recursively, through applying a direct sum of relevant CG transforms for irreps of a Schur basis of n qubits to a Tensor product of a Schur Transform for n qubits and a 2x2 Identity matrix (this tensor product with identity represents adding a new qubit), thus obtaining something like a Schur Transform for n+1 qubits, although with certain rows disordered. We then have to apply a certain permutation matrix in order to obtain the true Schur Transform for n+1 qubits.*)
(*The CG transform, when acting on an irrep of dimensionality d of n-qubit Schur basis, outputs two irreps of n+1-qubit Schur basis, one of them with dimensionality d+1 and the other with dimensionality d-1.*)


(* ::Input::Initialization:: *)
(*Identity matrix of size d\[Times]d*)
Id[d_]:=SparseArray[Band[{1,1}]->1,{d,d}];


(* ::Section:: *)
(*CG*)


(* ::Text:: *)
(*In this step we implement the Clebsch-Gordan (CG) transform for a subspace (irrep) of dimension d.*)
(*We do that directly, by making a sparse array with non-zero values being the CG-coefficients at specific corresponding positions in the matrix.*)


(* ::Input::Initialization:: *)
(*Parameters:*)(*l=2j=overhang*)(*w=j-m=Hamming weight of the overhang\[Element][0,l]*)(*Example:when j=1/2 we have:m=1/2-> |0>and m=-(1/2)-> |1>*)(*\[CapitalDelta]l\[Element]{-1,+1} change in overhang*)(*x\[Element]{0,1} the new symbol*)MyCG[l_,w_,\[CapitalDelta]l_,x_]:=If[x==0,\[CapitalDelta]l,1] 1/Sqrt[2] Sqrt[(l+1+\[CapitalDelta]l(1-2 x)(l+1-2 (w+x)))/(l+1)];
CG[d_]:=Module[{l1,l2,l3,l4},(*Increase overhang*)l1=Table[{i+1,2i}->MyCG[d-1,i-1,1,1],{i,1,d}];
l2=Table[{i+1,2i+1}->MyCG[d-1,i,1,0],{i,0,d-1}];
(*Decrease overhang*)l3=Table[{(d+1)+i+1,2i+2}->MyCG[d-1,i,-1,1],{i,0,d-2}];
l4=Table[{(d+1)+i+1,2i+2+1}->MyCG[d-1,i+1,-1,0],{i,0,d-2}];
SparseArray[Join[l1,l2,l3,l4],{2d,2d}]];


(* ::Section:: *)
(*Auxiliary functions for implementing the Schur Basis*)


(* ::Text:: *)
(*In this step we implement a depiction of the Schur Basis that uniquely defines every independent basis state. This depiction is equivalent to the classic one, which consists of three main components: partition, Standard Young Tableux (SYT) and the Semi-Standard Young Tableau (SSYT). *)
(*We also define some auxiliary functions that help to manipulate and construct new basis elements for higher number of qubits from lower number of qubits (specifically, by adding one qubit).*)


(* ::Input::Initialization:: *)
SchurBasis0 = {{{0,1},{1},{},{0}},{{0,1},{1},{},{1}}} (*This is the depiction of Schur basis for one qubit. Every element on the first level is a basis element. Inside every basis element, so on the second level, there are four elements: 
-first represents the partition, where the first element in the partition is the number of boxes (elements) in the second row of SYT (and SSYT) and the second 
element is the number of boxes in the first row of SYT (and SSYT) (for example: {2,4} means there are 2 boxes in second row of SYT and 4 in the first);
  -second represents the first row of SYT, with its elements being the numbers in boxes of the first row of SYT (in order);
  -third represents the second row of SYT, with its elements being the numbers in boxes of the second row of SYT (in order, shares order with the first row);
(* Example for second and third: {1,2,4},{3,5} means that the first two qubits have their total spin (total angular momentum) added (1,2 in first row), for the third qubit the total spin (1/2 for one qubit) is subtracted from the total spin of the system (i.e. J3 = J2 - 1/2; 3 in the second row), the total spin of fourth qubit was added (4 in first) and total spin of fifth qubit was subtracted (5 in second) *)
  -fourth represents the Hamming weight of the overhang, which, given a partition, uniquely determines the SSYT.*)


(* ::Input::Initialization:: *)
NumSSYT[n_, l2_]:=n-2*l2+1; (* Function of total number of boxes (qubits) 'n' in SSYT and the number of boxes in the second row 'l2', computes the number of SSYT's with these parameters. *)


(* ::Input::Initialization:: *)
NumSYT[n_,l2_]:= Binomial[n+1,l2]*(n-2*l2+1)/(n+1); (* Function of total number of boxes (qubits) 'n' in SYT and the number of boxes in the second row 'l2', computes the number of SYT's with these parameters. *)


(* ::Input::Initialization:: *)
(* Supporting function for AddFirst, represents adding a box (qubit) to the first row of the Young Tableau for a given basis element 'a', thus increasing the second entry in partition by one i.e. increasing the number of elements in the first row and adding a number that is next in order to the SYT first row entry, i.e. for an SYT of {1,2,4} {3,5} it adds 6 to the first row entry turning the SYT into {1,2,4,6} {3,5} *)
AddFirst0[{{\[Lambda]2_,\[Lambda]1_},row1_,row2_,m_}]:={{\[Lambda]2,\[Lambda]1+1},Append[row1,\[Lambda]1+\[Lambda]2+1],row2,m}; 


(* ::Input::Initialization:: *)
 (* Adds a box (qubit) to the first row for every basis element in a given set 'lst' i.e. applies AddFirst0 to every basis element in a given set and then adds a new basis element to the set with max Hamming weight increased by one because the number of SSYT's gets increased by one *)
AddFirst[lst_]:= Module[{lstnew,last},
lstnew=Map[AddFirst0,lst];
last=lst2[[-1]];
last[[4,1]]++;
Append[lstnew,last]
];


(* ::Input::Initialization:: *)
 (* Supporting function for AddSecond, represents adding a box (qubit) to the second row of the Young Tableau for a given basis element 'a', thus increasing the first entry in partition by one i.e. increasing the number of elements in the second row and adding a number that is next in order to the SYT second row entry, i.e. for an SYT of {1,2,4} {3,5} it adds 6 to the second row entry turning the SYT into {1,2,4} {3,5,6} *)
AddSecond0[{{\[Lambda]2_,\[Lambda]1_},row1_,row2_,m_}]:={{\[Lambda]2+1,\[Lambda]1},row1,Append[row2,\[Lambda]1+\[Lambda]2+1],m};


(* ::Input::Initialization:: *)
(* Adds a box (qubit) to the second row for every basis element in a given set 'lst' i.e. applies AddSecond0 to every basis element in a given set and then deletes the last basis element in this set because the number of SSYT's gets decreased by one *)
AddSecond[lst_]:= Map[AddSecond0,Most[lst]]; 


(* ::Section:: *)
(*Permutation for CG*)


(* ::Text:: *)
(*This step is more for the showcase of this important part in the algorithm, because afterwards the Permutation function is merged with the CG recursion step to form the Schur Transform, as this way the implementation is faster.*)
(*This part computes the permutation matrix that we have to apply after the CG recursive step. This permutation is needed because the CG recursion outputs a direct sum of all higher and lower irreps in order in n+1 qubit space for every irrep in n qubit space. So, for example, for a direct sum of irreps (ir1, ir2, ir3) in this order it would output a direct sum of irreps (Higher[ir1], Lower[ir1], Higher[ir2], Lower[ir2], Higher[ir3], Lower[ir3]) in this order, but this is not necessarily the correct order in which the Schur Transform should order the irreps (or blocks, if applied to matrices). Say, if (ir1, ir2, ir3) have dimensions (6, 4, 4) respectively, the output would have dimensions (7, 5, 5, 3, 5, 3) in this order, while the actual order should have been: (7, 5, 5, 5, 3, 3).*)
(*This step utilizes the Schur Basis depiction introduced earlier in order to modify the basis in the same way the CG recursion step does and obtain a basis for a higher number of qubits, but disordered in the same way as the result of the CG recursion step. We then apply Ordering to the disordered Schur Basis depiction and obtain a permutation vector, that essentially gives us the needed permutation to get the true Schur Transform.*)


(* ::Input:: *)
(*Permutation[n_]:=  Module[{counter,subsp,ar,sb,num,first,second},*)
(*sb=SchurBasis0; (* Schur basis for 1 qubit *)*)
(*num=1; (* Iterator for the number of qubits *)*)
(*While[num<n, (* Cycle goes through all Schur Basis depictions until n, recursive nature to replicate what happens to basis in CG recursion step *)*)
(*sb = Sort[sb]; (* Sort at the start of each cycle so that we can get an unsorted Schur Basis depiction when While ends *)*)
(*ar={}; (* Auxiliary array that helps to update sb at every cycle *)*)
(*counter = 1;*)
(*For[l2=0,l2<=Quotient[num,2],l2++, (* Starts with all boxes in first row, adds one box to second until max possible amount reached, thus going through all dimensions of irreps *)*)
(*For[j=1,j<=NumSYT[num,l2],j++, (* Goes through all possible SYT's for a given dimension for irrep, keeps track of multiplicity for each irrep, i.e. repeats the cycle as many times as the multiplicity of an irrep of given dimensionality *)*)
(*subsp = sb[[counter;;counter+NumSSYT[num,l2]-1]]; (* Gets an irrep (spin subspace) from sb *)*)
(*first = AddFirst[subsp]; (* Adds box to first row for every basis element in an irrep *)*)
(*second = AddSecond[subsp]; (* Adds box to second row for every basis element in an irrep *)*)
(*subsp = Join[first,second]; (* Gives a joined subspace of two new irreps -- higher (AddFirst) and lower (AddSecond) *)*)
(*ar = Join[ar,subsp]; (* Step by step builds the new (disordered!) Schur Basis *)*)
(*counter = counter + NumSSYT[num,l2] (* Goes to position of the next irrep *)*)
(*]*)
(*];*)
(*sb = ar; (* Set the old Schur Basis to the new one with one more qubit *)*)
(*num++; (* Goes to the subspace with one more qubit *)*)
(*];*)
(*Return[Ordering[sb]] (* Returns the ordering for the final unsorted sb *)*)
(*]*)


(* ::Section:: *)
(*Schur Transform through CG and Permutation*)


(* ::Text:: *)
(*In this step we implement the Schur Transform itself by combining CG recursion and Permutation.  It's natural to combine these two parts of the algorithm as they exist within the same recursion.*)
(*Everything is implemented through Sparse Arrays to make it faster.*)


(* ::Input::Initialization:: *)
SchurTransform[n_]:= Module[{counter,subsp,ar,sb,num,first,second,SchurTrans,ClebGor},
sb=SchurBasis0;
num=1;
SchurTrans= SparseArray[IdentityMatrix[2]]; (* Schur Transform for 1 qubit *)
While[num<n,
sb = Sort[sb];
ar={};
counter = 1; (* Taken from Permutation up to this point *)
ClebGor=SparseArray[CG[NumSSYT[num,0]]]; (* The first CG in direct sum with the highest dimensionality for the irrep, i.e. all boxes in first row *)
For[l2=0,l2<=Quotient[num,2],l2++,
Do[
subsp = sb[[counter;;counter+NumSSYT[num,l2]-1]];
first = AddFirst[subsp];
second = AddSecond[subsp];
subsp = Join[first,second];
ar = Join[ar,subsp];
counter = counter + NumSSYT[num,l2]; (* Taken from Permutation up to this point *)
If[l2==0,Continue[], (* Continue so that to skip the direct sum for the first CG, which was already set above *)
ClebGor=ArrayFlatten[{{ClebGor,0},{0,SparseArray[CG[NumSSYT[num,l2]]]}}]] (* Append to ClebGor the direct sum of ClebGor with the CG for the next irrep, thus constructing the total direct sum of relevant CG's *)
,NumSYT[num,l2]];
];
sb = ar;
num++; (* Taken from Permutation up to this point *)
SchurTrans = PermutationMatrix[Ordering[sb]] . ClebGor . KroneckerProduct[SchurTrans, SparseArray[IdentityMatrix[2]]] (* Construct the new Schur Transform from the old one, using the product of the direct sum of CG's with the Tensor product of the Schur Transform with Identity (representing adding one more qubit) and multiplying everything by the Permutation Matrix from the left *)
];
Return[SchurTrans]
]


End[];


EndPackage[];


(* ::Section:: *)
(*Workspace*)


(* ::Input:: *)
(*SchurTransform[2]//MatrixForm*)
(*Timing[SchurTransform[11];]*)



