(* ::Package:: *)

(* ::Title:: *)
(*Schur Transform*)


(* ::Text:: *)
(*The general idea behind this algorithm is to implement the Schur Transform recursively, through applying a direct sum of relevant CG transforms for irreps of a Schur basis of n qubits to a Tensor product of a Schur Transform for n qubits and a 2x2 Identity matrix (this tensor product with identity represents adding a new qubit), thus obtaining something like a Schur Transform for n+1 qubits, although with certain rows disordered. We then have to apply a certain permutation matrix in order to obtain the true Schur Transform for n+1 qubits.*)
(*The CG transform, when acting on an irrep of dimensionality d of n-qubit Schur basis, outputs two irreps of n+1-qubit Schur basis, one of them with dimensionality d+1 and the other with dimensionality d-1.*)


(* ::Section:: *)
(*Initialization*)


BeginPackage["STPackage`"];


(* ::Text:: *)
(*Clear everything in case the package was already loaded before.*)


Unprotect["STPackage`*"];
ClearAll["STPackage`*"];
ClearAll["STPackage`Private`*"];


(* ::Text:: *)
(*Description of the externally available SchurTransform function.*)


SchurTransform::usage = "SchurTransform[n] outputs a Schur Transform for n qubits.";


Begin["`Private`"];


(* ::Section:: *)
(*Clebsch-Gordan coefficients*)


(* ::Text:: *)
(*Here we implement the Clebsch-Gordan (CG) transform for a subspace (irrep) of dimension d.*)


(* ::Text:: *)
(*First, we need to compute the Clebsch-Gordan coefficients . We will use the following parameters :*)


(* ::Item:: *)
(*l = 2 j = overhang*)


(* ::Item:: *)
(*w = j - m = Hamming weight of the overhang \[Element] [0, l]*)


(* ::Item:: *)
(*\[CapitalDelta]l \[Element] {-1, +1} change in overhang*)


(* ::Item:: *)
(*x \[Element] {0, 1} the new symbol*)


(* ::Text:: *)
(*Example:*)
(*When j = 1/2 the overhang is l = 1 and the Hamming weight can be either 0 or 1.*)
(*The possible values of m are +1/2 and m = -1/2, which turn into w = 0 and w = 1 represented by qubit state |w>.*)


(* ::Text:: *)
(*Our expression is based on a formula from Wikipedia:*)
(*https://en.wikipedia.org/wiki/Clebsch%E2%80%93Gordan_coefficients#Special_cases*)


CG[l_,w_,\[CapitalDelta]l_,x_]:=If[x==0,\[CapitalDelta]l,1] 1/Sqrt[2] Sqrt[(l+1+\[CapitalDelta]l(1-2 x)(l+1-2 (w+x)))/(l+1)];


(* ::Text:: *)
(*We directly produce the Clebsch-Gordan transform as a sparse array with non-zero values being the CG coefficients at specific positions in the matrix.*)
(*The rows of this matrix are labeled by overhang l (or spin j) and weight w (or magnetic number m).*)
(*The columns are labeled by pairs (i,x) where i \[Element] {0,...,d} and x \[Element] {0,1} which are recalculated into a single index in {1,...,2d}.*)


CGTransform[d_]:=Module[{l1,l2,l3,l4},
	(* Increase overhang: \[CapitalDelta]l = 1 *)
	l1=Table[{i+1,2i}->CG[d-1,i-1,1,1],{i,1,d}];(* x = 0 *)
	l2=Table[{i+1,2i+1}->CG[d-1,i,1,0],{i,0,d-1}];(* x = 1 *)
	(* Decrease overhang: \[CapitalDelta]l = -1 *)
	l3=Table[{(d+1)+i+1,2i+2}->CG[d-1,i,-1,1],{i,0,d-2}];(* x = 1 *)
	l4=Table[{(d+1)+i+1,2i+2+1}->CG[d-1,i+1,-1,0],{i,0,d-2}];(* x = 0 *)
	SparseArray[Join[l1,l2,l3,l4],{2d,2d}]
];


(* ::Text:: *)
(*Direct sum of a given list of matrices .*)


DirectSum[lst_]:=ArrayFlatten@ReleaseHold@DiagonalMatrix[Hold/@lst];


(* ::Text:: *)
(*Direct sum of many smaller Clebsch - Gordan transforms .*)


BigCGTransform[n_]:=DirectSum@Flatten[Table[ConstantArray[CGTransform[NumSSYT[n,\[Lambda]2]],NumSYT[n,\[Lambda]2]],{\[Lambda]2,0,Quotient[n,2]}],1];


(* ::Section:: *)
(*Auxiliary functions for implementing the Schur basis*)


(* ::Text:: *)
(*In this step we implement a representation of the Schur basis that uniquely defines every independent basis state. This representation is equivalent to the classic one, which consists of three main components: partition, a Standard Young Tableux (SYT) and a Semi-Standard Young Tableau (SSYT). *)
(*We also define some auxiliary functions that help to manipulate and construct new basis elements for higher number of qubits from lower number of qubits (specifically, by adding one qubit).*)


(* ::Text:: *)
(*Here is how we represent the Schur basis for one qubit. Every element on the first level is a basis element. Inside every basis element, so on the second level, there are four elements:*)


(* ::Item:: *)
(*first represents the partition, where the first element in the partition is the number of boxes (elements) in the second row of SYT (and SSYT) and the second *)
(* element is the number of boxes in the first row of SYT (and SSYT) (for example : {2, 4} means there are 2 boxes in second row of SYT and 4 in the first);*)


(* ::Item:: *)
(*second represents the first row of SYT, with its elements being the numbers in boxes of the first row of SYT (in order);*)


(* ::Item:: *)
(*third represents the second row of SYT, with its elements being the numbers in boxes of the second row of SYT (in order, shares order with the first row);*)


(* ::Item:: *)
(*fourth represents the Hamming weight of the overhang, which, given a partition, uniquely determines the SSYT.*)


(* ::Text:: *)
(*Example for second and third component:*)
(*{1,2,4},{3,5} means that the first two qubits have their total spin (total angular momentum) added (1,2 in first row), for the third qubit the total spin (1/2 for one qubit) is subtracted from the total spin of the system (i.e. J3 = J2 - 1/2; 3 in the second row), the total spin of fourth qubit was added (4 in first) and total spin of fifth qubit was subtracted (5 in second).*)


SchurBasis0={{{0,1},{1},{},{0}},{{0,1},{1},{},{1}}};


(* ::Text:: *)
(*Given the total number of boxes (qubits) 'n' in SSYT and the number of boxes in the second row 'l2', computes the number of SSYT's with these parameters.*)


NumSSYT[n_,l2_]:=n-2*l2+1;


(* ::Text:: *)
(*Given the total number of boxes (qubits) 'n' in SYT and the number of boxes in the second row 'l2', computes the number of SYT's with these parameters.*)


NumSYT[n_,l2_]:= Binomial[n+1,l2]*(n-2*l2+1)/(n+1);


(* ::Text:: *)
(*Supporting function for AddFirst, represents adding a box (qubit) to the first row of the Young Tableau for a given basis element 'a', thus increasing the second entry in partition by one i.e. increasing the number of elements in the first row and adding a number that is next in order to the SYT first row entry, i.e. for an SYT of {1,2,4} {3,5} it adds 6 to the first row entry turning the SYT into {1,2,4,6} {3,5}.*)


AddFirst0[{{\[Lambda]2_,\[Lambda]1_},row1_,row2_,m_}]:={{\[Lambda]2,\[Lambda]1+1},Append[row1,\[Lambda]1+\[Lambda]2+1],row2,m}; 


(* ::Text:: *)
(*Adds a box (qubit) to the first row for every basis element in a given set 'lst' i.e. applies AddFirst0 to every basis element in a given set and then adds a new basis element to the set with max Hamming weight increased by one because the number of SSYT's gets increased by one.*)


AddFirst[lst_]:= Module[{lstnew,last},
	lstnew=Map[AddFirst0,lst];
	last=lstnew[[-1]];
	last[[4,1]]++;
	Append[lstnew,last]
];


(* ::Text:: *)
(*Supporting function for AddSecond, represents adding a box (qubit) to the second row of the Young Tableau for a given basis element 'a', thus increasing the first entry in partition by one i.e. increasing the number of elements in the second row and adding a number that is next in order to the SYT second row entry, i.e. for an SYT of {1,2,4} {3,5} it adds 6 to the second row entry turning the SYT into {1,2,4} {3,5,6}.*)


AddSecond0[{{\[Lambda]2_,\[Lambda]1_},row1_,row2_,m_}]:={{\[Lambda]2+1,\[Lambda]1},row1,Append[row2,\[Lambda]1+\[Lambda]2+1],m};


(* ::Text:: *)
(*Adds a box (qubit) to the second row for every basis element in a given set 'lst' i.e. applies AddSecond0 to every basis element in a given set and then deletes the last basis element in this set because the number of SSYT's gets decreased by one.*)


AddSecond[lst_]:=Map[AddSecond0,Most[lst]];


(* ::Section:: *)
(*Permutation for CG*)


(* ::Text:: *)
(*This step is more for the showcase of this important part in the algorithm, because afterwards the Permutation function is merged with the CG recursion step to form the Schur Transform, as this way the implementation is faster.*)
(*This part computes the permutation matrix that we have to apply after the CG recursive step. This permutation is needed because the CG recursion outputs a direct sum of all higher and lower irreps in order in n+1 qubit space for every irrep in n qubit space. So, for example, for a direct sum of irreps (ir1, ir2, ir3) in this order it would output a direct sum of irreps (Higher[ir1], Lower[ir1], Higher[ir2], Lower[ir2], Higher[ir3], Lower[ir3]) in this order, but this is not necessarily the correct order in which the Schur Transform should order the irreps (or blocks, if applied to matrices). Say, if (ir1, ir2, ir3) have dimensions (6, 4, 4) respectively, the output would have dimensions (7, 5, 5, 3, 5, 3) in this order, while the actual order should have been: (7, 5, 5, 5, 3, 3).*)
(*This step utilizes the Schur Basis depiction introduced earlier in order to modify the basis in the same way the CG recursion step does and obtain a basis for a higher number of qubits, but disordered in the same way as the result of the CG recursion step. We then apply Ordering to the disordered Schur Basis depiction and obtain a permutation vector, that essentially gives us the needed permutation to get the true Schur Transform.*)


(* ::Code:: *)
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


SchurTransform[n_]:=Module[{counter,subsp,ar,sb,num,BigCG,SchurTrans},
	sb=SchurBasis0;
	SchurTrans=SparseArray[IdentityMatrix[2]]; (* Schur Transform for 1 qubit *)
	Do[
		sb=Sort[sb];
		ar={};
		counter=1;
		(* The first CG in direct sum with the highest dimensionality for the irrep, i.e. all boxes in first row *)
		Do[
			subsp=sb[[counter;;counter+NumSSYT[num,l2]-1]];
			ar=Join[ar,AddFirst[subsp],AddSecond[subsp]];
			counter=counter+NumSSYT[num,l2];
			,{l2,0,Quotient[num,2]}
			,{NumSYT[num,l2]}
		];
		BigCG=BigCGTransform[num];
		sb=ar;
		(* Construct the new Schur Transform from the old one, using the product of the direct sum of CG's *)
		(* with the Tensor product of the Schur Transform with Identity (representing adding one more qubit) *)
		(* and multiplying everything by the Permutation Matrix from the left *)
		SchurTrans=PermutationMatrix[Ordering[sb]] . BigCG . KroneckerProduct[SchurTrans,SparseArray[IdentityMatrix[2]]];
	,{num,1,n-1}];
	SchurTrans
];


(* ::Section:: *)
(*End of package*)


End[];


EndPackage[];


(* ::Section:: *)
(*Tests*)


Table[SchurTransform[k] // MatrixForm, {k, 1, 3}]
And @@ Table[SchurTransform[k] . SchurTransform[k]\[ConjugateTranspose] == IdentityMatrix[2^k], {k, 1, 6}]


Timing[SchurTransform[11];]


RepeatedTiming[SchurTransform[11];]
