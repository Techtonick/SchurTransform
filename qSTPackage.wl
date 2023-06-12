(* ::Package:: *)

(* ::Title:: *)
(*q-Schur Transform*)


(* ::Text:: *)
(*The q-Schur Transform (q-deformed Schur Transform) is a generalisation of the Schur Transform based on the so called q-Clebsch-Gordan (qCG) transform instead of the regular Clebsch-Gordan transform. The generalisation consists in extension of the application of the transform, from U(2) group to the so called Quantum U(2) Group (see Klimyk & Schmudgen "Quantum Groups and Their Representations"), which is generally non-commutative, so then the q-ST is able to transform n-tensored matrices (elements) of the Quantum U(2) Group with arbitrary commutation parameter q. When q=1 we recover the standard Schur Transform.*)
(*The general idea behind this algorithm is to implement the q-Schur Transform recursively, through applying a direct sum of relevant qCG transforms for irreps of a q-Schur basis of n qubits to a Tensor product of a     q-Schur Transform for n qubits and a 2x2 Identity matrix (this tensor product with identity represents adding a new qubit), thus obtaining something like a q-Schur Transform for n+1 qubits, although with certain rows disordered. We then have to apply a certain permutation matrix in order to obtain the true q-Schur Transform for n+1 qubits.*)
(*The qCG transform, when acting on an irrep of dimensionality d of n-qubit q-Schur basis, outputs two irreps of n+1-qubit q-Schur basis, one of them with dimensionality d+1 and the other with dimensionality d-1.*)
(**)
(*Note that the idea behind this q-Schur Transform is analogous to the one in the package STPackage with the Schur Transform. It's only the formula for the CG transform that changes to qCG.*)


(* ::Section:: *)
(*Initialization*)


BeginPackage["STPackage`"];


(* ::Text:: *)
(*Clear everything in case the package was already loaded before.*)


Unprotect["STPackage`*"];
ClearAll["STPackage`*"];
ClearAll["STPackage`Private`*"];


(* ::Text:: *)
(*Description of the externally available QSchurTransform function.*)


QSchurTransform::usage = "QSchurTransform[n] outputs a q-Schur Transform for n qubits.";
q::usage = "The commutation parameter q.";


Begin["`Private`"];


(* ::Section:: *)
(*q-Clebsch-Gordan coefficients*)


(* ::Text:: *)
(*Here we implement the q-Clebsch-Gordan (qCG) transform for a subspace (irrep) of dimension d.*)


(* ::Text:: *)
(*First, we need to compute the q-Clebsch-Gordan coefficients . We will use the following parameters :*)


(* ::Item:: *)
(*l \[LongDash] spin of the initial state l = l1*)


(* ::Item:: *)
(*j \[LongDash] magnetic number (spin projection) of the initial state j = j1 \[Element] [-l, l]*)


(* ::Item:: *)
(*s \[Element] {-1, +1} \[LongDash] sign of the magnetic number of the added qubit state (sign of j2 = \[PlusMinus]1/2)*)


(* ::Item:: *)
(*the first entries (1 and 2) label:    1 \[LongDash] adding the spins l1 and l2, i.e.  l1 + l2 = l + 1/2;    2 \[LongDash] subtracting the spins l1 and l2, i.e.  l1 - l2 = l - 1/2*)


(* ::Text:: *)
(*Our expression is based on a formula from Klimyk&Schmudgen "Quantum Groups and Their Representations" p .81,eqs.(68),(69). The notation used in the formula is the same as in this expression.*)


(*Quantum integer*)Q[a_]:=(q^a-q^-a)/(q-q^-1);
(*Clebsch-Gordan coefficients from Klimyk& Schmudgen "Quantum Groups" p.81,eqs.(68),(69)*)
(*Adding box to 1st row*)
QCG[1,l_,j_,s_]:=q^(s (l-s j)/2) Sqrt[Q[l+s j+1]/Q[2 l+1]];
(*Adding box to 2nd row*)
QCG[2,l_,j_,s_]:=-s q^(-s (l+s j+1)/2) Sqrt[Q[l-s j]/Q[2 l+1]];
(*Clebsch-Gordan transform on 2 qubits*)


(* ::Text:: *)
(*Given the total number of boxes (qubits) ' n' in Semi-Standard Young Tableau (SSYT) and the number of boxes in the second row ' l2', computes the number of SSYT' s with these parameters .*)


NumSSYT[n_,l2_]:=n-2*l2+1;


(* ::Text:: *)
(*Given the total number of boxes (qubits) 'n' in Standard Young Tableau (SYT) and the number of boxes in the second row 'l2', computes the number of SYT's with these parameters.*)


NumSYT[n_,l2_]:= Binomial[n+1,l2]*(n-2*l2+1)/(n+1);


(* ::Text:: *)
(*We directly produce the q-Clebsch-Gordan transform as a sparse array with non-zero values being the q-CG coefficients at specific positions in the matrix.*)
(*The rows of this matrix are labeled by total spin J=j1+j2 and total magnetic number M=m1+m2, where M ranges (in the rows order) first from (j1+1/2) to (-j1-1/2) and then from (j1-1/2) to (-j1+1/2).*)
(*The columns are labeled by pairs (m1,m2) with m1 being the magnetic number of the initial system state to which we are adding a qubit, and m2 being the magnetic number of the added qubit, i.e. m1 ranges from -j1 to j1 and m2 ranges from -1/2 to 1/2. The order of the pairs  is from largest to smallest in dictionary order (example: 1st column is m1=j1, m2=1/2; 2nd column is m1=j1, m2=-1/2; 3rd is m1=j1-1, m2=1/2; ...).*)


QCGTransform[d_]:=Module[{tab,i,j},
	tab = ConstantArray[0,{2d,2d}];
	tab[[1,1]]=QCG[1,(d-1)/2,(d-1)/2,1];
	tab[[d+1,2d]]=QCG[1,(d-1)/2,-(d-1)/2,-1];
	i=2;
	j=2;
	Do[
		tab[[i,j]]=QCG[1,(d-1)/2,(d-1)/2-(i-2),-1];
		tab[[i,j+1]]=QCG[1,(d-1)/2,(d-1)/2-(i-1),1];
		i++;
		j=j+2;
		,d-1];
	i=d+2;
	j=2;
	Do[
		tab[[i,j]]=QCG[2,(d-1)/2,(d-1)/2-(i-d-2),-1];
		tab[[i,j+1]]=QCG[2,(d-1)/2,(d-1)/2-(i-d-1),1];
		i++;
		j=j+2;
		,d-1];
	SparseArray[tab]
];


(* ::Text:: *)
(*Direct sum of a given list of matrices .*)


DirectSum[lst_]:=ArrayFlatten@ReleaseHold@DiagonalMatrix[Hold/@lst];


(* ::Text:: *)
(*Direct sum of many smaller q-Clebsch-Gordan transforms .*)


BigQCGTransform[n_]:=DirectSum@Flatten[Table[ConstantArray[QCGTransform[NumSSYT[n,\[Lambda]2]],NumSYT[n,\[Lambda]2]],{\[Lambda]2,0,Quotient[n,2]}],1];


(* ::Section:: *)
(*Auxiliary functions for implementing the Schur basis*)


(* ::Text:: *)
(*In this step we implement a representation of the q-Schur basis that uniquely defines every independent basis state. This representation is equivalent to the classic one, which consists of three main components: partition, a Standard Young Tableau (SYT) and a Semi-Standard Young Tableau (SSYT). *)
(*We also define some auxiliary functions that help to manipulate and construct new basis elements for higher number of qubits from lower number of qubits (specifically, by adding one qubit).*)


(* ::Text:: *)
(*Here is how we represent the q-Schur basis for one qubit. Every element on the first level is a basis element. Inside every basis element, so on the second level, there are four elements:*)


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


QSchurBasis0={{{0,1},{1},{},{0}},{{0,1},{1},{},{1}}};


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
(*This step is more for the showcase of this important part in the algorithm, because afterwards the Permutation function is merged with the qCG recursion step to form the q-Schur Transform, as this way the implementation is faster.*)
(*This part computes the permutation matrix that we have to apply after the qCG recursive step. This permutation is needed because the qCG recursion outputs a direct sum of all higher and lower irreps in order in n+1 qubit space for every irrep in n qubit space. So, for example, for a direct sum of irreps (ir1, ir2, ir3) in this order it would output a direct sum of irreps (Higher[ir1], Lower[ir1], Higher[ir2], Lower[ir2], Higher[ir3], Lower[ir3]) in this order, but this is not necessarily the correct order in which the q-Schur Transform should order the irreps (or blocks, if applied to matrices). Say, if (ir1, ir2, ir3) have dimensions (6, 4, 4) respectively, the output would have dimensions (7, 5, 5, 3, 5, 3) in this order, while the actual order should have been: (7, 5, 5, 5, 3, 3).*)
(*This step utilizes the q-Schur Basis depiction (representation) introduced earlier in order to modify the basis in the same way the qCG recursion step does and obtain a basis for a higher number of qubits, but disordered in the same way as the result of the qCG recursion step. We then apply Ordering to the disordered q-Schur Basis depiction and obtain a permutation vector, that essentially gives us the needed permutation to get the true q-Schur Transform.*)


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
(*q-Schur Transform through qCG and Permutation*)


(* ::Text:: *)
(*In this step we implement the q-Schur Transform itself by combining qCG recursion and Permutation.  It's natural to combine these two parts of the algorithm as they exist within the same recursion.*)
(*Everything is implemented through Sparse Arrays to make it faster.*)


(* ::Code:: *)
(*(* Labels for one-qubit q-Schur basis states *)*)
(*SchurBasis[1]={{{0,1},{1},{},{0}},{{0,1},{1},{},{1}}};*)
(*(* Labels for n-qubit q-Schur basis states *)*)
(*SchurBasis[n_]:=SchurBasis[n]=Module[{newsb,counter,subsp},*)
(*	sb=SchurBasis[n-1];*)
(*	counter=1;*)
(*	newsb=Table[*)
(*		subsp=sb[[counter;;counter+NumSSYT[n-1,l2]-1]];*)
(*		counter=counter+NumSSYT[n-1,l2];*)
(*		{AddFirst[subsp],AddSecond[subsp]}*)
(*		,{l2,0,Quotient[n-1,2]}*)
(*		,{NumSYT[n-1,l2]}*)
(*	];*)
(*	Flatten[newsb,3]*)
(*];*)


(* Extend a given list of q-Schur basis labels from n-1 to n qubits *)
ExtendSchurBasis[sb_,n_]:=Module[{newsb,counter,subsp},
	counter=1;
	newsb=Table[
		subsp=sb[[counter;;counter+NumSSYT[n-1,l2]-1]];
		counter=counter+NumSSYT[n-1,l2];
		{AddFirst[subsp],AddSecond[subsp]}
		,{l2,0,Quotient[n-1,2]}
		,{NumSYT[n-1,l2]}
	];
	Flatten[newsb,3]
];


QSchurTransform[n_]:=Module[{QSchurTrans,sb,Id=SparseArray@IdentityMatrix[2]},
	(* q-Schur basis labels for 1 qubit *)
	sb={{{0,1},{1},{},{0}},{{0,1},{1},{},{1}}};
	(* q-Schur Transform for 1 qubit *)
	QSchurTrans=Id;
	(* Build up the q-Schur transform recursively *)
	Do[QSchurTrans=PermutationMatrix[Ordering[sb=ExtendSchurBasis[Sort@sb,m]]] . BigQCGTransform[m-1] . KroneckerProduct[QSchurTrans,Id];,{m,2,n}];
	QSchurTrans
];


(* ::Section:: *)
(*End of package*)


End[];


EndPackage[];


(* ::Section:: *)
(*Tests*)


Table[Normal[QSchurTransform[k]] // FullSimplify // MatrixForm, {k, 1, 3}]
And @@ Table[FullSimplify[Normal[QSchurTransform[k] . Transpose[QSchurTransform[k]]]] == IdentityMatrix[2^k], {k, 1, 6}]


Timing[QSchurTransform[8];]


RepeatedTiming[QSchurTransform[8];]


(* ::Text:: *)
(*Here we test if the q-Schur Transform actually transforms the n-times tensored matrix quantum group elements.*)
(*Initialize the matrix entries of an arbitrary matrix quantum group element T = { {a, b}, {c, d} } :*)


a;
b;
c;
d;


(* ::Text:: *)
(*Define the relations that a, b, c, d satisfy:*)
(*[*Note: a, b, c, d are non-commuting operators, relations were taken from https://arxiv.org/abs/2202.06937 , f acts like a non-commutative multiplication of all elements in its argument list]*)


Clear[f];
f[{x___,b,a,y___}]:=q*f[{x,a,b,y}];
f[{x___,c,a,y___}]:=q*f[{x,a,c,y}];
f[{x___,d,b,y___}]:=q*f[{x,b,d,y}];
f[{x___,d,c,y___}]:=q *f[{x,c,d,y}];
f[{x___,c,b,y___}]:=f[{x,b,c,y}];
f[{x___,d,a,y___}]:=f[{x,a,d,y}]+(q-q^-1)*f[{x,b,c,y}];
f[{x___,a,d,y___}]:=q^-1*f[{x,b,c,y}]+1;
f[{x___,a_,a_,y___}]:=f[{x,a^2,y}];
f[{x___,a_^k_,a_,y___}]:=f[{x,a^(k+1),y}];
f[{x___,a_,a_^k_,y___}]:=f[{x,a^(k+1),y}];
f[{x___,a_^k_,a_^m_,y___}]:=f[{x,a^(k+m),y}];


(* ::Text:: *)
(*Define the T^(\[TensorProduct]n) non-commutative Tensor (Kronecker) Product for T :*)


NCTensorProd[n_]:=Module[{M,TGate=({
 {{a}, {b}},
 {{c}, {d}}
})},
	If[n==1,
	(* In case n=1, don't tensor anything and just return T *)
		Return[SparseArray[({
 {a, b},
 {c, d}
})]],
	(* Else do the following steps: *)
		M=({
 {{a}, {b}},
 {{c}, {d}}
}); 
		(* Construct a concatenated Matrix recursively n-1 times, on each step concatanating two matrices of lists that show in which order the elements were added;
		each resulting matrix element is a list showing order of multiplication of the matrix elements of the initial matrices (same order as in non-commutative Tensor product) *)
		Do[
		M=Flatten[Table[Join[M[[i,j]],TGate[[k,l]]],{i,Length[M]},{j,Length[M]},{k,Length[TGate]},{l,Length[TGate]}],{{1,3},{2,4}}],
		n-1]; 
		(* Apply f to each element (list) in the resulting matrix *)
		Return[SparseArray[Table[f[M[[i,j]]],{i,Length[M]},{j,Length[M]}]]]
	]
]


(* ::Text:: *)
(*Matrix form in the computational basis:*)


NCTensorProd[2] // MatrixForm


(* ::Text:: *)
(*Test that the q-Schur Transform transforms the matrix to the q-Schur Basis:*)


FullSimplify[Normal[QSchurTransform[2] . NCTensorProd[2] . QSchurTransform[2]\[ConjugateTranspose]], q \[Element] Reals] // MatrixForm
