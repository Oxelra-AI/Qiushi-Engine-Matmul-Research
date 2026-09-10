(* Independent verification of the A-slot flattening bound for T_{3,3,3} *)
(* The flattening Phi_A maps the 9x9x9 tensor to a 27x27 matrix *)
(* Phi_A[(i, 3j+k), (j, 3i+k)] = T[3i+j, 3j+k, 3i+k] *)

(* Build T_{3,3,3} over GF(2): T[3i+j, 3j+k, 3i+k] = 1 *)
n = 3;
dim = n^2; (* = 9 *)

(* Build the 27x27 flattening matrix over the integers first *)
PhiA = ConstantArray[0, {27, 27}];
Do[
  row = i*9 + 3*j + k + 1;   (* 1-indexed, (i, 3j+k) *)
  col = j*9 + 3*i + k + 1;   (* 1-indexed, (j, 3i+k) *)
  PhiA[[row, col]] = 1;
, {i, 0, 2}, {j, 0, 2}, {k, 0, 2}];

(* Check it's a permutation matrix *)
Print["PhiA dimensions: ", Dimensions[PhiA]];
Print["Is permutation (each row sum 1): ", AllTrue[Total[PhiA, {2}], # == 1 &]];
Print["Is permutation (each col sum 1): ", AllTrue[Total[PhiA, {1}], # == 1 &]];
Print["Total nonzeros: ", Total[Flatten[PhiA]]];
Print["Determinant: ", Det[PhiA]];
Print["Rank over Q: ", MatrixRank[PhiA]];

(* Check over GF(2) *)
PhiAmod2 = Mod[PhiA, 2];
Print["Rank over GF(2): ", MatrixRank[PhiAmod2, Modulus -> 2]];

(* Verify the permutation structure: (i,j,k) -> (j,i,k) *)
perm = {};
Do[
  row = i*9 + 3*j + k;
  col = j*9 + 3*i + k;
  AppendTo[perm, {row, col}];
, {i, 0, 2}, {j, 0, 2}, {k, 0, 2}];
Print["Permutation pairs (0-indexed): ", Length[perm], " pairs"];
Print["All distinct rows: ", Length[Union[perm[[All, 1]]]] == 27];
Print["All distinct cols: ", Length[Union[perm[[All, 2]]]] == 27];

(* Same for B-slot: Phi_B[(j, 3i+k), (k, 3i+j)] = T[3i+j, 3j+k, 3i+k] *)
PhiB = ConstantArray[0, {27, 27}];
Do[
  row = j*9 + 3*i + k + 1;
  col = k*9 + 3*i + j + 1;
  PhiB[[row, col]] = 1;
, {i, 0, 2}, {j, 0, 2}, {k, 0, 2}];
Print["PhiB rank over Q: ", MatrixRank[PhiB]];
Print["PhiB rank over GF(2): ", MatrixRank[Mod[PhiB, 2], Modulus -> 2]];
Print["PhiB is permutation: ", Det[PhiB]];

Print["VERIFICATION COMPLETE"];
