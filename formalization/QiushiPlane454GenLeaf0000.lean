import QiushiPlane454GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane454GenLeaf0000Refs : Fin 56 → RowRef 174 55 := ![.occ 17, .occ 20, .occ 24, .occ 27, .occ 30, .occ 35, .occ 37, .occ 42, .occ 44, .occ 45, .occ 51, .occ 52, .occ 56, .occ 58, .occ 64, .occ 69, .occ 72, .occ 76, .occ 78, .occ 79, .occ 81, .occ 85, .occ 89, .occ 100, .occ 103, .occ 109, .occ 110, .occ 111, .occ 112, .occ 117, .occ 122, .occ 127, .occ 128, .occ 129, .occ 130, .occ 140, .occ 141, .occ 143, .occ 145, .occ 146, .occ 149, .occ 152, .occ 158, .occ 160, .sumGe, .nonneg 13, .nonneg 15, .nonneg 17, .nonneg 24, .nonneg 27, .nonneg 29, .nonneg 54, .branchLe 2 (0), .branchLe 4 (0), .branchLe 12 (0), .branchLe 26 (0)]

def plane454GenLeaf0000Mult : Fin 56 → Nat := ![30224, 87118, 93148, 44996, 48980, 30752, 44464, 77902, 77986, 50752, 62122, 10472, 45812, 21730, 128848, 30106, 60526, 82450, 1444, 25930, 121332, 15752, 127066, 17240, 29241, 55740, 47261, 85806, 10074, 10044, 15733, 21129, 46393, 6167, 8073, 22427, 27970, 87773, 7486, 12174, 1268, 27851, 12359, 17936, 256287, 86114, 8890, 112624, 24332, 54292, 37928, 4150, 240554, 243928, 150880, 203240]

theorem plane454GenLeaf0000 (x : Fin 55 → Int)
    (hroot : plane454GenOccSys.RootHolds x)
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane454GenLeaf0000Refs i).resolveCoeff plane454GenOccSys j)
    (fun i => (plane454GenLeaf0000Refs i).resolveRhs plane454GenOccSys) plane454GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane454GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 17
  · exact hroot.hOcc 20
  · exact hroot.hOcc 24
  · exact hroot.hOcc 27
  · exact hroot.hOcc 30
  · exact hroot.hOcc 35
  · exact hroot.hOcc 37
  · exact hroot.hOcc 42
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 56
  · exact hroot.hOcc 58
  · exact hroot.hOcc 64
  · exact hroot.hOcc 69
  · exact hroot.hOcc 72
  · exact hroot.hOcc 76
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 85
  · exact hroot.hOcc 89
  · exact hroot.hOcc 100
  · exact hroot.hOcc 103
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 112
  · exact hroot.hOcc 117
  · exact hroot.hOcc 122
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 143
  · exact hroot.hOcc 145
  · exact hroot.hOcc 146
  · exact hroot.hOcc 149
  · exact hroot.hOcc 152
  · exact hroot.hOcc 158
  · exact hroot.hOcc 160
  · change (∑ j, (-1 : Int) * x j) ≤ -plane454GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (15 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (17 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (24 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (27 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (29 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (54 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (2 : Fin 55) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (4 : Fin 55) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (12 : Fin 55) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (26 : Fin 55) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26

end QiushiMatmul
