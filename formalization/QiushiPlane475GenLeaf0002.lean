import QiushiPlane475GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane475GenLeaf0002Refs : Fin 57 → RowRef 126 56 := ![.occ 10, .occ 11, .occ 15, .occ 16, .occ 22, .occ 25, .occ 26, .occ 34, .occ 37, .occ 46, .occ 47, .occ 51, .occ 52, .occ 54, .occ 55, .occ 57, .occ 63, .occ 64, .occ 66, .occ 67, .occ 69, .occ 74, .occ 77, .occ 79, .occ 84, .occ 85, .occ 93, .occ 95, .occ 97, .occ 98, .occ 99, .occ 103, .occ 104, .occ 106, .occ 107, .occ 109, .occ 111, .occ 112, .occ 114, .occ 116, .occ 119, .occ 120, .occ 125, .sumGe, .nonneg 0, .nonneg 3, .nonneg 7, .nonneg 12, .nonneg 22, .nonneg 37, .nonneg 43, .nonneg 50, .nonneg 51, .nonneg 52, .nonneg 54, .branchGe 34 (1), .branchLe 27 (0)]

def plane475GenLeaf0002Mult : Fin 57 → Nat := ![191317, 186720, 126021, 156976, 65552, 3833, 156317, 169445, 42319, 1530, 74119, 43213, 34803, 13474, 2440, 9918, 10127, 63816, 118650, 35942, 9027, 13067, 8458, 26769, 6126, 31534, 64806, 38602, 36554, 6762, 41151, 32247, 72620, 99826, 16838, 38941, 12952, 77498, 87283, 23181, 50340, 6031, 8980, 243613, 85372, 33502, 37432, 114561, 10691, 7919, 158903, 7448, 51631, 230646, 13991, 1475970, 243613]

theorem plane475GenLeaf0002 (x : Fin 56 → Int)
    (hroot : plane475GenOccSys.RootHolds x)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane475GenLeaf0002Refs i).resolveCoeff plane475GenOccSys j)
    (fun i => (plane475GenLeaf0002Refs i).resolveRhs plane475GenOccSys) plane475GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane475GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 10
  · exact hroot.hOcc 11
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 22
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 34
  · exact hroot.hOcc 37
  · exact hroot.hOcc 46
  · exact hroot.hOcc 47
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 54
  · exact hroot.hOcc 55
  · exact hroot.hOcc 57
  · exact hroot.hOcc 63
  · exact hroot.hOcc 64
  · exact hroot.hOcc 66
  · exact hroot.hOcc 67
  · exact hroot.hOcc 69
  · exact hroot.hOcc 74
  · exact hroot.hOcc 77
  · exact hroot.hOcc 79
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 97
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 109
  · exact hroot.hOcc 111
  · exact hroot.hOcc 112
  · exact hroot.hOcc 114
  · exact hroot.hOcc 116
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 125
  · change (∑ j, (-1 : Int) * x j) ≤ -plane475GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (3 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (7 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (12 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (22 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (37 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (43 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (50 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (51 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (52 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (54 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (34 : Fin 56) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (27 : Fin 56) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27

end QiushiMatmul
