import QiushiPlane457GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane457GenLeaf0004Refs : Fin 50 → RowRef 178 49 := ![.occ 27, .occ 31, .occ 33, .occ 34, .occ 36, .occ 38, .occ 40, .occ 46, .occ 52, .occ 63, .occ 67, .occ 68, .occ 69, .occ 73, .occ 77, .occ 81, .occ 82, .occ 83, .occ 86, .occ 90, .occ 93, .occ 95, .occ 96, .occ 97, .occ 98, .occ 100, .occ 105, .occ 106, .occ 112, .occ 116, .occ 121, .occ 124, .occ 128, .occ 138, .occ 146, .occ 154, .occ 155, .occ 160, .occ 161, .occ 167, .occ 175, .sumGe, .nonneg 6, .nonneg 8, .nonneg 11, .nonneg 43, .branchGe 3 (1), .branchLe 23 (0), .branchLe 26 (0), .branchGe 35 (1)]

def plane457GenLeaf0004Mult : Fin 50 → Nat := ![269, 468, 414, 286, 1095, 259, 1330, 1659, 253, 1055, 197, 1146, 1222, 701, 461, 527, 522, 55, 864, 353, 753, 82, 500, 301, 980, 168, 224, 174, 1091, 441, 574, 508, 180, 522, 245, 5, 24, 72, 616, 123, 19, 1863, 1793, 2133, 505, 967, 4851, 1341, 1336, 9665]

theorem plane457GenLeaf0004 (x : Fin 49 → Int)
    (hroot : plane457GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane457GenLeaf0004Refs i).resolveCoeff plane457GenOccSys j)
    (fun i => (plane457GenLeaf0004Refs i).resolveRhs plane457GenOccSys) plane457GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane457GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 27
  · exact hroot.hOcc 31
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 36
  · exact hroot.hOcc 38
  · exact hroot.hOcc 40
  · exact hroot.hOcc 46
  · exact hroot.hOcc 52
  · exact hroot.hOcc 63
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 69
  · exact hroot.hOcc 73
  · exact hroot.hOcc 77
  · exact hroot.hOcc 81
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 86
  · exact hroot.hOcc 90
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 97
  · exact hroot.hOcc 98
  · exact hroot.hOcc 100
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 112
  · exact hroot.hOcc 116
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 128
  · exact hroot.hOcc 138
  · exact hroot.hOcc 146
  · exact hroot.hOcc 154
  · exact hroot.hOcc 155
  · exact hroot.hOcc 160
  · exact hroot.hOcc 161
  · exact hroot.hOcc 167
  · exact hroot.hOcc 175
  · change (∑ j, (-1 : Int) * x j) ≤ -plane457GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (8 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (11 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (43 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (3 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (23 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (35 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35

end QiushiMatmul
