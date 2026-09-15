import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0566Refs : Fin 36 → RowRef 1665 43 := ![.occ 120, .occ 135, .occ 142, .occ 293, .occ 329, .occ 572, .occ 640, .occ 696, .occ 944, .occ 982, .occ 1075, .occ 1097, .occ 1179, .occ 1253, .occ 1259, .occ 1265, .occ 1304, .occ 1328, .occ 1330, .occ 1401, .occ 1417, .occ 1425, .occ 1533, .occ 1607, .occ 1622, .occ 1645, .occ 1659, .sumGe, .nonneg 21, .nonneg 22, .branchGe 15 (1), .branchGe 35 (1), .branchGe 25 (1), .branchGe 29 (1), .branchLe 32 (0), .branchLe 4 (0)]

def plane484GenLeaf0566Mult : Fin 36 → Nat := ![10, 106, 34, 58, 60, 20, 28, 26, 10, 2, 18, 12, 57, 9, 48, 13, 30, 33, 12, 24, 16, 22, 3, 48, 18, 11, 7, 117, 244, 10, 342, 266, 510, 218, 84, 108]

theorem plane484GenLeaf0566 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0566Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0566Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0566Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0566Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 135
  · exact hroot.hOcc 142
  · exact hroot.hOcc 293
  · exact hroot.hOcc 329
  · exact hroot.hOcc 572
  · exact hroot.hOcc 640
  · exact hroot.hOcc 696
  · exact hroot.hOcc 944
  · exact hroot.hOcc 982
  · exact hroot.hOcc 1075
  · exact hroot.hOcc 1097
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1253
  · exact hroot.hOcc 1259
  · exact hroot.hOcc 1265
  · exact hroot.hOcc 1304
  · exact hroot.hOcc 1328
  · exact hroot.hOcc 1330
  · exact hroot.hOcc 1401
  · exact hroot.hOcc 1417
  · exact hroot.hOcc 1425
  · exact hroot.hOcc 1533
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1622
  · exact hroot.hOcc 1645
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4

end QiushiMatmul
