import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0493Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 123, .occ 129, .occ 135, .occ 138, .occ 140, .occ 330, .occ 439, .occ 441, .occ 700, .occ 782, .occ 813, .occ 1147, .occ 1154, .occ 1271, .occ 1302, .occ 1343, .occ 1375, .occ 1380, .occ 1386, .occ 1405, .occ 1406, .occ 1409, .occ 1419, .occ 1432, .occ 1535, .occ 1536, .occ 1590, .occ 1610, .occ 1612, .occ 1622, .occ 1631, .occ 1664, .sumGe, .nonneg 13, .branchGe 15 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 32 (0), .branchLe 14 (0), .branchLe 36 (0), .branchLe 10 (0), .branchLe 11 (0)]

def plane484GenLeaf0493Mult : Fin 44 → Nat := ![2994, 524, 442, 404, 2014, 2406, 339, 708, 367, 3133, 406, 82, 708, 129, 129, 622, 197, 707, 417, 459, 154, 391, 26, 953, 26, 69, 1007, 380, 2785, 154, 263, 393, 1214, 75, 4991, 31, 9949, 4991, 12205, 4991, 571, 2749, 4991, 1398]

theorem plane484GenLeaf0493 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0493Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0493Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0493Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0493Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 129
  · exact hroot.hOcc 135
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 330
  · exact hroot.hOcc 439
  · exact hroot.hOcc 441
  · exact hroot.hOcc 700
  · exact hroot.hOcc 782
  · exact hroot.hOcc 813
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1271
  · exact hroot.hOcc 1302
  · exact hroot.hOcc 1343
  · exact hroot.hOcc 1375
  · exact hroot.hOcc 1380
  · exact hroot.hOcc 1386
  · exact hroot.hOcc 1405
  · exact hroot.hOcc 1406
  · exact hroot.hOcc 1409
  · exact hroot.hOcc 1419
  · exact hroot.hOcc 1432
  · exact hroot.hOcc 1535
  · exact hroot.hOcc 1536
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1612
  · exact hroot.hOcc 1622
  · exact hroot.hOcc 1631
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (11 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11

end QiushiMatmul
