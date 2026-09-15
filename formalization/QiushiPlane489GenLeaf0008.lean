import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0008Refs : Fin 33 → RowRef 371 32 := ![.occ 96, .occ 99, .occ 104, .occ 105, .occ 115, .occ 125, .occ 126, .occ 148, .occ 149, .occ 161, .occ 164, .occ 176, .occ 194, .occ 202, .occ 306, .occ 308, .occ 313, .occ 322, .occ 330, .occ 337, .occ 340, .occ 344, .occ 348, .occ 360, .sumGe, .branchLe 14 (0), .branchLe 9 (0), .branchGe 31 (1), .branchLe 23 (0), .branchLe 4 (0), .branchGe 12 (1), .branchLe 18 (0), .branchGe 10 (1)]

def plane489GenLeaf0008Mult : Fin 33 → Nat := ![92, 49, 112, 88, 276, 109, 246, 51, 146, 43, 51, 162, 62, 100, 30, 90, 35, 75, 66, 117, 35, 75, 40, 58, 351, 258, 351, 150, 132, 246, 658, 261, 649]

theorem plane489GenLeaf0008 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0008Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0008Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0008Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 96
  · exact hroot.hOcc 99
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 115
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 148
  · exact hroot.hOcc 149
  · exact hroot.hOcc 161
  · exact hroot.hOcc 164
  · exact hroot.hOcc 176
  · exact hroot.hOcc 194
  · exact hroot.hOcc 202
  · exact hroot.hOcc 306
  · exact hroot.hOcc 308
  · exact hroot.hOcc 313
  · exact hroot.hOcc 322
  · exact hroot.hOcc 330
  · exact hroot.hOcc 337
  · exact hroot.hOcc 340
  · exact hroot.hOcc 344
  · exact hroot.hOcc 348
  · exact hroot.hOcc 360
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (9 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (31 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (23 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (4 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (12 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (18 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (10 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
