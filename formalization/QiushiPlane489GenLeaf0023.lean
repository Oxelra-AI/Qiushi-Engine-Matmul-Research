import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0023Refs : Fin 33 → RowRef 371 32 := ![.occ 95, .occ 104, .occ 105, .occ 127, .occ 128, .occ 137, .occ 139, .occ 176, .occ 188, .occ 202, .occ 203, .occ 206, .occ 214, .occ 227, .occ 235, .occ 251, .occ 254, .occ 273, .occ 282, .occ 295, .occ 308, .occ 321, .occ 326, .occ 344, .occ 345, .occ 350, .occ 367, .sumGe, .nonneg 4, .branchLe 14 (0), .branchGe 9 (1), .branchGe 12 (1), .branchGe 5 (1)]

def plane489GenLeaf0023Mult : Fin 33 → Nat := ![436, 65, 141, 18, 519, 131, 52, 11, 34, 378, 120, 10, 9, 7, 240, 213, 106, 128, 172, 10, 37, 107, 265, 104, 34, 28, 9, 519, 34, 65, 1561, 1524, 940]

theorem plane489GenLeaf0023 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0023Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0023Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0023Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0023Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 95
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 176
  · exact hroot.hOcc 188
  · exact hroot.hOcc 202
  · exact hroot.hOcc 203
  · exact hroot.hOcc 206
  · exact hroot.hOcc 214
  · exact hroot.hOcc 227
  · exact hroot.hOcc 235
  · exact hroot.hOcc 251
  · exact hroot.hOcc 254
  · exact hroot.hOcc 273
  · exact hroot.hOcc 282
  · exact hroot.hOcc 295
  · exact hroot.hOcc 308
  · exact hroot.hOcc 321
  · exact hroot.hOcc 326
  · exact hroot.hOcc 344
  · exact hroot.hOcc 345
  · exact hroot.hOcc 350
  · exact hroot.hOcc 367
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 32) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (14 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (9 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (12 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (5 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
