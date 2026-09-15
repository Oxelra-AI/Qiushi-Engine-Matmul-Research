import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0013Refs : Fin 31 → RowRef 371 32 := ![.occ 97, .occ 100, .occ 112, .occ 116, .occ 117, .occ 124, .occ 131, .occ 147, .occ 149, .occ 188, .occ 205, .occ 207, .occ 216, .occ 239, .occ 244, .occ 267, .occ 295, .occ 322, .occ 337, .occ 338, .occ 347, .occ 348, .occ 350, .occ 363, .sumGe, .branchLe 14 (0), .branchLe 9 (0), .branchGe 31 (1), .branchGe 23 (1), .branchGe 7 (1), .branchLe 24 (0)]

def plane489GenLeaf0013Mult : Fin 31 → Nat := ![24, 30, 31, 3, 40, 6, 39, 39, 30, 21, 24, 45, 10, 30, 44, 47, 35, 36, 58, 15, 7, 73, 75, 6, 178, 133, 178, 60, 346, 46, 178]

theorem plane489GenLeaf0013 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0013Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0013Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0013Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0013Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 97
  · exact hroot.hOcc 100
  · exact hroot.hOcc 112
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 124
  · exact hroot.hOcc 131
  · exact hroot.hOcc 147
  · exact hroot.hOcc 149
  · exact hroot.hOcc 188
  · exact hroot.hOcc 205
  · exact hroot.hOcc 207
  · exact hroot.hOcc 216
  · exact hroot.hOcc 239
  · exact hroot.hOcc 244
  · exact hroot.hOcc 267
  · exact hroot.hOcc 295
  · exact hroot.hOcc 322
  · exact hroot.hOcc 337
  · exact hroot.hOcc 338
  · exact hroot.hOcc 347
  · exact hroot.hOcc 348
  · exact hroot.hOcc 350
  · exact hroot.hOcc 363
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (9 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (31 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (23 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (7 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (24 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24

end QiushiMatmul
