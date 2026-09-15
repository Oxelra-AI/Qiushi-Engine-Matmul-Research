import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0014Refs : Fin 32 → RowRef 371 32 := ![.occ 96, .occ 98, .occ 99, .occ 102, .occ 116, .occ 124, .occ 145, .occ 151, .occ 169, .occ 194, .occ 202, .occ 216, .occ 230, .occ 232, .occ 237, .occ 286, .occ 312, .occ 317, .occ 322, .occ 324, .occ 337, .occ 344, .occ 345, .occ 366, .occ 368, .sumGe, .branchLe 14 (0), .branchLe 9 (0), .branchGe 31 (1), .branchGe 23 (1), .branchGe 7 (1), .branchGe 24 (1)]

def plane489GenLeaf0014Mult : Fin 32 → Nat := ![50, 21, 14, 67, 30, 39, 17, 36, 53, 30, 14, 11, 49, 98, 72, 11, 42, 52, 8, 7, 58, 57, 19, 30, 27, 151, 121, 151, 326, 158, 339, 386]

theorem plane489GenLeaf0014 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0014Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0014Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0014Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0014Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 96
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 102
  · exact hroot.hOcc 116
  · exact hroot.hOcc 124
  · exact hroot.hOcc 145
  · exact hroot.hOcc 151
  · exact hroot.hOcc 169
  · exact hroot.hOcc 194
  · exact hroot.hOcc 202
  · exact hroot.hOcc 216
  · exact hroot.hOcc 230
  · exact hroot.hOcc 232
  · exact hroot.hOcc 237
  · exact hroot.hOcc 286
  · exact hroot.hOcc 312
  · exact hroot.hOcc 317
  · exact hroot.hOcc 322
  · exact hroot.hOcc 324
  · exact hroot.hOcc 337
  · exact hroot.hOcc 344
  · exact hroot.hOcc 345
  · exact hroot.hOcc 366
  · exact hroot.hOcc 368
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (9 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (31 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (23 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (7 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (24 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24

end QiushiMatmul
