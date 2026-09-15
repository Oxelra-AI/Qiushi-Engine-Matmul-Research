import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0012Refs : Fin 28 → RowRef 371 32 := ![.occ 97, .occ 100, .occ 104, .occ 117, .occ 118, .occ 119, .occ 147, .occ 153, .occ 154, .occ 201, .occ 207, .occ 219, .occ 231, .occ 322, .occ 328, .occ 339, .occ 341, .occ 345, .occ 350, .occ 352, .occ 368, .occ 370, .sumGe, .branchLe 9 (0), .branchGe 31 (1), .branchGe 23 (1), .branchLe 7 (0), .branchGe 27 (1)]

def plane489GenLeaf0012Mult : Fin 28 → Nat := ![7, 8, 10, 22, 3, 8, 14, 4, 3, 13, 24, 4, 3, 3, 3, 8, 7, 3, 15, 12, 12, 7, 37, 25, 46, 78, 25, 71]

theorem plane489GenLeaf0012 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0012Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0012Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0012Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0012Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 97
  · exact hroot.hOcc 100
  · exact hroot.hOcc 104
  · exact hroot.hOcc 117
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 147
  · exact hroot.hOcc 153
  · exact hroot.hOcc 154
  · exact hroot.hOcc 201
  · exact hroot.hOcc 207
  · exact hroot.hOcc 219
  · exact hroot.hOcc 231
  · exact hroot.hOcc 322
  · exact hroot.hOcc 328
  · exact hroot.hOcc 339
  · exact hroot.hOcc 341
  · exact hroot.hOcc 345
  · exact hroot.hOcc 350
  · exact hroot.hOcc 352
  · exact hroot.hOcc 368
  · exact hroot.hOcc 370
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (9 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (31 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (23 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (7 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (27 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27

end QiushiMatmul
