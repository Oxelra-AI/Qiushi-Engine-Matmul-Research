import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0002Refs : Fin 33 → RowRef 371 32 := ![.occ 105, .occ 125, .occ 126, .occ 129, .occ 140, .occ 148, .occ 161, .occ 164, .occ 171, .occ 187, .occ 194, .occ 197, .occ 201, .occ 202, .occ 252, .occ 272, .occ 284, .occ 285, .occ 288, .occ 304, .occ 306, .occ 309, .occ 348, .occ 350, .occ 368, .sumGe, .branchLe 14 (0), .branchLe 9 (0), .branchLe 31 (0), .branchLe 25 (0), .branchGe 10 (1), .branchLe 18 (0), .branchGe 16 (1)]

def plane489GenLeaf0002Mult : Fin 33 → Nat := ![4945, 4788, 7104, 1826, 7759, 7453, 5158, 4969, 4306, 3399, 2685, 2048, 3116, 428, 1527, 2441, 2316, 2490, 1656, 2397, 2832, 1232, 5875, 5801, 657, 18134, 12621, 18134, 11602, 14505, 16700, 10285, 27125]

theorem plane489GenLeaf0002 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0002Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0002Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 105
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 129
  · exact hroot.hOcc 140
  · exact hroot.hOcc 148
  · exact hroot.hOcc 161
  · exact hroot.hOcc 164
  · exact hroot.hOcc 171
  · exact hroot.hOcc 187
  · exact hroot.hOcc 194
  · exact hroot.hOcc 197
  · exact hroot.hOcc 201
  · exact hroot.hOcc 202
  · exact hroot.hOcc 252
  · exact hroot.hOcc 272
  · exact hroot.hOcc 284
  · exact hroot.hOcc 285
  · exact hroot.hOcc 288
  · exact hroot.hOcc 304
  · exact hroot.hOcc 306
  · exact hroot.hOcc 309
  · exact hroot.hOcc 348
  · exact hroot.hOcc 350
  · exact hroot.hOcc 368
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (9 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (31 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (25 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (10 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (18 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (16 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16

end QiushiMatmul
