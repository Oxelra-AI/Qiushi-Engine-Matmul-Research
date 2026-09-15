import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0015Refs : Fin 32 → RowRef 371 32 := ![.occ 96, .occ 97, .occ 105, .occ 130, .occ 137, .occ 139, .occ 145, .occ 151, .occ 156, .occ 165, .occ 181, .occ 213, .occ 224, .occ 261, .occ 273, .occ 282, .occ 303, .occ 321, .occ 341, .occ 342, .occ 346, .occ 349, .occ 359, .occ 362, .occ 364, .sumGe, .branchLe 14 (0), .branchGe 9 (1), .branchLe 12 (0), .branchLe 17 (0), .branchLe 22 (0), .branchLe 28 (0)]

def plane489GenLeaf0015Mult : Fin 32 → Nat := ![280, 1161, 903, 1019, 995, 264, 356, 83, 15, 38, 503, 83, 548, 312, 174, 297, 503, 416, 217, 80, 104, 217, 596, 78, 124, 1832, 1198, 3258, 1416, 1520, 1236, 1532]

theorem plane489GenLeaf0015 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0015Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0015Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0015Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0015Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 96
  · exact hroot.hOcc 97
  · exact hroot.hOcc 105
  · exact hroot.hOcc 130
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 145
  · exact hroot.hOcc 151
  · exact hroot.hOcc 156
  · exact hroot.hOcc 165
  · exact hroot.hOcc 181
  · exact hroot.hOcc 213
  · exact hroot.hOcc 224
  · exact hroot.hOcc 261
  · exact hroot.hOcc 273
  · exact hroot.hOcc 282
  · exact hroot.hOcc 303
  · exact hroot.hOcc 321
  · exact hroot.hOcc 341
  · exact hroot.hOcc 342
  · exact hroot.hOcc 346
  · exact hroot.hOcc 349
  · exact hroot.hOcc 359
  · exact hroot.hOcc 362
  · exact hroot.hOcc 364
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (9 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (12 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (17 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (22 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (28 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28

end QiushiMatmul
