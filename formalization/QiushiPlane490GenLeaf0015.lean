import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0015Refs : Fin 42 → RowRef 713 43 := ![.occ 84, .occ 85, .occ 86, .occ 94, .occ 95, .occ 99, .occ 102, .occ 104, .occ 106, .occ 109, .occ 110, .occ 125, .occ 127, .occ 155, .occ 166, .occ 183, .occ 196, .occ 201, .occ 202, .occ 309, .occ 314, .occ 343, .occ 354, .occ 371, .occ 396, .occ 397, .occ 494, .occ 501, .occ 531, .occ 552, .occ 596, .occ 605, .occ 665, .occ 692, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchLe 23 (0), .branchGe 16 (1), .branchLe 15 (0), .branchLe 21 (0), .branchLe 32 (0)]

def plane490GenLeaf0015Mult : Fin 42 → Nat := ![21, 30, 75, 75, 105, 3, 12, 22, 2, 26, 10, 15, 33, 15, 1, 54, 12, 33, 3, 51, 6, 23, 30, 15, 9, 6, 3, 54, 6, 24, 9, 15, 27, 45, 111, 57, 96, 111, 423, 111, 111, 81]

theorem plane490GenLeaf0015 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0015Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0015Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0015Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0015Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 99
  · exact hroot.hOcc 102
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 155
  · exact hroot.hOcc 166
  · exact hroot.hOcc 183
  · exact hroot.hOcc 196
  · exact hroot.hOcc 201
  · exact hroot.hOcc 202
  · exact hroot.hOcc 309
  · exact hroot.hOcc 314
  · exact hroot.hOcc 343
  · exact hroot.hOcc 354
  · exact hroot.hOcc 371
  · exact hroot.hOcc 396
  · exact hroot.hOcc 397
  · exact hroot.hOcc 494
  · exact hroot.hOcc 501
  · exact hroot.hOcc 531
  · exact hroot.hOcc 552
  · exact hroot.hOcc 596
  · exact hroot.hOcc 605
  · exact hroot.hOcc 665
  · exact hroot.hOcc 692
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32

end QiushiMatmul
