import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0026Refs : Fin 32 → RowRef 371 32 := ![.occ 98, .occ 100, .occ 102, .occ 105, .occ 112, .occ 116, .occ 128, .occ 129, .occ 134, .occ 158, .occ 187, .occ 188, .occ 198, .occ 207, .occ 245, .occ 283, .occ 305, .occ 310, .occ 335, .occ 337, .occ 338, .occ 341, .occ 345, .occ 348, .occ 362, .sumGe, .nonneg 27, .branchGe 14 (1), .branchLe 26 (0), .branchLe 7 (0), .branchLe 30 (0), .branchGe 4 (1)]

def plane489GenLeaf0026Mult : Fin 32 → Nat := ![46, 91, 53, 114, 16, 42, 117, 2, 1, 116, 7, 1, 52, 75, 58, 9, 58, 16, 56, 4, 6, 2, 10, 6, 6, 132, 1, 315, 116, 74, 108, 387]

theorem plane489GenLeaf0026 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0026Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0026Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0026Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0026Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 98
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 112
  · exact hroot.hOcc 116
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 134
  · exact hroot.hOcc 158
  · exact hroot.hOcc 187
  · exact hroot.hOcc 188
  · exact hroot.hOcc 198
  · exact hroot.hOcc 207
  · exact hroot.hOcc 245
  · exact hroot.hOcc 283
  · exact hroot.hOcc 305
  · exact hroot.hOcc 310
  · exact hroot.hOcc 335
  · exact hroot.hOcc 337
  · exact hroot.hOcc 338
  · exact hroot.hOcc 341
  · exact hroot.hOcc 345
  · exact hroot.hOcc 348
  · exact hroot.hOcc 362
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (27 : Fin 32) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (14 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (26 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (7 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (30 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (4 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
