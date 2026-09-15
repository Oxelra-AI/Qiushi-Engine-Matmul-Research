import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0088Refs : Fin 31 → RowRef 668 48 := ![.occ 81, .occ 85, .occ 88, .occ 89, .occ 91, .occ 101, .occ 105, .occ 112, .occ 114, .occ 116, .occ 120, .occ 182, .occ 187, .occ 226, .occ 238, .occ 242, .occ 246, .occ 251, .occ 303, .occ 305, .occ 315, .occ 316, .occ 350, .occ 351, .occ 384, .occ 649, .occ 657, .sumGe, .nonneg 30, .branchGe 39 (1), .branchGe 7 (1)]

def plane487GenLeaf0088Mult : Fin 31 → Nat := ![4, 2, 4, 2, 4, 2, 2, 1, 5, 5, 1, 5, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 5, 2, 8, 45]

theorem plane487GenLeaf0088 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_39 : (1 : Int) ≤ x 39)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0088Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0088Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0088Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0088Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 81
  · exact hroot.hOcc 85
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 91
  · exact hroot.hOcc 101
  · exact hroot.hOcc 105
  · exact hroot.hOcc 112
  · exact hroot.hOcc 114
  · exact hroot.hOcc 116
  · exact hroot.hOcc 120
  · exact hroot.hOcc 182
  · exact hroot.hOcc 187
  · exact hroot.hOcc 226
  · exact hroot.hOcc 238
  · exact hroot.hOcc 242
  · exact hroot.hOcc 246
  · exact hroot.hOcc 251
  · exact hroot.hOcc 303
  · exact hroot.hOcc 305
  · exact hroot.hOcc 315
  · exact hroot.hOcc 316
  · exact hroot.hOcc 350
  · exact hroot.hOcc 351
  · exact hroot.hOcc 384
  · exact hroot.hOcc 649
  · exact hroot.hOcc 657
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (30 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7

end QiushiMatmul
