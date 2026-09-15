import QiushiPlane471GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane471GenLeaf0018Refs : Fin 33 → RowRef 304 63 := ![.occ 22, .occ 23, .occ 24, .occ 25, .occ 43, .occ 75, .occ 99, .occ 100, .occ 101, .occ 105, .occ 108, .occ 109, .occ 113, .occ 125, .occ 170, .occ 172, .occ 189, .occ 209, .occ 216, .occ 218, .occ 219, .occ 230, .occ 248, .occ 251, .occ 255, .occ 277, .occ 289, .occ 292, .occ 293, .sumGe, .nonneg 8, .nonneg 55, .branchGe 48 (1)]

def plane471GenLeaf0018Mult : Fin 33 → Nat := ![5, 7, 4, 4, 18, 16, 13, 11, 10, 6, 15, 16, 7, 4, 1, 5, 5, 3, 2, 4, 2, 1, 9, 1, 4, 1, 1, 8, 2, 19, 30, 30, 166]

theorem plane471GenLeaf0018 (x : Fin 63 → Int)
    (hroot : plane471GenOccSys.RootHolds x)
    (hLB_48 : (1 : Int) ≤ x 48)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane471GenLeaf0018Refs i).resolveCoeff plane471GenOccSys j)
    (fun i => (plane471GenLeaf0018Refs i).resolveRhs plane471GenOccSys) plane471GenLeaf0018Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane471GenLeaf0018Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 43
  · exact hroot.hOcc 75
  · exact hroot.hOcc 99
  · exact hroot.hOcc 100
  · exact hroot.hOcc 101
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 113
  · exact hroot.hOcc 125
  · exact hroot.hOcc 170
  · exact hroot.hOcc 172
  · exact hroot.hOcc 189
  · exact hroot.hOcc 209
  · exact hroot.hOcc 216
  · exact hroot.hOcc 218
  · exact hroot.hOcc 219
  · exact hroot.hOcc 230
  · exact hroot.hOcc 248
  · exact hroot.hOcc 251
  · exact hroot.hOcc 255
  · exact hroot.hOcc 277
  · exact hroot.hOcc 289
  · exact hroot.hOcc 292
  · exact hroot.hOcc 293
  · change (∑ j, (-1 : Int) * x j) ≤ -plane471GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (48 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_48

end QiushiMatmul
