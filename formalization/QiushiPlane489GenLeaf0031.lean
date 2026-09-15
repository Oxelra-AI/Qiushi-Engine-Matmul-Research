import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0031Refs : Fin 32 → RowRef 371 32 := ![.occ 96, .occ 98, .occ 103, .occ 133, .occ 139, .occ 140, .occ 142, .occ 144, .occ 147, .occ 149, .occ 160, .occ 178, .occ 184, .occ 187, .occ 198, .occ 202, .occ 235, .occ 264, .occ 275, .occ 277, .occ 283, .occ 305, .occ 307, .occ 344, .occ 348, .sumGe, .branchGe 14 (1), .branchLe 26 (0), .branchGe 7 (1), .branchLe 18 (0), .branchLe 31 (0), .branchGe 22 (1)]

def plane489GenLeaf0031Mult : Fin 32 → Nat := ![26, 150, 92, 68, 22, 40, 17, 16, 72, 225, 74, 74, 14, 208, 150, 42, 117, 91, 26, 98, 88, 153, 98, 1, 36, 339, 333, 241, 360, 160, 302, 1105]

theorem plane489GenLeaf0031 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0031Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0031Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0031Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0031Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 96
  · exact hroot.hOcc 98
  · exact hroot.hOcc 103
  · exact hroot.hOcc 133
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 144
  · exact hroot.hOcc 147
  · exact hroot.hOcc 149
  · exact hroot.hOcc 160
  · exact hroot.hOcc 178
  · exact hroot.hOcc 184
  · exact hroot.hOcc 187
  · exact hroot.hOcc 198
  · exact hroot.hOcc 202
  · exact hroot.hOcc 235
  · exact hroot.hOcc 264
  · exact hroot.hOcc 275
  · exact hroot.hOcc 277
  · exact hroot.hOcc 283
  · exact hroot.hOcc 305
  · exact hroot.hOcc 307
  · exact hroot.hOcc 344
  · exact hroot.hOcc 348
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (26 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (7 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (31 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (22 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
