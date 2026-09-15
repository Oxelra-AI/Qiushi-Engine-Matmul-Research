import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0011Refs : Fin 32 → RowRef 371 32 := ![.occ 96, .occ 97, .occ 102, .occ 105, .occ 112, .occ 117, .occ 150, .occ 151, .occ 187, .occ 188, .occ 194, .occ 205, .occ 208, .occ 227, .occ 241, .occ 247, .occ 256, .occ 291, .occ 337, .occ 340, .occ 341, .occ 344, .occ 345, .occ 348, .occ 368, .sumGe, .branchLe 14 (0), .branchLe 9 (0), .branchGe 31 (1), .branchGe 23 (1), .branchLe 7 (0), .branchLe 27 (0)]

def plane489GenLeaf0011Mult : Fin 32 → Nat := ![244, 544, 291, 32, 193, 250, 163, 140, 247, 69, 529, 83, 83, 125, 232, 84, 84, 21, 294, 99, 156, 96, 252, 206, 31, 781, 781, 760, 603, 1268, 571, 750]

theorem plane489GenLeaf0011 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0011Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0011Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0011Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0011Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 96
  · exact hroot.hOcc 97
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 112
  · exact hroot.hOcc 117
  · exact hroot.hOcc 150
  · exact hroot.hOcc 151
  · exact hroot.hOcc 187
  · exact hroot.hOcc 188
  · exact hroot.hOcc 194
  · exact hroot.hOcc 205
  · exact hroot.hOcc 208
  · exact hroot.hOcc 227
  · exact hroot.hOcc 241
  · exact hroot.hOcc 247
  · exact hroot.hOcc 256
  · exact hroot.hOcc 291
  · exact hroot.hOcc 337
  · exact hroot.hOcc 340
  · exact hroot.hOcc 341
  · exact hroot.hOcc 344
  · exact hroot.hOcc 345
  · exact hroot.hOcc 348
  · exact hroot.hOcc 368
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (9 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (31 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (23 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (7 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (27 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27

end QiushiMatmul
