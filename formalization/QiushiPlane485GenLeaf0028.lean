import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0028Refs : Fin 42 → RowRef 421 41 := ![.occ 135, .occ 136, .occ 142, .occ 143, .occ 146, .occ 151, .occ 152, .occ 171, .occ 177, .occ 213, .occ 218, .occ 224, .occ 225, .occ 239, .occ 245, .occ 257, .occ 261, .occ 265, .occ 279, .occ 314, .occ 318, .occ 321, .occ 330, .occ 335, .occ 355, .occ 367, .occ 373, .occ 377, .occ 406, .occ 414, .sumGe, .nonneg 7, .branchGe 28 (1), .branchLe 19 (0), .branchLe 22 (0), .branchLe 0 (0), .branchLe 35 (0), .branchLe 6 (0), .branchLe 32 (0), .branchLe 29 (0), .branchLe 14 (0), .branchGe 11 (1)]

def plane485GenLeaf0028Mult : Fin 42 → Nat := ![429, 371, 333, 117, 222, 136, 202, 528, 34, 254, 410, 114, 160, 60, 24, 146, 144, 34, 304, 122, 30, 64, 110, 480, 32, 136, 170, 112, 110, 170, 1106, 578, 980, 738, 460, 510, 802, 306, 718, 968, 970, 1678]

theorem plane485GenLeaf0028 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0028Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0028Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0028Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0028Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 142
  · exact hroot.hOcc 143
  · exact hroot.hOcc 146
  · exact hroot.hOcc 151
  · exact hroot.hOcc 152
  · exact hroot.hOcc 171
  · exact hroot.hOcc 177
  · exact hroot.hOcc 213
  · exact hroot.hOcc 218
  · exact hroot.hOcc 224
  · exact hroot.hOcc 225
  · exact hroot.hOcc 239
  · exact hroot.hOcc 245
  · exact hroot.hOcc 257
  · exact hroot.hOcc 261
  · exact hroot.hOcc 265
  · exact hroot.hOcc 279
  · exact hroot.hOcc 314
  · exact hroot.hOcc 318
  · exact hroot.hOcc 321
  · exact hroot.hOcc 330
  · exact hroot.hOcc 335
  · exact hroot.hOcc 355
  · exact hroot.hOcc 367
  · exact hroot.hOcc 373
  · exact hroot.hOcc 377
  · exact hroot.hOcc 406
  · exact hroot.hOcc 414
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (28 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (19 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (22 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (0 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (35 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (6 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (32 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (29 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (14 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11

end QiushiMatmul
