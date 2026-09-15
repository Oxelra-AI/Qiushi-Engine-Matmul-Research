import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0010Refs : Fin 41 → RowRef 421 41 := ![.occ 86, .occ 87, .occ 107, .occ 132, .occ 136, .occ 155, .occ 161, .occ 163, .occ 164, .occ 169, .occ 183, .occ 190, .occ 217, .occ 224, .occ 232, .occ 233, .occ 240, .occ 242, .occ 246, .occ 265, .occ 276, .occ 297, .occ 305, .occ 306, .occ 311, .occ 316, .occ 362, .occ 372, .occ 374, .occ 392, .occ 393, .occ 401, .sumGe, .nonneg 13, .branchLe 28 (0), .branchLe 21 (0), .branchLe 14 (0), .branchLe 11 (0), .branchGe 39 (1), .branchGe 29 (1), .branchGe 25 (1)]

def plane485GenLeaf0010Mult : Fin 41 → Nat := ![2530, 3267, 2893, 667, 237, 2179, 2952, 3240, 5580, 379, 328, 1717, 2, 3615, 505, 4259, 4204, 3772, 5560, 1440, 29, 206, 687, 129, 1025, 2063, 1556, 2564, 1296, 3619, 20, 669, 9199, 4049, 6757, 3315, 7482, 4842, 11149, 21799, 21538]

theorem plane485GenLeaf0010 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0010Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0010Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0010Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0010Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 86
  · exact hroot.hOcc 87
  · exact hroot.hOcc 107
  · exact hroot.hOcc 132
  · exact hroot.hOcc 136
  · exact hroot.hOcc 155
  · exact hroot.hOcc 161
  · exact hroot.hOcc 163
  · exact hroot.hOcc 164
  · exact hroot.hOcc 169
  · exact hroot.hOcc 183
  · exact hroot.hOcc 190
  · exact hroot.hOcc 217
  · exact hroot.hOcc 224
  · exact hroot.hOcc 232
  · exact hroot.hOcc 233
  · exact hroot.hOcc 240
  · exact hroot.hOcc 242
  · exact hroot.hOcc 246
  · exact hroot.hOcc 265
  · exact hroot.hOcc 276
  · exact hroot.hOcc 297
  · exact hroot.hOcc 305
  · exact hroot.hOcc 306
  · exact hroot.hOcc 311
  · exact hroot.hOcc 316
  · exact hroot.hOcc 362
  · exact hroot.hOcc 372
  · exact hroot.hOcc 374
  · exact hroot.hOcc 392
  · exact hroot.hOcc 393
  · exact hroot.hOcc 401
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (14 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (39 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (29 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (25 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25

end QiushiMatmul
