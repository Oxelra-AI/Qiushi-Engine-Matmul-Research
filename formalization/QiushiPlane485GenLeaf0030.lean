import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0030Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 101, .occ 102, .occ 104, .occ 106, .occ 107, .occ 115, .occ 135, .occ 145, .occ 146, .occ 151, .occ 152, .occ 159, .occ 171, .occ 172, .occ 175, .occ 190, .occ 218, .occ 224, .occ 238, .occ 245, .occ 275, .occ 299, .occ 309, .occ 313, .occ 316, .occ 348, .occ 367, .occ 375, .occ 376, .occ 407, .occ 414, .sumGe, .nonneg 7, .branchGe 28 (1), .branchLe 19 (0), .branchLe 22 (0), .branchLe 0 (0), .branchLe 35 (0), .branchLe 6 (0), .branchLe 32 (0), .branchGe 29 (1)]

def plane485GenLeaf0030Mult : Fin 42 → Nat := ![157, 163, 262, 175, 85, 226, 137, 162, 16, 58, 20, 103, 83, 10, 211, 56, 59, 91, 15, 170, 334, 317, 143, 22, 16, 46, 103, 16, 72, 175, 17, 16, 453, 56, 1515, 433, 203, 394, 250, 148, 32, 1715]

theorem plane485GenLeaf0030 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0030Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0030Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0030Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0030Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 101
  · exact hroot.hOcc 102
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 115
  · exact hroot.hOcc 135
  · exact hroot.hOcc 145
  · exact hroot.hOcc 146
  · exact hroot.hOcc 151
  · exact hroot.hOcc 152
  · exact hroot.hOcc 159
  · exact hroot.hOcc 171
  · exact hroot.hOcc 172
  · exact hroot.hOcc 175
  · exact hroot.hOcc 190
  · exact hroot.hOcc 218
  · exact hroot.hOcc 224
  · exact hroot.hOcc 238
  · exact hroot.hOcc 245
  · exact hroot.hOcc 275
  · exact hroot.hOcc 299
  · exact hroot.hOcc 309
  · exact hroot.hOcc 313
  · exact hroot.hOcc 316
  · exact hroot.hOcc 348
  · exact hroot.hOcc 367
  · exact hroot.hOcc 375
  · exact hroot.hOcc 376
  · exact hroot.hOcc 407
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
  · change (∑ k, (if k = (29 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29

end QiushiMatmul
