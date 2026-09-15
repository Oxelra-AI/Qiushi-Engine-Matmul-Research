import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0026Refs : Fin 44 → RowRef 713 43 := ![.occ 94, .occ 95, .occ 102, .occ 103, .occ 104, .occ 106, .occ 110, .occ 127, .occ 146, .occ 149, .occ 150, .occ 155, .occ 157, .occ 214, .occ 239, .occ 252, .occ 303, .occ 309, .occ 316, .occ 366, .occ 372, .occ 374, .occ 455, .occ 456, .occ 475, .occ 479, .occ 484, .occ 494, .occ 500, .occ 518, .occ 534, .occ 649, .occ 691, .occ 692, .sumGe, .nonneg 21, .nonneg 38, .branchLe 29 (0), .branchLe 4 (0), .branchLe 23 (0), .branchGe 16 (1), .branchGe 15 (1), .branchGe 32 (1), .branchGe 20 (1)]

def plane490GenLeaf0026Mult : Fin 44 → Nat := ![159, 160, 34, 49, 190, 112, 142, 28, 33, 55, 11, 30, 29, 10, 12, 18, 49, 13, 114, 96, 32, 13, 30, 15, 13, 65, 14, 16, 81, 17, 29, 62, 1, 66, 190, 30, 8, 160, 105, 189, 447, 200, 416, 567]

theorem plane490GenLeaf0026 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0026Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0026Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0026Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0026Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 110
  · exact hroot.hOcc 127
  · exact hroot.hOcc 146
  · exact hroot.hOcc 149
  · exact hroot.hOcc 150
  · exact hroot.hOcc 155
  · exact hroot.hOcc 157
  · exact hroot.hOcc 214
  · exact hroot.hOcc 239
  · exact hroot.hOcc 252
  · exact hroot.hOcc 303
  · exact hroot.hOcc 309
  · exact hroot.hOcc 316
  · exact hroot.hOcc 366
  · exact hroot.hOcc 372
  · exact hroot.hOcc 374
  · exact hroot.hOcc 455
  · exact hroot.hOcc 456
  · exact hroot.hOcc 475
  · exact hroot.hOcc 479
  · exact hroot.hOcc 484
  · exact hroot.hOcc 494
  · exact hroot.hOcc 500
  · exact hroot.hOcc 518
  · exact hroot.hOcc 534
  · exact hroot.hOcc 649
  · exact hroot.hOcc 691
  · exact hroot.hOcc 692
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
