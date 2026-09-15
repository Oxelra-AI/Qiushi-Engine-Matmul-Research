import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0023Refs : Fin 44 → RowRef 713 43 := ![.occ 85, .occ 89, .occ 94, .occ 95, .occ 110, .occ 131, .occ 198, .occ 263, .occ 266, .occ 271, .occ 277, .occ 283, .occ 295, .occ 309, .occ 333, .occ 335, .occ 348, .occ 364, .occ 373, .occ 387, .occ 391, .occ 456, .occ 457, .occ 484, .occ 486, .occ 532, .occ 540, .occ 575, .occ 599, .occ 626, .occ 631, .occ 649, .occ 665, .occ 672, .occ 692, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchLe 23 (0), .branchGe 16 (1), .branchGe 15 (1), .branchLe 32 (0), .branchGe 3 (1), .branchGe 33 (1)]

def plane490GenLeaf0023Mult : Fin 44 → Nat := ![254, 231, 141, 293, 90, 156, 117, 32, 220, 67, 165, 32, 115, 32, 215, 19, 140, 115, 64, 49, 67, 9, 41, 118, 55, 111, 92, 13, 16, 65, 213, 32, 59, 139, 18, 445, 91, 64, 377, 863, 399, 426, 1319, 1288]

theorem plane490GenLeaf0023 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0023Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0023Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0023Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0023Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 89
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 110
  · exact hroot.hOcc 131
  · exact hroot.hOcc 198
  · exact hroot.hOcc 263
  · exact hroot.hOcc 266
  · exact hroot.hOcc 271
  · exact hroot.hOcc 277
  · exact hroot.hOcc 283
  · exact hroot.hOcc 295
  · exact hroot.hOcc 309
  · exact hroot.hOcc 333
  · exact hroot.hOcc 335
  · exact hroot.hOcc 348
  · exact hroot.hOcc 364
  · exact hroot.hOcc 373
  · exact hroot.hOcc 387
  · exact hroot.hOcc 391
  · exact hroot.hOcc 456
  · exact hroot.hOcc 457
  · exact hroot.hOcc 484
  · exact hroot.hOcc 486
  · exact hroot.hOcc 532
  · exact hroot.hOcc 540
  · exact hroot.hOcc 575
  · exact hroot.hOcc 599
  · exact hroot.hOcc 626
  · exact hroot.hOcc 631
  · exact hroot.hOcc 649
  · exact hroot.hOcc 665
  · exact hroot.hOcc 672
  · exact hroot.hOcc 692
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (33 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33

end QiushiMatmul
