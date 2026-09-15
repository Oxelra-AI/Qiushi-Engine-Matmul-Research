import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0034Refs : Fin 49 → RowRef 668 48 := ![.occ 82, .occ 85, .occ 89, .occ 92, .occ 93, .occ 95, .occ 103, .occ 110, .occ 111, .occ 153, .occ 176, .occ 218, .occ 219, .occ 231, .occ 269, .occ 294, .occ 296, .occ 297, .occ 303, .occ 312, .occ 315, .occ 316, .occ 333, .occ 356, .occ 361, .occ 378, .occ 379, .occ 386, .occ 394, .occ 399, .occ 415, .occ 439, .occ 472, .occ 539, .occ 540, .occ 563, .occ 590, .occ 593, .occ 599, .occ 608, .occ 665, .sumGe, .nonneg 0, .nonneg 29, .branchLe 39 (0), .branchGe 6 (1), .branchGe 33 (1), .branchLe 12 (0), .branchGe 42 (1)]

def plane487GenLeaf0034Mult : Fin 49 → Nat := ![28006, 1899, 708, 10602, 8013, 14931, 8361, 26593, 30163, 8305, 1434, 5727, 14723, 9271, 25343, 24860, 6304, 10909, 16906, 6773, 26063, 3184, 7542, 741, 5367, 266, 18606, 17152, 1229, 29463, 5792, 4235, 17626, 1484, 2323, 237, 708, 10187, 7296, 10942, 246, 54157, 19976, 13040, 36048, 95863, 49434, 47384, 150700]

theorem plane487GenLeaf0034 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0034Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0034Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0034Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0034Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 85
  · exact hroot.hOcc 89
  · exact hroot.hOcc 92
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 103
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 153
  · exact hroot.hOcc 176
  · exact hroot.hOcc 218
  · exact hroot.hOcc 219
  · exact hroot.hOcc 231
  · exact hroot.hOcc 269
  · exact hroot.hOcc 294
  · exact hroot.hOcc 296
  · exact hroot.hOcc 297
  · exact hroot.hOcc 303
  · exact hroot.hOcc 312
  · exact hroot.hOcc 315
  · exact hroot.hOcc 316
  · exact hroot.hOcc 333
  · exact hroot.hOcc 356
  · exact hroot.hOcc 361
  · exact hroot.hOcc 378
  · exact hroot.hOcc 379
  · exact hroot.hOcc 386
  · exact hroot.hOcc 394
  · exact hroot.hOcc 399
  · exact hroot.hOcc 415
  · exact hroot.hOcc 439
  · exact hroot.hOcc 472
  · exact hroot.hOcc 539
  · exact hroot.hOcc 540
  · exact hroot.hOcc 563
  · exact hroot.hOcc 590
  · exact hroot.hOcc 593
  · exact hroot.hOcc 599
  · exact hroot.hOcc 608
  · exact hroot.hOcc 665
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (29 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (6 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (33 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33
  · change (∑ k, (if k = (12 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (42 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42

end QiushiMatmul
