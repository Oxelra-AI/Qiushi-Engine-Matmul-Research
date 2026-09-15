import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0058Refs : Fin 50 → RowRef 726 49 := ![.occ 88, .occ 100, .occ 104, .occ 105, .occ 106, .occ 116, .occ 152, .occ 159, .occ 161, .occ 164, .occ 195, .occ 232, .occ 241, .occ 267, .occ 299, .occ 305, .occ 328, .occ 338, .occ 366, .occ 368, .occ 370, .occ 396, .occ 402, .occ 413, .occ 416, .occ 485, .occ 506, .occ 524, .occ 526, .occ 529, .occ 547, .occ 585, .occ 590, .occ 594, .occ 629, .occ 634, .occ 643, .occ 644, .occ 692, .occ 715, .occ 716, .occ 722, .sumGe, .nonneg 2, .nonneg 45, .branchLe 31 (0), .branchLe 16 (0), .branchGe 27 (1), .branchLe 11 (0), .branchGe 23 (1)]

def plane491GenLeaf0058Mult : Fin 50 → Nat := ![99, 300, 695, 340, 376, 12, 94, 131, 5704, 2357, 6277, 176, 665, 8159, 363, 148, 7775, 4691, 11045, 5079, 241, 11654, 24, 249, 6562, 4161, 6824, 6511, 135, 869, 2102, 120, 62, 262, 113, 311, 14, 176, 4380, 1102, 7287, 379, 16789, 621, 7416, 7021, 483, 65776, 7533, 73237]

theorem plane491GenLeaf0058 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0058Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0058Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0058Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0058Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 88
  · exact hroot.hOcc 100
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 116
  · exact hroot.hOcc 152
  · exact hroot.hOcc 159
  · exact hroot.hOcc 161
  · exact hroot.hOcc 164
  · exact hroot.hOcc 195
  · exact hroot.hOcc 232
  · exact hroot.hOcc 241
  · exact hroot.hOcc 267
  · exact hroot.hOcc 299
  · exact hroot.hOcc 305
  · exact hroot.hOcc 328
  · exact hroot.hOcc 338
  · exact hroot.hOcc 366
  · exact hroot.hOcc 368
  · exact hroot.hOcc 370
  · exact hroot.hOcc 396
  · exact hroot.hOcc 402
  · exact hroot.hOcc 413
  · exact hroot.hOcc 416
  · exact hroot.hOcc 485
  · exact hroot.hOcc 506
  · exact hroot.hOcc 524
  · exact hroot.hOcc 526
  · exact hroot.hOcc 529
  · exact hroot.hOcc 547
  · exact hroot.hOcc 585
  · exact hroot.hOcc 590
  · exact hroot.hOcc 594
  · exact hroot.hOcc 629
  · exact hroot.hOcc 634
  · exact hroot.hOcc 643
  · exact hroot.hOcc 644
  · exact hroot.hOcc 692
  · exact hroot.hOcc 715
  · exact hroot.hOcc 716
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (45 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (23 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23

end QiushiMatmul
