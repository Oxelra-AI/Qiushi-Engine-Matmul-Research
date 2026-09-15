import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0042Refs : Fin 49 → RowRef 726 49 := ![.occ 78, .occ 79, .occ 80, .occ 81, .occ 109, .occ 116, .occ 166, .occ 197, .occ 219, .occ 221, .occ 223, .occ 232, .occ 233, .occ 234, .occ 246, .occ 260, .occ 292, .occ 304, .occ 317, .occ 318, .occ 341, .occ 366, .occ 405, .occ 422, .occ 427, .occ 430, .occ 456, .occ 504, .occ 530, .occ 531, .occ 532, .occ 552, .occ 554, .occ 628, .occ 634, .occ 686, .occ 700, .occ 702, .occ 722, .sumGe, .nonneg 14, .nonneg 16, .nonneg 34, .branchLe 31 (0), .branchLe 27 (0), .branchGe 29 (1), .branchLe 43 (0), .branchGe 9 (1), .branchGe 0 (1)]

def plane491GenLeaf0042Mult : Fin 49 → Nat := ![29, 17, 50, 35, 15, 186, 95, 38, 11, 230, 241, 92, 42, 75, 91, 153, 18, 46, 19, 11, 157, 67, 20, 4, 48, 37, 70, 10, 85, 12, 25, 151, 153, 4, 31, 31, 52, 132, 81, 393, 210, 3, 377, 225, 122, 397, 147, 1370, 1636]

theorem plane491GenLeaf0042 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0042Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0042Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0042Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0042Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 109
  · exact hroot.hOcc 116
  · exact hroot.hOcc 166
  · exact hroot.hOcc 197
  · exact hroot.hOcc 219
  · exact hroot.hOcc 221
  · exact hroot.hOcc 223
  · exact hroot.hOcc 232
  · exact hroot.hOcc 233
  · exact hroot.hOcc 234
  · exact hroot.hOcc 246
  · exact hroot.hOcc 260
  · exact hroot.hOcc 292
  · exact hroot.hOcc 304
  · exact hroot.hOcc 317
  · exact hroot.hOcc 318
  · exact hroot.hOcc 341
  · exact hroot.hOcc 366
  · exact hroot.hOcc 405
  · exact hroot.hOcc 422
  · exact hroot.hOcc 427
  · exact hroot.hOcc 430
  · exact hroot.hOcc 456
  · exact hroot.hOcc 504
  · exact hroot.hOcc 530
  · exact hroot.hOcc 531
  · exact hroot.hOcc 532
  · exact hroot.hOcc 552
  · exact hroot.hOcc 554
  · exact hroot.hOcc 628
  · exact hroot.hOcc 634
  · exact hroot.hOcc 686
  · exact hroot.hOcc 700
  · exact hroot.hOcc 702
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (16 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (34 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (9 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (0 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
