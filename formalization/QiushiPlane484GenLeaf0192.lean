import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0192Refs : Fin 42 → RowRef 1665 43 := ![.occ 120, .occ 129, .occ 201, .occ 387, .occ 390, .occ 412, .occ 430, .occ 471, .occ 848, .occ 1154, .occ 1179, .occ 1220, .occ 1253, .occ 1254, .occ 1265, .occ 1348, .occ 1357, .occ 1374, .occ 1381, .occ 1384, .occ 1385, .occ 1439, .occ 1450, .occ 1492, .occ 1529, .occ 1536, .occ 1547, .occ 1573, .occ 1629, .sumGe, .nonneg 17, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchLe 1 (0), .branchGe 5 (1), .branchLe 22 (0), .branchGe 30 (1), .branchGe 40 (1)]

def plane484GenLeaf0192Mult : Fin 42 → Nat := ![38, 65, 85, 26, 209, 132, 172, 55, 22, 30, 33, 53, 7, 29, 52, 66, 86, 9, 51, 41, 19, 49, 33, 7, 38, 45, 85, 39, 33, 242, 5, 44, 196, 645, 672, 176, 163, 146, 391, 212, 516, 946]

theorem plane484GenLeaf0192 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0192Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0192Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0192Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0192Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 129
  · exact hroot.hOcc 201
  · exact hroot.hOcc 387
  · exact hroot.hOcc 390
  · exact hroot.hOcc 412
  · exact hroot.hOcc 430
  · exact hroot.hOcc 471
  · exact hroot.hOcc 848
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1253
  · exact hroot.hOcc 1254
  · exact hroot.hOcc 1265
  · exact hroot.hOcc 1348
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1374
  · exact hroot.hOcc 1381
  · exact hroot.hOcc 1384
  · exact hroot.hOcc 1385
  · exact hroot.hOcc 1439
  · exact hroot.hOcc 1450
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1529
  · exact hroot.hOcc 1536
  · exact hroot.hOcc 1547
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1629
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (40 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40

end QiushiMatmul
