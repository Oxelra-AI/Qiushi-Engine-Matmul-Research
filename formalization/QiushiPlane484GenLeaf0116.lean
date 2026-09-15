import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0116Refs : Fin 38 → RowRef 1665 43 := ![.occ 124, .occ 127, .occ 130, .occ 142, .occ 145, .occ 180, .occ 208, .occ 209, .occ 356, .occ 386, .occ 429, .occ 652, .occ 811, .occ 1150, .occ 1238, .occ 1239, .occ 1297, .occ 1298, .occ 1446, .occ 1449, .occ 1455, .occ 1472, .occ 1477, .occ 1537, .occ 1547, .occ 1573, .occ 1597, .sumGe, .nonneg 1, .nonneg 2, .branchLe 15 (0), .branchLe 29 (0), .branchGe 4 (1), .branchGe 36 (1), .branchGe 26 (1), .branchGe 21 (1), .branchLe 24 (0), .branchLe 18 (0)]

def plane484GenLeaf0116Mult : Fin 38 → Nat := ![52, 75, 134, 118, 98, 141, 78, 56, 179, 204, 61, 103, 3, 171, 24, 21, 22, 131, 73, 83, 28, 59, 104, 11, 7, 39, 59, 350, 118, 86, 6, 350, 1344, 358, 178, 748, 350, 350]

theorem plane484GenLeaf0116 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0116Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0116Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0116Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0116Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 124
  · exact hroot.hOcc 127
  · exact hroot.hOcc 130
  · exact hroot.hOcc 142
  · exact hroot.hOcc 145
  · exact hroot.hOcc 180
  · exact hroot.hOcc 208
  · exact hroot.hOcc 209
  · exact hroot.hOcc 356
  · exact hroot.hOcc 386
  · exact hroot.hOcc 429
  · exact hroot.hOcc 652
  · exact hroot.hOcc 811
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1238
  · exact hroot.hOcc 1239
  · exact hroot.hOcc 1297
  · exact hroot.hOcc 1298
  · exact hroot.hOcc 1446
  · exact hroot.hOcc 1449
  · exact hroot.hOcc 1455
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1537
  · exact hroot.hOcc 1547
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1597
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18

end QiushiMatmul
