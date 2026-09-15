import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0460Refs : Fin 38 → RowRef 1665 43 := ![.occ 134, .occ 142, .occ 191, .occ 192, .occ 206, .occ 330, .occ 385, .occ 395, .occ 419, .occ 525, .occ 674, .occ 862, .occ 873, .occ 1070, .occ 1159, .occ 1188, .occ 1191, .occ 1200, .occ 1268, .occ 1380, .occ 1419, .occ 1467, .occ 1567, .occ 1615, .occ 1645, .occ 1646, .occ 1659, .sumGe, .nonneg 0, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 29 (1), .branchGe 27 (1), .branchLe 8 (0), .branchLe 4 (0), .branchGe 16 (1), .branchLe 10 (0)]

def plane484GenLeaf0460Mult : Fin 38 → Nat := ![81, 98, 104, 25, 41, 140, 131, 36, 143, 156, 91, 59, 72, 11, 32, 31, 52, 18, 30, 9, 50, 69, 160, 111, 10, 10, 42, 281, 142, 677, 249, 131, 595, 355, 261, 170, 955, 239]

theorem plane484GenLeaf0460 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0460Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0460Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0460Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0460Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 134
  · exact hroot.hOcc 142
  · exact hroot.hOcc 191
  · exact hroot.hOcc 192
  · exact hroot.hOcc 206
  · exact hroot.hOcc 330
  · exact hroot.hOcc 385
  · exact hroot.hOcc 395
  · exact hroot.hOcc 419
  · exact hroot.hOcc 525
  · exact hroot.hOcc 674
  · exact hroot.hOcc 862
  · exact hroot.hOcc 873
  · exact hroot.hOcc 1070
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1268
  · exact hroot.hOcc 1380
  · exact hroot.hOcc 1419
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1645
  · exact hroot.hOcc 1646
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
