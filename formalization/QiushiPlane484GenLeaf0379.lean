import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0379Refs : Fin 40 → RowRef 1665 43 := ![.occ 121, .occ 125, .occ 133, .occ 134, .occ 179, .occ 221, .occ 301, .occ 305, .occ 325, .occ 349, .occ 386, .occ 472, .occ 615, .occ 690, .occ 859, .occ 1164, .occ 1168, .occ 1214, .occ 1319, .occ 1320, .occ 1357, .occ 1505, .occ 1506, .occ 1515, .occ 1559, .occ 1571, .occ 1597, .occ 1606, .sumGe, .nonneg 8, .nonneg 16, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchGe 35 (1), .branchLe 30 (0), .branchLe 42 (0), .branchGe 27 (1), .branchGe 9 (1)]

def plane484GenLeaf0379Mult : Fin 40 → Nat := ![6, 98, 7, 69, 16, 8, 14, 74, 1, 6, 45, 2, 4, 30, 40, 26, 30, 8, 30, 8, 8, 50, 8, 2, 22, 30, 8, 46, 114, 50, 22, 106, 100, 36, 270, 122, 106, 68, 136, 288]

theorem plane484GenLeaf0379 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0379Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0379Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0379Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0379Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 125
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 179
  · exact hroot.hOcc 221
  · exact hroot.hOcc 301
  · exact hroot.hOcc 305
  · exact hroot.hOcc 325
  · exact hroot.hOcc 349
  · exact hroot.hOcc 386
  · exact hroot.hOcc 472
  · exact hroot.hOcc 615
  · exact hroot.hOcc 690
  · exact hroot.hOcc 859
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1319
  · exact hroot.hOcc 1320
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1505
  · exact hroot.hOcc 1506
  · exact hroot.hOcc 1515
  · exact hroot.hOcc 1559
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1606
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
