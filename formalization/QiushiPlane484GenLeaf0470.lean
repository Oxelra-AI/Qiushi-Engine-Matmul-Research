import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0470Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 122, .occ 123, .occ 124, .occ 131, .occ 132, .occ 133, .occ 135, .occ 142, .occ 186, .occ 420, .occ 581, .occ 762, .occ 1109, .occ 1113, .occ 1136, .occ 1159, .occ 1174, .occ 1200, .occ 1336, .occ 1385, .occ 1454, .occ 1483, .occ 1580, .occ 1601, .occ 1602, .occ 1603, .occ 1608, .occ 1615, .occ 1629, .occ 1646, .sumGe, .nonneg 19, .nonneg 20, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 0 (1), .branchLe 25 (0), .branchLe 3 (0), .branchLe 38 (0), .branchLe 27 (0), .branchGe 34 (1), .branchLe 41 (0)]

def plane484GenLeaf0470Mult : Fin 44 → Nat := ![26425, 14736, 1031, 11034, 34455, 3476, 51865, 7364, 35035, 54078, 2124, 48553, 21634, 29153, 19243, 21622, 41846, 8186, 28736, 7934, 14934, 23734, 14654, 2176, 21420, 9854, 4908, 6208, 8170, 2176, 35720, 127692, 27798, 17688, 297386, 71192, 102264, 104970, 10110, 39730, 113038, 90786, 175958, 127692]

theorem plane484GenLeaf0470 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0470Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0470Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0470Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0470Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 142
  · exact hroot.hOcc 186
  · exact hroot.hOcc 420
  · exact hroot.hOcc 581
  · exact hroot.hOcc 762
  · exact hroot.hOcc 1109
  · exact hroot.hOcc 1113
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1336
  · exact hroot.hOcc 1385
  · exact hroot.hOcc 1454
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1646
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (27 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (41 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41

end QiushiMatmul
