import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0467Refs : Fin 40 → RowRef 1665 43 := ![.occ 123, .occ 138, .occ 156, .occ 162, .occ 170, .occ 498, .occ 513, .occ 581, .occ 595, .occ 635, .occ 769, .occ 867, .occ 927, .occ 944, .occ 972, .occ 1081, .occ 1108, .occ 1176, .occ 1243, .occ 1286, .occ 1302, .occ 1306, .occ 1386, .occ 1427, .occ 1453, .occ 1470, .occ 1590, .occ 1630, .occ 1639, .occ 1646, .occ 1652, .sumGe, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 0 (0), .branchGe 29 (1), .branchGe 27 (1), .branchGe 8 (1), .branchGe 30 (1)]

def plane484GenLeaf0467Mult : Fin 40 → Nat := ![104, 46, 23, 26, 225, 182, 10, 12, 121, 7, 28, 12, 134, 42, 158, 10, 65, 29, 48, 10, 29, 29, 51, 39, 52, 114, 18, 24, 10, 83, 111, 308, 846, 308, 290, 308, 304, 240, 1410, 444]

theorem plane484GenLeaf0467 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0467Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0467Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0467Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0467Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 138
  · exact hroot.hOcc 156
  · exact hroot.hOcc 162
  · exact hroot.hOcc 170
  · exact hroot.hOcc 498
  · exact hroot.hOcc 513
  · exact hroot.hOcc 581
  · exact hroot.hOcc 595
  · exact hroot.hOcc 635
  · exact hroot.hOcc 769
  · exact hroot.hOcc 867
  · exact hroot.hOcc 927
  · exact hroot.hOcc 944
  · exact hroot.hOcc 972
  · exact hroot.hOcc 1081
  · exact hroot.hOcc 1108
  · exact hroot.hOcc 1176
  · exact hroot.hOcc 1243
  · exact hroot.hOcc 1286
  · exact hroot.hOcc 1302
  · exact hroot.hOcc 1306
  · exact hroot.hOcc 1386
  · exact hroot.hOcc 1427
  · exact hroot.hOcc 1453
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1630
  · exact hroot.hOcc 1639
  · exact hroot.hOcc 1646
  · exact hroot.hOcc 1652
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30

end QiushiMatmul
