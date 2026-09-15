import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0129Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 122, .occ 139, .occ 348, .occ 703, .occ 708, .occ 716, .occ 723, .occ 796, .occ 983, .occ 1070, .occ 1154, .occ 1215, .occ 1251, .occ 1325, .occ 1380, .occ 1382, .occ 1405, .occ 1428, .occ 1452, .occ 1455, .occ 1471, .occ 1491, .occ 1601, .occ 1603, .occ 1608, .occ 1610, .occ 1622, .occ 1630, .occ 1631, .occ 1653, .occ 1661, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 39 (0), .branchLe 32 (0), .branchGe 28 (1), .branchGe 6 (1), .branchLe 33 (0), .branchGe 42 (1)]

def plane484GenLeaf0129Mult : Fin 44 → Nat := ![67694, 54460, 65224, 52754, 3586, 116, 8910, 12866, 79718, 20126, 26836, 53598, 2985, 10769, 14904, 35066, 9558, 59192, 40284, 36219, 13208, 425, 39466, 1636, 21752, 12798, 1036, 28783, 467, 3152, 16007, 62503, 196318, 163916, 156852, 102586, 196318, 26300, 81106, 196318, 221130, 271512, 196318, 241938]

theorem plane484GenLeaf0129 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0129Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0129Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0129Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0129Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 139
  · exact hroot.hOcc 348
  · exact hroot.hOcc 703
  · exact hroot.hOcc 708
  · exact hroot.hOcc 716
  · exact hroot.hOcc 723
  · exact hroot.hOcc 796
  · exact hroot.hOcc 983
  · exact hroot.hOcc 1070
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1251
  · exact hroot.hOcc 1325
  · exact hroot.hOcc 1380
  · exact hroot.hOcc 1382
  · exact hroot.hOcc 1405
  · exact hroot.hOcc 1428
  · exact hroot.hOcc 1452
  · exact hroot.hOcc 1455
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1622
  · exact hroot.hOcc 1630
  · exact hroot.hOcc 1631
  · exact hroot.hOcc 1653
  · exact hroot.hOcc 1661
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42

end QiushiMatmul
