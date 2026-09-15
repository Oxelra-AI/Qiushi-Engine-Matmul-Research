import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0146Refs : Fin 43 → RowRef 1665 43 := ![.occ 127, .occ 128, .occ 316, .occ 334, .occ 545, .occ 575, .occ 668, .occ 670, .occ 737, .occ 757, .occ 1140, .occ 1151, .occ 1170, .occ 1172, .occ 1216, .occ 1243, .occ 1295, .occ 1296, .occ 1301, .occ 1306, .occ 1337, .occ 1353, .occ 1436, .occ 1458, .occ 1459, .occ 1524, .occ 1601, .occ 1625, .occ 1653, .occ 1655, .occ 1656, .occ 1659, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 39 (1), .branchLe 16 (0), .branchGe 27 (1), .branchLe 24 (0), .branchGe 12 (1)]

def plane484GenLeaf0146Mult : Fin 43 → Nat := ![142, 274, 282, 242, 132, 18, 116, 174, 494, 124, 9, 121, 50, 42, 121, 93, 255, 164, 185, 7, 282, 341, 46, 58, 58, 158, 46, 226, 55, 8, 151, 50, 876, 826, 876, 2158, 826, 260, 2816, 334, 398, 718, 1746]

theorem plane484GenLeaf0146 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0146Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0146Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0146Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0146Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 316
  · exact hroot.hOcc 334
  · exact hroot.hOcc 545
  · exact hroot.hOcc 575
  · exact hroot.hOcc 668
  · exact hroot.hOcc 670
  · exact hroot.hOcc 737
  · exact hroot.hOcc 757
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1243
  · exact hroot.hOcc 1295
  · exact hroot.hOcc 1296
  · exact hroot.hOcc 1301
  · exact hroot.hOcc 1306
  · exact hroot.hOcc 1337
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1436
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1524
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1625
  · exact hroot.hOcc 1653
  · exact hroot.hOcc 1655
  · exact hroot.hOcc 1656
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
