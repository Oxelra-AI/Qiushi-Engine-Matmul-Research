import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0143Refs : Fin 44 → RowRef 1665 43 := ![.occ 122, .occ 129, .occ 130, .occ 132, .occ 309, .occ 316, .occ 329, .occ 358, .occ 462, .occ 601, .occ 737, .occ 818, .occ 930, .occ 997, .occ 1140, .occ 1215, .occ 1228, .occ 1245, .occ 1248, .occ 1255, .occ 1306, .occ 1332, .occ 1337, .occ 1353, .occ 1525, .occ 1538, .occ 1580, .occ 1601, .occ 1619, .occ 1625, .occ 1646, .occ 1656, .sumGe, .nonneg 1, .nonneg 8, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 39 (1), .branchLe 16 (0), .branchLe 27 (0), .branchGe 13 (1)]

def plane484GenLeaf0143Mult : Fin 44 → Nat := ![4678, 17918, 10390, 1580, 1332, 6616, 9356, 482, 1302, 7202, 48720, 4132, 14934, 14722, 19367, 21615, 11106, 1580, 12831, 2915, 10775, 10256, 7717, 4201, 6258, 9738, 6258, 9716, 1100, 13531, 4336, 1362, 58436, 4200, 1302, 43644, 54100, 177440, 58436, 40518, 106698, 24738, 58436, 120654]

theorem plane484GenLeaf0143 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0143Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0143Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0143Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0143Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 132
  · exact hroot.hOcc 309
  · exact hroot.hOcc 316
  · exact hroot.hOcc 329
  · exact hroot.hOcc 358
  · exact hroot.hOcc 462
  · exact hroot.hOcc 601
  · exact hroot.hOcc 737
  · exact hroot.hOcc 818
  · exact hroot.hOcc 930
  · exact hroot.hOcc 997
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1228
  · exact hroot.hOcc 1245
  · exact hroot.hOcc 1248
  · exact hroot.hOcc 1255
  · exact hroot.hOcc 1306
  · exact hroot.hOcc 1332
  · exact hroot.hOcc 1337
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1525
  · exact hroot.hOcc 1538
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1619
  · exact hroot.hOcc 1625
  · exact hroot.hOcc 1646
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
