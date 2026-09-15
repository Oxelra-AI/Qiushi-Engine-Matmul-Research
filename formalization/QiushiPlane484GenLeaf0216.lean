import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0216Refs : Fin 44 → RowRef 1665 43 := ![.occ 128, .occ 134, .occ 137, .occ 192, .occ 201, .occ 290, .occ 320, .occ 366, .occ 373, .occ 379, .occ 385, .occ 706, .occ 870, .occ 997, .occ 1023, .occ 1160, .occ 1222, .occ 1236, .occ 1259, .occ 1348, .occ 1352, .occ 1358, .occ 1373, .occ 1380, .occ 1471, .occ 1481, .occ 1529, .occ 1623, .occ 1632, .occ 1636, .occ 1655, .occ 1659, .sumGe, .nonneg 7, .nonneg 19, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchGe 16 (1), .branchLe 37 (0), .branchLe 22 (0), .branchGe 27 (1), .branchGe 5 (1)]

def plane484GenLeaf0216Mult : Fin 44 → Nat := ![2226, 620, 1285, 4870, 951, 2136, 1145, 1690, 3217, 5678, 1794, 1169, 769, 872, 3110, 966, 440, 1219, 2353, 3740, 1260, 4249, 1351, 2697, 2014, 1227, 1169, 91, 1227, 616, 1268, 17, 9149, 1574, 1275, 3193, 6021, 21021, 9888, 34615, 9149, 2444, 14727, 23861]

theorem plane484GenLeaf0216 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0216Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0216Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0216Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0216Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 128
  · exact hroot.hOcc 134
  · exact hroot.hOcc 137
  · exact hroot.hOcc 192
  · exact hroot.hOcc 201
  · exact hroot.hOcc 290
  · exact hroot.hOcc 320
  · exact hroot.hOcc 366
  · exact hroot.hOcc 373
  · exact hroot.hOcc 379
  · exact hroot.hOcc 385
  · exact hroot.hOcc 706
  · exact hroot.hOcc 870
  · exact hroot.hOcc 997
  · exact hroot.hOcc 1023
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1222
  · exact hroot.hOcc 1236
  · exact hroot.hOcc 1259
  · exact hroot.hOcc 1348
  · exact hroot.hOcc 1352
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1373
  · exact hroot.hOcc 1380
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1529
  · exact hroot.hOcc 1623
  · exact hroot.hOcc 1632
  · exact hroot.hOcc 1636
  · exact hroot.hOcc 1655
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
