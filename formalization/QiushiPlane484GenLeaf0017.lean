import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0017Refs : Fin 40 → RowRef 1665 43 := ![.occ 139, .occ 141, .occ 330, .occ 522, .occ 531, .occ 538, .occ 612, .occ 697, .occ 1049, .occ 1147, .occ 1150, .occ 1170, .occ 1172, .occ 1186, .occ 1187, .occ 1286, .occ 1305, .occ 1308, .occ 1335, .occ 1390, .occ 1392, .occ 1405, .occ 1432, .occ 1477, .occ 1512, .occ 1522, .occ 1631, .occ 1658, .occ 1664, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 35 (0), .branchGe 41 (1), .branchGe 19 (1), .branchLe 10 (0), .branchLe 5 (0)]

def plane484GenLeaf0017Mult : Fin 40 → Nat := ![4718, 1573, 3247, 1344, 2782, 934, 598, 1400, 1332, 467, 16, 2618, 1856, 1718, 1849, 184, 1602, 1394, 413, 784, 482, 2839, 1319, 1856, 1329, 1412, 682, 3112, 1090, 10384, 934, 6350, 10384, 6740, 5416, 7284, 19612, 26348, 10200, 5860]

theorem plane484GenLeaf0017 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0017Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0017Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0017Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0017Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 330
  · exact hroot.hOcc 522
  · exact hroot.hOcc 531
  · exact hroot.hOcc 538
  · exact hroot.hOcc 612
  · exact hroot.hOcc 697
  · exact hroot.hOcc 1049
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1286
  · exact hroot.hOcc 1305
  · exact hroot.hOcc 1308
  · exact hroot.hOcc 1335
  · exact hroot.hOcc 1390
  · exact hroot.hOcc 1392
  · exact hroot.hOcc 1405
  · exact hroot.hOcc 1432
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1512
  · exact hroot.hOcc 1522
  · exact hroot.hOcc 1631
  · exact hroot.hOcc 1658
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5

end QiushiMatmul
