import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0502Refs : Fin 37 → RowRef 1665 43 := ![.occ 119, .occ 126, .occ 135, .occ 138, .occ 140, .occ 155, .occ 170, .occ 191, .occ 289, .occ 596, .occ 618, .occ 783, .occ 843, .occ 1112, .occ 1200, .occ 1208, .occ 1218, .occ 1235, .occ 1271, .occ 1276, .occ 1324, .occ 1358, .occ 1394, .occ 1410, .occ 1447, .occ 1550, .occ 1567, .occ 1590, .occ 1621, .occ 1658, .sumGe, .branchGe 15 (1), .branchLe 35 (0), .branchGe 7 (1), .branchGe 32 (1), .branchLe 39 (0), .branchLe 10 (0)]

def plane484GenLeaf0502Mult : Fin 37 → Nat := ![324, 122, 500, 700, 160, 36, 164, 36, 38, 32, 4, 846, 160, 662, 116, 240, 432, 185, 13, 80, 18, 196, 80, 603, 27, 786, 80, 242, 604, 252, 1556, 5214, 1316, 3998, 2848, 1476, 1396]

theorem plane484GenLeaf0502 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0502Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0502Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0502Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0502Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 126
  · exact hroot.hOcc 135
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 155
  · exact hroot.hOcc 170
  · exact hroot.hOcc 191
  · exact hroot.hOcc 289
  · exact hroot.hOcc 596
  · exact hroot.hOcc 618
  · exact hroot.hOcc 783
  · exact hroot.hOcc 843
  · exact hroot.hOcc 1112
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1218
  · exact hroot.hOcc 1235
  · exact hroot.hOcc 1271
  · exact hroot.hOcc 1276
  · exact hroot.hOcc 1324
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1394
  · exact hroot.hOcc 1410
  · exact hroot.hOcc 1447
  · exact hroot.hOcc 1550
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1621
  · exact hroot.hOcc 1658
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
