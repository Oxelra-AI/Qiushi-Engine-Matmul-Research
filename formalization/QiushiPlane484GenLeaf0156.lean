import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0156Refs : Fin 44 → RowRef 1665 43 := ![.occ 121, .occ 127, .occ 128, .occ 509, .occ 581, .occ 582, .occ 614, .occ 727, .occ 777, .occ 780, .occ 808, .occ 1045, .occ 1059, .occ 1164, .occ 1215, .occ 1216, .occ 1238, .occ 1376, .occ 1380, .occ 1383, .occ 1389, .occ 1404, .occ 1406, .occ 1414, .occ 1432, .occ 1434, .occ 1443, .occ 1452, .occ 1494, .occ 1608, .occ 1633, .occ 1636, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 18 (0), .branchLe 30 (0), .branchLe 21 (0), .branchGe 42 (1), .branchLe 0 (0), .branchGe 26 (1)]

def plane484GenLeaf0156Mult : Fin 44 → Nat := ![998, 1237, 362, 293, 1034, 590, 1174, 116, 1952, 3033, 980, 541, 605, 128, 490, 1360, 326, 439, 975, 491, 163, 690, 637, 363, 642, 362, 109, 549, 730, 1587, 664, 315, 4121, 1781, 1238, 4624, 4121, 10448, 1978, 2534, 3643, 11822, 1046, 10268]

theorem plane484GenLeaf0156 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0156Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0156Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0156Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0156Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 509
  · exact hroot.hOcc 581
  · exact hroot.hOcc 582
  · exact hroot.hOcc 614
  · exact hroot.hOcc 727
  · exact hroot.hOcc 777
  · exact hroot.hOcc 780
  · exact hroot.hOcc 808
  · exact hroot.hOcc 1045
  · exact hroot.hOcc 1059
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1238
  · exact hroot.hOcc 1376
  · exact hroot.hOcc 1380
  · exact hroot.hOcc 1383
  · exact hroot.hOcc 1389
  · exact hroot.hOcc 1404
  · exact hroot.hOcc 1406
  · exact hroot.hOcc 1414
  · exact hroot.hOcc 1432
  · exact hroot.hOcc 1434
  · exact hroot.hOcc 1443
  · exact hroot.hOcc 1452
  · exact hroot.hOcc 1494
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1633
  · exact hroot.hOcc 1636
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26

end QiushiMatmul
