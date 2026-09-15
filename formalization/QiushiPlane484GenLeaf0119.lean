import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0119Refs : Fin 44 → RowRef 1665 43 := ![.occ 92, .occ 128, .occ 130, .occ 131, .occ 133, .occ 141, .occ 385, .occ 447, .occ 474, .occ 745, .occ 754, .occ 859, .occ 860, .occ 861, .occ 1161, .occ 1166, .occ 1224, .occ 1262, .occ 1289, .occ 1403, .occ 1407, .occ 1443, .occ 1458, .occ 1517, .occ 1538, .occ 1558, .occ 1601, .occ 1603, .occ 1632, .occ 1639, .occ 1656, .occ 1659, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 39 (0), .branchLe 32 (0), .branchLe 28 (0), .branchLe 5 (0), .branchLe 6 (0), .branchLe 40 (0)]

def plane484GenLeaf0119Mult : Fin 44 → Nat := ![1096, 8176, 11126, 2089, 2713, 2357, 6361, 320, 8390, 7230, 4000, 2936, 12718, 1200, 936, 9072, 4476, 3416, 6026, 4532, 30, 2906, 1736, 6156, 11656, 11336, 498, 13050, 5146, 2428, 2438, 1360, 40488, 34326, 35124, 40412, 35342, 23334, 24316, 40488, 27438, 16514, 25284, 40488]

theorem plane484GenLeaf0119 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0119Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0119Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0119Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0119Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 92
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 141
  · exact hroot.hOcc 385
  · exact hroot.hOcc 447
  · exact hroot.hOcc 474
  · exact hroot.hOcc 745
  · exact hroot.hOcc 754
  · exact hroot.hOcc 859
  · exact hroot.hOcc 860
  · exact hroot.hOcc 861
  · exact hroot.hOcc 1161
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1224
  · exact hroot.hOcc 1262
  · exact hroot.hOcc 1289
  · exact hroot.hOcc 1403
  · exact hroot.hOcc 1407
  · exact hroot.hOcc 1443
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1517
  · exact hroot.hOcc 1538
  · exact hroot.hOcc 1558
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1632
  · exact hroot.hOcc 1639
  · exact hroot.hOcc 1656
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (40 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40

end QiushiMatmul
