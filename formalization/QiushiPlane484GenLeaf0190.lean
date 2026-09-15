import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0190Refs : Fin 42 → RowRef 1665 43 := ![.occ 120, .occ 196, .occ 200, .occ 437, .occ 657, .occ 710, .occ 789, .occ 1170, .occ 1213, .occ 1257, .occ 1259, .occ 1265, .occ 1268, .occ 1269, .occ 1340, .occ 1341, .occ 1345, .occ 1346, .occ 1373, .occ 1380, .occ 1492, .occ 1500, .occ 1505, .occ 1522, .occ 1524, .occ 1561, .occ 1606, .occ 1623, .occ 1656, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchLe 1 (0), .branchGe 5 (1), .branchLe 22 (0), .branchGe 30 (1), .branchLe 40 (0), .branchLe 4 (0)]

def plane484GenLeaf0190Mult : Fin 42 → Nat := ![317, 358, 188, 9, 31, 115, 85, 132, 29, 138, 33, 22, 28, 116, 127, 91, 50, 226, 132, 31, 168, 77, 48, 65, 161, 29, 161, 82, 137, 692, 543, 524, 699, 1126, 358, 55, 526, 1368, 692, 1161, 692, 692]

theorem plane484GenLeaf0190 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0190Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0190Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0190Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0190Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 196
  · exact hroot.hOcc 200
  · exact hroot.hOcc 437
  · exact hroot.hOcc 657
  · exact hroot.hOcc 710
  · exact hroot.hOcc 789
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1257
  · exact hroot.hOcc 1259
  · exact hroot.hOcc 1265
  · exact hroot.hOcc 1268
  · exact hroot.hOcc 1269
  · exact hroot.hOcc 1340
  · exact hroot.hOcc 1341
  · exact hroot.hOcc 1345
  · exact hroot.hOcc 1346
  · exact hroot.hOcc 1373
  · exact hroot.hOcc 1380
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1500
  · exact hroot.hOcc 1505
  · exact hroot.hOcc 1522
  · exact hroot.hOcc 1524
  · exact hroot.hOcc 1561
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1623
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (40 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4

end QiushiMatmul
