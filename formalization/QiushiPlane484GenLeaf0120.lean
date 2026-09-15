import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0120Refs : Fin 44 → RowRef 1665 43 := ![.occ 130, .occ 132, .occ 139, .occ 141, .occ 404, .occ 452, .occ 462, .occ 480, .occ 545, .occ 607, .occ 643, .occ 688, .occ 1168, .occ 1172, .occ 1179, .occ 1191, .occ 1215, .occ 1224, .occ 1232, .occ 1289, .occ 1290, .occ 1312, .occ 1321, .occ 1427, .occ 1443, .occ 1456, .occ 1471, .occ 1489, .occ 1548, .occ 1603, .occ 1619, .occ 1659, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 39 (0), .branchLe 32 (0), .branchLe 28 (0), .branchLe 5 (0), .branchLe 6 (0), .branchGe 40 (1)]

def plane484GenLeaf0120Mult : Fin 44 → Nat := ![101945, 46855, 94889, 62233, 192956, 991, 51263, 20913, 49136, 61649, 32811, 123351, 20233, 21438, 93317, 11840, 98303, 6545, 16512, 44428, 42348, 31559, 33372, 126101, 29991, 59194, 82743, 7893, 38128, 34090, 53218, 29240, 369252, 286794, 349519, 683984, 275935, 301133, 369252, 303176, 161139, 340012, 340012, 783973]

theorem plane484GenLeaf0120 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0120Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0120Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0120Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0120Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 130
  · exact hroot.hOcc 132
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 404
  · exact hroot.hOcc 452
  · exact hroot.hOcc 462
  · exact hroot.hOcc 480
  · exact hroot.hOcc 545
  · exact hroot.hOcc 607
  · exact hroot.hOcc 643
  · exact hroot.hOcc 688
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1224
  · exact hroot.hOcc 1232
  · exact hroot.hOcc 1289
  · exact hroot.hOcc 1290
  · exact hroot.hOcc 1312
  · exact hroot.hOcc 1321
  · exact hroot.hOcc 1427
  · exact hroot.hOcc 1443
  · exact hroot.hOcc 1456
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1548
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1619
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
  · change (∑ k, (if k = (40 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40

end QiushiMatmul
