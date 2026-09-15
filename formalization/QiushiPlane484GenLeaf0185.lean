import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0185Refs : Fin 27 → RowRef 1665 43 := ![.occ 212, .occ 220, .occ 437, .occ 470, .occ 633, .occ 840, .occ 889, .occ 1013, .occ 1114, .occ 1117, .occ 1227, .occ 1425, .occ 1486, .occ 1499, .occ 1516, .occ 1607, .occ 1623, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 1 (0), .branchGe 7 (1), .branchLe 39 (0), .branchGe 22 (1)]

def plane484GenLeaf0185Mult : Fin 27 → Nat := ![1, 1, 2, 3, 4, 3, 3, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 10, 25, 3, 3, 15, 4, 12]

theorem plane484GenLeaf0185 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0185Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0185Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0185Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0185Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 212
  · exact hroot.hOcc 220
  · exact hroot.hOcc 437
  · exact hroot.hOcc 470
  · exact hroot.hOcc 633
  · exact hroot.hOcc 840
  · exact hroot.hOcc 889
  · exact hroot.hOcc 1013
  · exact hroot.hOcc 1114
  · exact hroot.hOcc 1117
  · exact hroot.hOcc 1227
  · exact hroot.hOcc 1425
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1499
  · exact hroot.hOcc 1516
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1623
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
