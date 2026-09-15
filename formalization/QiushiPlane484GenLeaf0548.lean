import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0548Refs : Fin 44 → RowRef 1665 43 := ![.occ 92, .occ 122, .occ 123, .occ 128, .occ 131, .occ 133, .occ 135, .occ 210, .occ 212, .occ 249, .occ 325, .occ 377, .occ 379, .occ 483, .occ 704, .occ 866, .occ 1102, .occ 1154, .occ 1158, .occ 1159, .occ 1206, .occ 1220, .occ 1333, .occ 1391, .occ 1401, .occ 1478, .occ 1483, .occ 1499, .occ 1578, .occ 1597, .occ 1610, .sumGe, .nonneg 39, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchGe 30 (1), .branchGe 1 (1), .branchLe 11 (0), .branchLe 32 (0), .branchGe 28 (1), .branchLe 9 (0), .branchGe 6 (1)]

def plane484GenLeaf0548Mult : Fin 44 → Nat := ![362, 756, 373, 53, 222, 1018, 37, 337, 53, 324, 28, 479, 275, 35, 870, 1280, 64, 262, 377, 523, 215, 111, 124, 144, 180, 641, 268, 129, 627, 18, 164, 1397, 110, 4016, 3012, 162, 1369, 2403, 1566, 157, 1397, 2723, 756, 5946]

theorem plane484GenLeaf0548 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0548Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0548Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0548Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0548Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 92
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 128
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 210
  · exact hroot.hOcc 212
  · exact hroot.hOcc 249
  · exact hroot.hOcc 325
  · exact hroot.hOcc 377
  · exact hroot.hOcc 379
  · exact hroot.hOcc 483
  · exact hroot.hOcc 704
  · exact hroot.hOcc 866
  · exact hroot.hOcc 1102
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1333
  · exact hroot.hOcc 1391
  · exact hroot.hOcc 1401
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1499
  · exact hroot.hOcc 1578
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1610
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (11 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
