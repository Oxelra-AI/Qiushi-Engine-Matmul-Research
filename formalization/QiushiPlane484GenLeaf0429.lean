import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0429Refs : Fin 44 → RowRef 1665 43 := ![.occ 122, .occ 124, .occ 125, .occ 127, .occ 135, .occ 142, .occ 175, .occ 353, .occ 354, .occ 581, .occ 650, .occ 813, .occ 964, .occ 1097, .occ 1136, .occ 1188, .occ 1244, .occ 1289, .occ 1307, .occ 1339, .occ 1358, .occ 1375, .occ 1439, .occ 1447, .occ 1477, .occ 1522, .occ 1609, .occ 1627, .occ 1639, .occ 1651, .occ 1656, .occ 1659, .sumGe, .nonneg 0, .nonneg 2, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 29 (0), .branchLe 23 (0), .branchLe 19 (0), .branchLe 40 (0), .branchLe 28 (0), .branchGe 4 (1)]

def plane484GenLeaf0429Mult : Fin 44 → Nat := ![4148, 10603, 13403, 13727, 10151, 13424, 3653, 7319, 2508, 5476, 3940, 16362, 1693, 1048, 13772, 628, 2707, 619, 208, 414, 15761, 928, 4029, 6528, 765, 2104, 4086, 354, 867, 10326, 293, 2037, 35089, 17644, 563, 53142, 30706, 1256, 21024, 34222, 32692, 35089, 19328, 97641]

theorem plane484GenLeaf0429 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0429Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0429Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0429Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0429Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 135
  · exact hroot.hOcc 142
  · exact hroot.hOcc 175
  · exact hroot.hOcc 353
  · exact hroot.hOcc 354
  · exact hroot.hOcc 581
  · exact hroot.hOcc 650
  · exact hroot.hOcc 813
  · exact hroot.hOcc 964
  · exact hroot.hOcc 1097
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1244
  · exact hroot.hOcc 1289
  · exact hroot.hOcc 1307
  · exact hroot.hOcc 1339
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1375
  · exact hroot.hOcc 1439
  · exact hroot.hOcc 1447
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1522
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1627
  · exact hroot.hOcc 1639
  · exact hroot.hOcc 1651
  · exact hroot.hOcc 1656
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (40 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
