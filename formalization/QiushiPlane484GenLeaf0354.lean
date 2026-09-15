import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0354Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 124, .occ 125, .occ 128, .occ 287, .occ 386, .occ 446, .occ 447, .occ 565, .occ 615, .occ 859, .occ 861, .occ 1145, .occ 1164, .occ 1186, .occ 1187, .occ 1190, .occ 1224, .occ 1305, .occ 1381, .occ 1403, .occ 1455, .occ 1456, .occ 1458, .occ 1489, .occ 1521, .occ 1608, .occ 1609, .occ 1655, .sumGe, .nonneg 9, .nonneg 21, .nonneg 26, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchLe 35 (0), .branchLe 3 (0), .branchLe 24 (0), .branchLe 18 (0), .branchLe 19 (0), .branchLe 14 (0), .branchGe 8 (1)]

def plane484GenLeaf0354Mult : Fin 44 → Nat := ![6, 2, 42, 53, 99, 133, 55, 30, 2, 20, 67, 89, 28, 52, 60, 20, 2, 24, 4, 15, 8, 14, 1, 16, 24, 6, 92, 6, 18, 176, 43, 16, 49, 176, 202, 30, 297, 176, 10, 76, 98, 96, 42, 591]

theorem plane484GenLeaf0354 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0354Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0354Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0354Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0354Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 287
  · exact hroot.hOcc 386
  · exact hroot.hOcc 446
  · exact hroot.hOcc 447
  · exact hroot.hOcc 565
  · exact hroot.hOcc 615
  · exact hroot.hOcc 859
  · exact hroot.hOcc 861
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1224
  · exact hroot.hOcc 1305
  · exact hroot.hOcc 1381
  · exact hroot.hOcc 1403
  · exact hroot.hOcc 1455
  · exact hroot.hOcc 1456
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1521
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1655
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
