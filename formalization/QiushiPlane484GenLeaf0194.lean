import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0194Refs : Fin 42 → RowRef 1665 43 := ![.occ 120, .occ 129, .occ 130, .occ 132, .occ 201, .occ 309, .occ 339, .occ 358, .occ 365, .occ 370, .occ 371, .occ 376, .occ 390, .occ 437, .occ 470, .occ 810, .occ 1023, .occ 1154, .occ 1241, .occ 1242, .occ 1262, .occ 1269, .occ 1296, .occ 1303, .occ 1334, .occ 1373, .occ 1440, .occ 1555, .occ 1617, .occ 1626, .sumGe, .nonneg 15, .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchLe 1 (0), .branchGe 5 (1), .branchGe 22 (1), .branchLe 19 (0), .branchGe 39 (1)]

def plane484GenLeaf0194Mult : Fin 42 → Nat := ![33, 22, 6, 10, 93, 37, 38, 3, 50, 30, 84, 72, 52, 16, 56, 28, 26, 3, 18, 4, 8, 16, 7, 2, 29, 51, 14, 31, 13, 9, 93, 18, 93, 384, 263, 46, 74, 90, 404, 293, 77, 365]

theorem plane484GenLeaf0194 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0194Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0194Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0194Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0194Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 132
  · exact hroot.hOcc 201
  · exact hroot.hOcc 309
  · exact hroot.hOcc 339
  · exact hroot.hOcc 358
  · exact hroot.hOcc 365
  · exact hroot.hOcc 370
  · exact hroot.hOcc 371
  · exact hroot.hOcc 376
  · exact hroot.hOcc 390
  · exact hroot.hOcc 437
  · exact hroot.hOcc 470
  · exact hroot.hOcc 810
  · exact hroot.hOcc 1023
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1241
  · exact hroot.hOcc 1242
  · exact hroot.hOcc 1262
  · exact hroot.hOcc 1269
  · exact hroot.hOcc 1296
  · exact hroot.hOcc 1303
  · exact hroot.hOcc 1334
  · exact hroot.hOcc 1373
  · exact hroot.hOcc 1440
  · exact hroot.hOcc 1555
  · exact hroot.hOcc 1617
  · exact hroot.hOcc 1626
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39

end QiushiMatmul
