import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0365Refs : Fin 44 → RowRef 1665 43 := ![.occ 122, .occ 125, .occ 131, .occ 132, .occ 135, .occ 136, .occ 137, .occ 407, .occ 476, .occ 523, .occ 541, .occ 580, .occ 641, .occ 644, .occ 1147, .occ 1164, .occ 1166, .occ 1188, .occ 1190, .occ 1213, .occ 1215, .occ 1255, .occ 1256, .occ 1284, .occ 1451, .occ 1462, .occ 1479, .occ 1489, .occ 1491, .occ 1580, .sumGe, .nonneg 16, .nonneg 26, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchLe 35 (0), .branchLe 3 (0), .branchGe 24 (1), .branchGe 40 (1), .branchLe 5 (0), .branchGe 41 (1), .branchLe 9 (0)]

def plane484GenLeaf0365Mult : Fin 44 → Nat := ![726, 278, 2287, 783, 873, 2137, 930, 1190, 528, 2272, 2124, 220, 94, 600, 1048, 328, 1026, 212, 122, 80, 1024, 184, 1504, 452, 868, 1024, 864, 334, 1334, 706, 4424, 1052, 308, 1052, 2844, 3070, 8724, 4344, 2042, 10468, 4080, 4146, 7178, 3812]

theorem plane484GenLeaf0365 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0365Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0365Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0365Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0365Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 125
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 407
  · exact hroot.hOcc 476
  · exact hroot.hOcc 523
  · exact hroot.hOcc 541
  · exact hroot.hOcc 580
  · exact hroot.hOcc 641
  · exact hroot.hOcc 644
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1255
  · exact hroot.hOcc 1256
  · exact hroot.hOcc 1284
  · exact hroot.hOcc 1451
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1479
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1580
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (40 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9

end QiushiMatmul
