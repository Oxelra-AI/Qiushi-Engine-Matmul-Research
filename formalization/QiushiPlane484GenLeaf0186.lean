import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0186Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 220, .occ 242, .occ 307, .occ 309, .occ 445, .occ 470, .occ 737, .occ 1164, .occ 1196, .occ 1227, .occ 1239, .occ 1241, .occ 1259, .occ 1260, .occ 1292, .occ 1337, .occ 1357, .occ 1373, .occ 1411, .occ 1417, .occ 1440, .occ 1486, .occ 1509, .occ 1511, .occ 1513, .occ 1514, .occ 1546, .occ 1555, .occ 1601, .occ 1603, .occ 1606, .sumGe, .nonneg 15, .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchLe 1 (0), .branchLe 5 (0), .branchGe 7 (1), .branchGe 39 (1), .branchLe 34 (0)]

def plane484GenLeaf0186Mult : Fin 44 → Nat := ![970, 733, 2308, 535, 151, 2362, 229, 283, 2405, 345, 316, 97, 334, 439, 36, 57, 1864, 20, 55, 644, 756, 1627, 30, 278, 136, 137, 650, 624, 1667, 197, 97, 20, 3709, 1519, 3334, 11097, 6918, 2929, 3709, 3709, 3179, 5556, 10130, 3512]

theorem plane484GenLeaf0186 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0186Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0186Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0186Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0186Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 220
  · exact hroot.hOcc 242
  · exact hroot.hOcc 307
  · exact hroot.hOcc 309
  · exact hroot.hOcc 445
  · exact hroot.hOcc 470
  · exact hroot.hOcc 737
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1227
  · exact hroot.hOcc 1239
  · exact hroot.hOcc 1241
  · exact hroot.hOcc 1259
  · exact hroot.hOcc 1260
  · exact hroot.hOcc 1292
  · exact hroot.hOcc 1337
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1373
  · exact hroot.hOcc 1411
  · exact hroot.hOcc 1417
  · exact hroot.hOcc 1440
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1509
  · exact hroot.hOcc 1511
  · exact hroot.hOcc 1513
  · exact hroot.hOcc 1514
  · exact hroot.hOcc 1546
  · exact hroot.hOcc 1555
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1606
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34

end QiushiMatmul
