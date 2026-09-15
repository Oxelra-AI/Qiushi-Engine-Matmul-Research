import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0064Refs : Fin 49 → RowRef 668 48 := ![.occ 86, .occ 95, .occ 99, .occ 103, .occ 128, .occ 130, .occ 161, .occ 166, .occ 188, .occ 198, .occ 206, .occ 220, .occ 223, .occ 224, .occ 230, .occ 246, .occ 281, .occ 308, .occ 315, .occ 316, .occ 329, .occ 343, .occ 348, .occ 377, .occ 381, .occ 383, .occ 401, .occ 402, .occ 415, .occ 507, .occ 509, .occ 515, .occ 531, .occ 546, .occ 547, .occ 604, .occ 644, .occ 645, .occ 650, .occ 653, .sumGe, .branchGe 39 (1), .branchLe 7 (0), .branchLe 28 (0), .branchLe 40 (0), .branchLe 29 (0), .branchGe 19 (1), .branchLe 17 (0), .branchLe 4 (0)]

def plane487GenLeaf0064Mult : Fin 49 → Nat := ![160658, 57144, 25084, 113556, 41780, 145283, 278881, 9588, 4617, 95562, 87241, 56281, 115258, 145283, 48886, 3191, 85719, 93102, 175152, 31582, 25629, 88244, 80105, 25081, 54392, 150200, 28664, 78658, 84643, 23383, 28664, 26598, 30615, 26933, 25710, 2096, 53837, 25143, 52047, 60611, 366425, 553321, 156500, 340715, 305814, 124641, 1353811, 309937, 305814]

theorem plane487GenLeaf0064 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0064Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0064Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0064Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0064Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 86
  · exact hroot.hOcc 95
  · exact hroot.hOcc 99
  · exact hroot.hOcc 103
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 161
  · exact hroot.hOcc 166
  · exact hroot.hOcc 188
  · exact hroot.hOcc 198
  · exact hroot.hOcc 206
  · exact hroot.hOcc 220
  · exact hroot.hOcc 223
  · exact hroot.hOcc 224
  · exact hroot.hOcc 230
  · exact hroot.hOcc 246
  · exact hroot.hOcc 281
  · exact hroot.hOcc 308
  · exact hroot.hOcc 315
  · exact hroot.hOcc 316
  · exact hroot.hOcc 329
  · exact hroot.hOcc 343
  · exact hroot.hOcc 348
  · exact hroot.hOcc 377
  · exact hroot.hOcc 381
  · exact hroot.hOcc 383
  · exact hroot.hOcc 401
  · exact hroot.hOcc 402
  · exact hroot.hOcc 415
  · exact hroot.hOcc 507
  · exact hroot.hOcc 509
  · exact hroot.hOcc 515
  · exact hroot.hOcc 531
  · exact hroot.hOcc 546
  · exact hroot.hOcc 547
  · exact hroot.hOcc 604
  · exact hroot.hOcc 644
  · exact hroot.hOcc 645
  · exact hroot.hOcc 650
  · exact hroot.hOcc 653
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (28 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (29 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (19 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (17 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (4 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4

end QiushiMatmul
