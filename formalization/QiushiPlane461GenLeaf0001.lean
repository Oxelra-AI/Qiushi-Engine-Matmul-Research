import QiushiPlane461GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane461GenLeaf0001Refs : Fin 63 → RowRef 151 62 := ![.occ 2, .occ 3, .occ 10, .occ 14, .occ 17, .occ 18, .occ 19, .occ 23, .occ 26, .occ 28, .occ 30, .occ 32, .occ 33, .occ 34, .occ 36, .occ 37, .occ 38, .occ 39, .occ 40, .occ 41, .occ 43, .occ 44, .occ 49, .occ 53, .occ 55, .occ 62, .occ 65, .occ 66, .occ 73, .occ 74, .occ 86, .occ 87, .occ 89, .occ 90, .occ 91, .occ 97, .occ 98, .occ 104, .occ 106, .occ 123, .occ 136, .occ 140, .occ 141, .occ 142, .occ 143, .occ 144, .occ 147, .sumGe, .nonneg 6, .nonneg 9, .nonneg 10, .nonneg 15, .nonneg 25, .nonneg 32, .nonneg 33, .nonneg 36, .nonneg 38, .nonneg 43, .nonneg 51, .nonneg 53, .branchLe 16 (0), .branchLe 7 (0), .branchGe 22 (1)]

def plane461GenLeaf0001Mult : Fin 63 → Nat := ![61469, 305218, 110619, 689742, 1094053, 151491, 766240, 570677, 389849, 580420, 2111497, 440151, 946914, 691019, 375181, 254533, 690981, 552881, 342274, 736987, 544522, 400722, 322620, 645815, 584679, 581548, 260547, 172767, 820278, 729302, 521246, 448265, 1231707, 277171, 475285, 446901, 405717, 52539, 8143, 332056, 77682, 153761, 70296, 253834, 133606, 384444, 416611, 3014142, 2672947, 2709500, 13918, 5328, 237894, 1736795, 1229604, 1149722, 1326323, 124131, 1167959, 1195830, 2860381, 824963, 3878062]

theorem plane461GenLeaf0001 (x : Fin 62 → Int)
    (hroot : plane461GenOccSys.RootHolds x)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane461GenLeaf0001Refs i).resolveCoeff plane461GenOccSys j)
    (fun i => (plane461GenLeaf0001Refs i).resolveRhs plane461GenOccSys) plane461GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane461GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 3
  · exact hroot.hOcc 10
  · exact hroot.hOcc 14
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 23
  · exact hroot.hOcc 26
  · exact hroot.hOcc 28
  · exact hroot.hOcc 30
  · exact hroot.hOcc 32
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 38
  · exact hroot.hOcc 39
  · exact hroot.hOcc 40
  · exact hroot.hOcc 41
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 49
  · exact hroot.hOcc 53
  · exact hroot.hOcc 55
  · exact hroot.hOcc 62
  · exact hroot.hOcc 65
  · exact hroot.hOcc 66
  · exact hroot.hOcc 73
  · exact hroot.hOcc 74
  · exact hroot.hOcc 86
  · exact hroot.hOcc 87
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 91
  · exact hroot.hOcc 97
  · exact hroot.hOcc 98
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 123
  · exact hroot.hOcc 136
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 143
  · exact hroot.hOcc 144
  · exact hroot.hOcc 147
  · change (∑ j, (-1 : Int) * x j) ≤ -plane461GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (9 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (10 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (15 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (25 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (32 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (33 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (36 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (38 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (43 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (51 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (53 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (16 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (7 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (22 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
