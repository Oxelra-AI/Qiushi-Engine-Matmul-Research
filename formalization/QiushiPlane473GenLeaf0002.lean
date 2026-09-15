import QiushiPlane473GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane473GenLeaf0002Refs : Fin 60 → RowRef 153 59 := ![.occ 8, .occ 9, .occ 13, .occ 17, .occ 26, .occ 29, .occ 32, .occ 36, .occ 37, .occ 38, .occ 43, .occ 44, .occ 45, .occ 46, .occ 48, .occ 49, .occ 50, .occ 51, .occ 52, .occ 53, .occ 54, .occ 57, .occ 58, .occ 59, .occ 61, .occ 70, .occ 71, .occ 74, .occ 78, .occ 79, .occ 80, .occ 81, .occ 84, .occ 85, .occ 88, .occ 91, .occ 92, .occ 97, .occ 102, .occ 104, .occ 109, .occ 113, .occ 122, .occ 123, .occ 125, .occ 133, .occ 134, .occ 143, .occ 152, .sumGe, .nonneg 9, .nonneg 16, .nonneg 28, .nonneg 38, .nonneg 51, .nonneg 54, .nonneg 55, .branchLe 40 (0), .branchLe 14 (0), .branchGe 44 (1)]

def plane473GenLeaf0002Mult : Fin 60 → Nat := ![751580, 691332, 320175, 707348, 149231, 4012748, 1717663, 600154, 1839881, 2036091, 640128, 822990, 2624727, 1779951, 971226, 3190544, 1218284, 2783691, 835139, 131785, 2233452, 26250, 1875679, 1804002, 2968646, 3648330, 2583908, 763688, 2229955, 1230852, 326832, 2020015, 313373, 459587, 1022370, 1777678, 2528262, 553736, 533859, 781786, 895365, 103137, 110862, 1130180, 277678, 10220, 1560700, 810865, 806289, 7705519, 337629, 1276016, 83409, 174535, 1683916, 1151103, 1488082, 6336506, 6998171, 19095931]

theorem plane473GenLeaf0002 (x : Fin 59 → Int)
    (hroot : plane473GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane473GenLeaf0002Refs i).resolveCoeff plane473GenOccSys j)
    (fun i => (plane473GenLeaf0002Refs i).resolveRhs plane473GenOccSys) plane473GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane473GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · exact hroot.hOcc 9
  · exact hroot.hOcc 13
  · exact hroot.hOcc 17
  · exact hroot.hOcc 26
  · exact hroot.hOcc 29
  · exact hroot.hOcc 32
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 38
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 46
  · exact hroot.hOcc 48
  · exact hroot.hOcc 49
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 53
  · exact hroot.hOcc 54
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 59
  · exact hroot.hOcc 61
  · exact hroot.hOcc 70
  · exact hroot.hOcc 71
  · exact hroot.hOcc 74
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 88
  · exact hroot.hOcc 91
  · exact hroot.hOcc 92
  · exact hroot.hOcc 97
  · exact hroot.hOcc 102
  · exact hroot.hOcc 104
  · exact hroot.hOcc 109
  · exact hroot.hOcc 113
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 143
  · exact hroot.hOcc 152
  · change (∑ j, (-1 : Int) * x j) ≤ -plane473GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (9 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (16 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (28 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (38 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (51 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (54 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (55 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (40 : Fin 59) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (14 : Fin 59) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (44 : Fin 59) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44

end QiushiMatmul
