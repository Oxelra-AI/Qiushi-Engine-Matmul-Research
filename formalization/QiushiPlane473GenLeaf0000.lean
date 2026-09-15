import QiushiPlane473GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane473GenLeaf0000Refs : Fin 60 → RowRef 153 59 := ![.occ 7, .occ 9, .occ 11, .occ 20, .occ 23, .occ 27, .occ 36, .occ 37, .occ 40, .occ 44, .occ 45, .occ 46, .occ 51, .occ 52, .occ 54, .occ 58, .occ 61, .occ 67, .occ 70, .occ 71, .occ 73, .occ 76, .occ 78, .occ 79, .occ 80, .occ 81, .occ 87, .occ 88, .occ 92, .occ 93, .occ 97, .occ 98, .occ 100, .occ 101, .occ 105, .occ 108, .occ 110, .occ 112, .occ 118, .occ 119, .occ 121, .occ 122, .occ 123, .occ 126, .occ 136, .occ 137, .occ 143, .occ 145, .occ 146, .occ 147, .occ 148, .occ 149, .sumGe, .nonneg 19, .nonneg 38, .nonneg 55, .branchLe 40 (0), .branchLe 14 (0), .branchLe 44 (0), .branchLe 20 (0)]

def plane473GenLeaf0000Mult : Fin 60 → Nat := ![16363076, 5286984, 2322044, 20094480, 5702168, 15256936, 65159606, 14363002, 7698312, 34135732, 27155278, 61067154, 39357161, 11493623, 39165826, 12828024, 6979785, 4942977, 25972081, 24238549, 3529840, 28762028, 32400837, 19710105, 30263031, 48886410, 18882408, 10257989, 17673256, 23332854, 4498954, 1471412, 15777820, 25461716, 10962164, 26568866, 10895266, 13193080, 7445312, 35273540, 5245948, 7850396, 9247384, 6505506, 25603666, 4678034, 645261, 13011010, 12373555, 9532092, 6358412, 1639222, 152688616, 37997992, 134677080, 34499584, 138038384, 136798112, 84440320, 127439008]

theorem plane473GenLeaf0000 (x : Fin 59 → Int)
    (hroot : plane473GenOccSys.RootHolds x)
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane473GenLeaf0000Refs i).resolveCoeff plane473GenOccSys j)
    (fun i => (plane473GenLeaf0000Refs i).resolveRhs plane473GenOccSys) plane473GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane473GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · exact hroot.hOcc 9
  · exact hroot.hOcc 11
  · exact hroot.hOcc 20
  · exact hroot.hOcc 23
  · exact hroot.hOcc 27
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 40
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 46
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 54
  · exact hroot.hOcc 58
  · exact hroot.hOcc 61
  · exact hroot.hOcc 67
  · exact hroot.hOcc 70
  · exact hroot.hOcc 71
  · exact hroot.hOcc 73
  · exact hroot.hOcc 76
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 92
  · exact hroot.hOcc 93
  · exact hroot.hOcc 97
  · exact hroot.hOcc 98
  · exact hroot.hOcc 100
  · exact hroot.hOcc 101
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 110
  · exact hroot.hOcc 112
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 126
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 143
  · exact hroot.hOcc 145
  · exact hroot.hOcc 146
  · exact hroot.hOcc 147
  · exact hroot.hOcc 148
  · exact hroot.hOcc 149
  · change (∑ j, (-1 : Int) * x j) ≤ -plane473GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (38 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (55 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (40 : Fin 59) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (14 : Fin 59) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (44 : Fin 59) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (20 : Fin 59) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20

end QiushiMatmul
