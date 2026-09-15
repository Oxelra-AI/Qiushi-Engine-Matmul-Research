import QiushiPlane458GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane458GenLeaf0001Refs : Fin 57 → RowRef 203 56 := ![.occ 7, .occ 9, .occ 13, .occ 20, .occ 26, .occ 31, .occ 33, .occ 35, .occ 47, .occ 50, .occ 51, .occ 54, .occ 57, .occ 69, .occ 74, .occ 75, .occ 77, .occ 84, .occ 92, .occ 95, .occ 99, .occ 102, .occ 106, .occ 108, .occ 111, .occ 114, .occ 120, .occ 124, .occ 126, .occ 130, .occ 133, .occ 134, .occ 139, .occ 140, .occ 141, .occ 149, .occ 161, .occ 166, .occ 167, .occ 169, .occ 181, .occ 186, .occ 194, .occ 195, .occ 196, .occ 200, .sumGe, .nonneg 6, .nonneg 29, .nonneg 32, .nonneg 39, .nonneg 52, .nonneg 53, .branchLe 46 (0), .branchLe 30 (0), .branchLe 31 (0), .branchGe 9 (1)]

def plane458GenLeaf0001Mult : Fin 57 → Nat := ![232703, 304438, 171378, 258158, 393798, 468384, 100995, 49198, 322700, 226888, 220149, 409528, 108964, 527949, 906900, 264018, 194902, 305327, 62606, 622292, 316511, 213489, 428904, 91130, 441536, 538767, 95077, 115442, 41015, 130067, 237439, 249380, 68707, 67967, 27398, 222135, 22288, 94996, 139063, 284210, 44102, 17885, 59921, 152373, 362088, 91391, 1307592, 441090, 745465, 719581, 394238, 170706, 257151, 1307592, 1307592, 632374, 3295194]

theorem plane458GenLeaf0001 (x : Fin 56 → Int)
    (hroot : plane458GenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane458GenLeaf0001Refs i).resolveCoeff plane458GenOccSys j)
    (fun i => (plane458GenLeaf0001Refs i).resolveRhs plane458GenOccSys) plane458GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane458GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · exact hroot.hOcc 9
  · exact hroot.hOcc 13
  · exact hroot.hOcc 20
  · exact hroot.hOcc 26
  · exact hroot.hOcc 31
  · exact hroot.hOcc 33
  · exact hroot.hOcc 35
  · exact hroot.hOcc 47
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 54
  · exact hroot.hOcc 57
  · exact hroot.hOcc 69
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
  · exact hroot.hOcc 77
  · exact hroot.hOcc 84
  · exact hroot.hOcc 92
  · exact hroot.hOcc 95
  · exact hroot.hOcc 99
  · exact hroot.hOcc 102
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 111
  · exact hroot.hOcc 114
  · exact hroot.hOcc 120
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 130
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 149
  · exact hroot.hOcc 161
  · exact hroot.hOcc 166
  · exact hroot.hOcc 167
  · exact hroot.hOcc 169
  · exact hroot.hOcc 181
  · exact hroot.hOcc 186
  · exact hroot.hOcc 194
  · exact hroot.hOcc 195
  · exact hroot.hOcc 196
  · exact hroot.hOcc 200
  · change (∑ j, (-1 : Int) * x j) ≤ -plane458GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (29 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (32 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (39 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (52 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (53 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (46 : Fin 56) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (30 : Fin 56) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (31 : Fin 56) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (9 : Fin 56) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
