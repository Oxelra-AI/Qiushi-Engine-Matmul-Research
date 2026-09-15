import QiushiPlane469GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane469GenLeaf0004Refs : Fin 61 → RowRef 217 60 := ![.occ 11, .occ 12, .occ 15, .occ 21, .occ 26, .occ 32, .occ 42, .occ 48, .occ 52, .occ 57, .occ 58, .occ 68, .occ 69, .occ 70, .occ 71, .occ 72, .occ 78, .occ 82, .occ 83, .occ 84, .occ 87, .occ 93, .occ 94, .occ 106, .occ 110, .occ 113, .occ 121, .occ 122, .occ 129, .occ 136, .occ 151, .occ 152, .occ 157, .occ 163, .occ 166, .occ 176, .occ 178, .occ 187, .occ 196, .occ 197, .occ 198, .occ 205, .occ 207, .occ 208, .occ 213, .sumGe, .nonneg 3, .nonneg 10, .nonneg 13, .nonneg 17, .nonneg 19, .nonneg 30, .nonneg 32, .nonneg 39, .nonneg 51, .nonneg 52, .nonneg 57, .branchLe 34 (0), .branchLe 8 (0), .branchLe 54 (0), .branchGe 40 (1)]

def plane469GenLeaf0004Mult : Fin 61 → Nat := ![839229, 2921476, 19359, 315694, 1776582, 669880, 2373065, 603961, 1527380, 11686, 1645453, 2837235, 973415, 393913, 1415900, 434309, 822055, 1027651, 345925, 941177, 13146, 417753, 772828, 354126, 1487495, 11975, 1440514, 689023, 805945, 813012, 466836, 1501663, 554798, 265284, 124723, 751575, 323218, 361109, 77197, 67851, 266001, 89152, 93657, 588550, 105299, 3904307, 1395227, 1232500, 1394441, 3369103, 885013, 175628, 4855426, 1338213, 910521, 3048972, 189059, 2979917, 2699048, 2528053, 16526794]

theorem plane469GenLeaf0004 (x : Fin 60 → Int)
    (hroot : plane469GenOccSys.RootHolds x)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hUB_34 : x 34 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_54 : x 54 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane469GenLeaf0004Refs i).resolveCoeff plane469GenOccSys j)
    (fun i => (plane469GenLeaf0004Refs i).resolveRhs plane469GenOccSys) plane469GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane469GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 11
  · exact hroot.hOcc 12
  · exact hroot.hOcc 15
  · exact hroot.hOcc 21
  · exact hroot.hOcc 26
  · exact hroot.hOcc 32
  · exact hroot.hOcc 42
  · exact hroot.hOcc 48
  · exact hroot.hOcc 52
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 68
  · exact hroot.hOcc 69
  · exact hroot.hOcc 70
  · exact hroot.hOcc 71
  · exact hroot.hOcc 72
  · exact hroot.hOcc 78
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 87
  · exact hroot.hOcc 93
  · exact hroot.hOcc 94
  · exact hroot.hOcc 106
  · exact hroot.hOcc 110
  · exact hroot.hOcc 113
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 129
  · exact hroot.hOcc 136
  · exact hroot.hOcc 151
  · exact hroot.hOcc 152
  · exact hroot.hOcc 157
  · exact hroot.hOcc 163
  · exact hroot.hOcc 166
  · exact hroot.hOcc 176
  · exact hroot.hOcc 178
  · exact hroot.hOcc 187
  · exact hroot.hOcc 196
  · exact hroot.hOcc 197
  · exact hroot.hOcc 198
  · exact hroot.hOcc 205
  · exact hroot.hOcc 207
  · exact hroot.hOcc 208
  · exact hroot.hOcc 213
  · change (∑ j, (-1 : Int) * x j) ≤ -plane469GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (10 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (13 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (17 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (30 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (32 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (39 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (51 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (52 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (57 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (34 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (8 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (54 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_54
  · change (∑ k, (if k = (40 : Fin 60) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40

end QiushiMatmul
