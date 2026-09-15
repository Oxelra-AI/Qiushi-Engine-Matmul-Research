import QiushiPlane462GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane462GenLeaf0002Refs : Fin 63 → RowRef 294 62 := ![.occ 2, .occ 5, .occ 8, .occ 14, .occ 26, .occ 71, .occ 74, .occ 77, .occ 78, .occ 81, .occ 82, .occ 85, .occ 88, .occ 89, .occ 91, .occ 92, .occ 97, .occ 99, .occ 100, .occ 102, .occ 109, .occ 113, .occ 115, .occ 116, .occ 117, .occ 119, .occ 120, .occ 128, .occ 150, .occ 151, .occ 153, .occ 158, .occ 164, .occ 165, .occ 177, .occ 199, .occ 201, .occ 211, .occ 214, .occ 235, .occ 242, .occ 244, .occ 257, .occ 260, .occ 275, .occ 278, .occ 281, .occ 284, .occ 288, .sumGe, .nonneg 0, .nonneg 7, .nonneg 8, .nonneg 11, .nonneg 13, .nonneg 20, .nonneg 26, .nonneg 53, .branchLe 3 (0), .branchLe 34 (1), .branchGe 28 (1), .branchLe 43 (0), .branchGe 2 (1)]

def plane462GenLeaf0002Mult : Fin 63 → Nat := ![579576, 159576, 163436, 877649, 339726, 494698, 5723, 53397, 80268, 674689, 122322, 526359, 418138, 234274, 90958, 437210, 188396, 289182, 200804, 370670, 372918, 39301, 39332, 60703, 483457, 139832, 37402, 251018, 95981, 111586, 33308, 295912, 260773, 325990, 249557, 271836, 20388, 171715, 22620, 55928, 229527, 228123, 236248, 35869, 221803, 281672, 104697, 222768, 49715, 1929672, 342562, 2146510, 2082786, 176988, 127868, 536604, 154164, 487120, 1929672, 1665680, 1625312, 912096, 2353448]

theorem plane462GenLeaf0002 (x : Fin 62 → Int)
    (hroot : plane462GenOccSys.RootHolds x)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (1 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane462GenLeaf0002Refs i).resolveCoeff plane462GenOccSys j)
    (fun i => (plane462GenLeaf0002Refs i).resolveRhs plane462GenOccSys) plane462GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane462GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 5
  · exact hroot.hOcc 8
  · exact hroot.hOcc 14
  · exact hroot.hOcc 26
  · exact hroot.hOcc 71
  · exact hroot.hOcc 74
  · exact hroot.hOcc 77
  · exact hroot.hOcc 78
  · exact hroot.hOcc 81
  · exact hroot.hOcc 82
  · exact hroot.hOcc 85
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 91
  · exact hroot.hOcc 92
  · exact hroot.hOcc 97
  · exact hroot.hOcc 99
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 109
  · exact hroot.hOcc 113
  · exact hroot.hOcc 115
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 128
  · exact hroot.hOcc 150
  · exact hroot.hOcc 151
  · exact hroot.hOcc 153
  · exact hroot.hOcc 158
  · exact hroot.hOcc 164
  · exact hroot.hOcc 165
  · exact hroot.hOcc 177
  · exact hroot.hOcc 199
  · exact hroot.hOcc 201
  · exact hroot.hOcc 211
  · exact hroot.hOcc 214
  · exact hroot.hOcc 235
  · exact hroot.hOcc 242
  · exact hroot.hOcc 244
  · exact hroot.hOcc 257
  · exact hroot.hOcc 260
  · exact hroot.hOcc 275
  · exact hroot.hOcc 278
  · exact hroot.hOcc 281
  · exact hroot.hOcc 284
  · exact hroot.hOcc 288
  · change (∑ j, (-1 : Int) * x j) ≤ -plane462GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (11 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (13 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (20 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (26 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (53 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (3 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (34 : Fin 62) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (28 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (43 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (2 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
