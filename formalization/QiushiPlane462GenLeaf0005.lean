import QiushiPlane462GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane462GenLeaf0005Refs : Fin 63 → RowRef 294 62 := ![.occ 11, .occ 15, .occ 17, .occ 19, .occ 21, .occ 28, .occ 37, .occ 47, .occ 62, .occ 67, .occ 68, .occ 74, .occ 76, .occ 78, .occ 80, .occ 81, .occ 84, .occ 86, .occ 88, .occ 91, .occ 92, .occ 94, .occ 98, .occ 99, .occ 104, .occ 105, .occ 109, .occ 113, .occ 114, .occ 115, .occ 121, .occ 122, .occ 130, .occ 137, .occ 145, .occ 146, .occ 149, .occ 155, .occ 188, .occ 193, .occ 200, .occ 206, .occ 238, .occ 246, .occ 248, .occ 269, .occ 276, .occ 277, .occ 283, .occ 293, .sumGe, .nonneg 7, .nonneg 8, .nonneg 15, .nonneg 39, .nonneg 47, .nonneg 48, .nonneg 54, .branchLe 5 (0), .branchLe 2 (0), .branchLe 43 (0), .branchLe 4 (0), .branchLe 9 (0)]

def plane462GenLeaf0005Mult : Fin 63 → Nat := ![561470, 327952, 702982, 236236, 1141058, 81342, 837430, 121930, 2270888, 1239724, 481736, 196810, 1033048, 1048458, 1717040, 919986, 479144, 1743404, 1408360, 1270606, 957992, 944612, 210270, 588796, 1417450, 719158, 817612, 1272239, 369060, 455429, 490707, 792789, 70532, 298444, 1108719, 1275786, 854852, 819191, 169301, 333772, 888528, 535561, 102473, 313241, 101080, 641093, 523326, 725344, 936224, 1125513, 6791080, 2028470, 4622644, 1048744, 254672, 1649016, 2146316, 755700, 5491732, 2357038, 830432, 5551356, 6065736]

theorem plane462GenLeaf0005 (x : Fin 62 → Int)
    (hroot : plane462GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane462GenLeaf0005Refs i).resolveCoeff plane462GenOccSys j)
    (fun i => (plane462GenLeaf0005Refs i).resolveRhs plane462GenOccSys) plane462GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane462GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 11
  · exact hroot.hOcc 15
  · exact hroot.hOcc 17
  · exact hroot.hOcc 19
  · exact hroot.hOcc 21
  · exact hroot.hOcc 28
  · exact hroot.hOcc 37
  · exact hroot.hOcc 47
  · exact hroot.hOcc 62
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 74
  · exact hroot.hOcc 76
  · exact hroot.hOcc 78
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 84
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 91
  · exact hroot.hOcc 92
  · exact hroot.hOcc 94
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 109
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 130
  · exact hroot.hOcc 137
  · exact hroot.hOcc 145
  · exact hroot.hOcc 146
  · exact hroot.hOcc 149
  · exact hroot.hOcc 155
  · exact hroot.hOcc 188
  · exact hroot.hOcc 193
  · exact hroot.hOcc 200
  · exact hroot.hOcc 206
  · exact hroot.hOcc 238
  · exact hroot.hOcc 246
  · exact hroot.hOcc 248
  · exact hroot.hOcc 269
  · exact hroot.hOcc 276
  · exact hroot.hOcc 277
  · exact hroot.hOcc 283
  · exact hroot.hOcc 293
  · change (∑ j, (-1 : Int) * x j) ≤ -plane462GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (15 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (39 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (47 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (48 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (54 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (5 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (2 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (43 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (4 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (9 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9

end QiushiMatmul
