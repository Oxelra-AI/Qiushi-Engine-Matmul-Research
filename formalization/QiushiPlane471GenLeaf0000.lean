import QiushiPlane471GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane471GenLeaf0000Refs : Fin 64 → RowRef 304 63 := ![.occ 6, .occ 9, .occ 21, .occ 31, .occ 34, .occ 35, .occ 36, .occ 37, .occ 46, .occ 49, .occ 50, .occ 56, .occ 57, .occ 58, .occ 61, .occ 82, .occ 83, .occ 85, .occ 93, .occ 95, .occ 109, .occ 114, .occ 118, .occ 119, .occ 120, .occ 124, .occ 127, .occ 133, .occ 136, .occ 138, .occ 139, .occ 154, .occ 159, .occ 184, .occ 193, .occ 195, .occ 201, .occ 212, .occ 242, .occ 244, .occ 247, .occ 249, .occ 271, .occ 275, .occ 282, .occ 284, .occ 287, .occ 288, .occ 290, .occ 291, .occ 295, .occ 301, .sumGe, .nonneg 7, .nonneg 10, .nonneg 21, .nonneg 49, .nonneg 52, .branchLe 48 (0), .branchLe 14 (0), .branchLe 38 (0), .branchLe 12 (0), .branchLe 20 (0), .branchLe 43 (0)]

def plane471GenLeaf0000Mult : Fin 64 → Nat := ![22591316, 575407, 76147203, 103526555, 4615468, 6762156, 36973622, 53713336, 5403710, 22226512, 240945076, 71339199, 70700947, 23010744, 7541609, 137238654, 67518536, 130672255, 67828914, 49978463, 102566385, 3702531, 59713201, 137671533, 36102967, 52586644, 12535180, 6976517, 55074562, 125904215, 75354394, 111186, 12874845, 19101632, 31952762, 18277727, 116613807, 76141344, 35147826, 6734567, 6226508, 39314599, 25233774, 28962220, 41797393, 110087936, 16570144, 109650534, 18240322, 1064243, 64149344, 41545677, 441376182, 56316315, 104296002, 379801738, 227085183, 93049482, 338809797, 351993064, 423741795, 213933670, 310463610, 423741795]

theorem plane471GenLeaf0000 (x : Fin 63 → Int)
    (hroot : plane471GenOccSys.RootHolds x)
    (hUB_48 : x 48 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane471GenLeaf0000Refs i).resolveCoeff plane471GenOccSys j)
    (fun i => (plane471GenLeaf0000Refs i).resolveRhs plane471GenOccSys) plane471GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane471GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 6
  · exact hroot.hOcc 9
  · exact hroot.hOcc 21
  · exact hroot.hOcc 31
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 46
  · exact hroot.hOcc 49
  · exact hroot.hOcc 50
  · exact hroot.hOcc 56
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 61
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 85
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 109
  · exact hroot.hOcc 114
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 124
  · exact hroot.hOcc 127
  · exact hroot.hOcc 133
  · exact hroot.hOcc 136
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 154
  · exact hroot.hOcc 159
  · exact hroot.hOcc 184
  · exact hroot.hOcc 193
  · exact hroot.hOcc 195
  · exact hroot.hOcc 201
  · exact hroot.hOcc 212
  · exact hroot.hOcc 242
  · exact hroot.hOcc 244
  · exact hroot.hOcc 247
  · exact hroot.hOcc 249
  · exact hroot.hOcc 271
  · exact hroot.hOcc 275
  · exact hroot.hOcc 282
  · exact hroot.hOcc 284
  · exact hroot.hOcc 287
  · exact hroot.hOcc 288
  · exact hroot.hOcc 290
  · exact hroot.hOcc 291
  · exact hroot.hOcc 295
  · exact hroot.hOcc 301
  · change (∑ j, (-1 : Int) * x j) ≤ -plane471GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (21 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (52 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (48 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_48
  · change (∑ k, (if k = (14 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (38 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (12 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (20 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (43 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43

end QiushiMatmul
