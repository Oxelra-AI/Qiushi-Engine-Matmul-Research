import QiushiPlane463GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane463GenLeaf0002Refs : Fin 64 → RowRef 278 63 := ![.occ 15, .occ 22, .occ 25, .occ 26, .occ 39, .occ 40, .occ 47, .occ 52, .occ 53, .occ 55, .occ 61, .occ 78, .occ 79, .occ 93, .occ 97, .occ 109, .occ 114, .occ 143, .occ 153, .occ 154, .occ 163, .occ 166, .occ 168, .occ 169, .occ 170, .occ 173, .occ 186, .occ 187, .occ 191, .occ 192, .occ 193, .occ 207, .occ 222, .occ 229, .occ 236, .occ 244, .occ 259, .occ 263, .occ 264, .occ 266, .occ 268, .occ 271, .occ 272, .occ 274, .occ 276, .sumGe, .nonneg 0, .nonneg 7, .nonneg 10, .nonneg 14, .nonneg 40, .nonneg 42, .nonneg 44, .nonneg 49, .nonneg 54, .branchLe 15 (0), .branchLe 24 (0), .branchLe 60 (0), .branchLe 21 (0), .branchLe 19 (0), .branchLe 47 (0), .branchLe 22 (0), .branchLe 20 (0), .branchGe 2 (1)]

def plane463GenLeaf0002Mult : Fin 64 → Nat := ![40368, 63192, 165856, 10400, 81976, 526864, 110304, 45960, 232808, 21528, 289704, 56368, 793124, 203472, 347992, 355544, 39872, 155760, 180272, 295368, 13196, 95934, 239686, 48640, 206570, 48166, 182038, 241030, 200904, 142344, 55676, 293148, 54216, 89808, 2508, 5296, 399416, 142329, 117736, 43637, 42035, 74111, 53348, 214872, 239356, 1334580, 2090208, 591920, 1157032, 10592, 64320, 402656, 233400, 372936, 465400, 615272, 1021152, 678560, 899984, 808736, 1095224, 888832, 808736, 1600200]

theorem plane463GenLeaf0002 (x : Fin 63 → Int)
    (hroot : plane463GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_60 : x 60 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_47 : x 47 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane463GenLeaf0002Refs i).resolveCoeff plane463GenOccSys j)
    (fun i => (plane463GenLeaf0002Refs i).resolveRhs plane463GenOccSys) plane463GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane463GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 15
  · exact hroot.hOcc 22
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 39
  · exact hroot.hOcc 40
  · exact hroot.hOcc 47
  · exact hroot.hOcc 52
  · exact hroot.hOcc 53
  · exact hroot.hOcc 55
  · exact hroot.hOcc 61
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 93
  · exact hroot.hOcc 97
  · exact hroot.hOcc 109
  · exact hroot.hOcc 114
  · exact hroot.hOcc 143
  · exact hroot.hOcc 153
  · exact hroot.hOcc 154
  · exact hroot.hOcc 163
  · exact hroot.hOcc 166
  · exact hroot.hOcc 168
  · exact hroot.hOcc 169
  · exact hroot.hOcc 170
  · exact hroot.hOcc 173
  · exact hroot.hOcc 186
  · exact hroot.hOcc 187
  · exact hroot.hOcc 191
  · exact hroot.hOcc 192
  · exact hroot.hOcc 193
  · exact hroot.hOcc 207
  · exact hroot.hOcc 222
  · exact hroot.hOcc 229
  · exact hroot.hOcc 236
  · exact hroot.hOcc 244
  · exact hroot.hOcc 259
  · exact hroot.hOcc 263
  · exact hroot.hOcc 264
  · exact hroot.hOcc 266
  · exact hroot.hOcc 268
  · exact hroot.hOcc 271
  · exact hroot.hOcc 272
  · exact hroot.hOcc 274
  · exact hroot.hOcc 276
  · change (∑ j, (-1 : Int) * x j) ≤ -plane463GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (14 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (40 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (42 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (54 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (15 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (24 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (60 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_60
  · change (∑ k, (if k = (21 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (19 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (47 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_47
  · change (∑ k, (if k = (22 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (20 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (2 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
