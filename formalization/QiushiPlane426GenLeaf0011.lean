import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0011Refs : Fin 59 → RowRef 340 58 := ![.occ 5, .occ 8, .occ 11, .occ 13, .occ 62, .occ 71, .occ 81, .occ 82, .occ 99, .occ 104, .occ 116, .occ 117, .occ 124, .occ 125, .occ 126, .occ 130, .occ 134, .occ 160, .occ 189, .occ 205, .occ 208, .occ 211, .occ 221, .occ 242, .occ 270, .occ 279, .occ 288, .occ 290, .occ 294, .occ 296, .occ 302, .occ 310, .occ 312, .occ 318, .occ 321, .occ 322, .occ 323, .occ 327, .occ 328, .occ 333, .occ 334, .occ 335, .sumGe, .nonneg 16, .nonneg 17, .nonneg 19, .nonneg 24, .nonneg 28, .nonneg 33, .nonneg 38, .nonneg 40, .nonneg 47, .branchLe 43 (0), .branchLe 14 (0), .branchGe 1 (1), .branchLe 35 (0), .branchGe 4 (1), .branchLe 29 (0), .branchLe 20 (0)]

def plane426GenLeaf0011Mult : Fin 59 → Nat := ![11676, 16290, 1106, 4042, 4056, 9512, 2116, 8664, 18748, 15932, 32464, 6736, 984, 10604, 20944, 8544, 4340, 13892, 750, 12826, 714, 21830, 554, 1464, 2288, 9048, 6302, 2038, 2540, 1284, 6354, 4142, 10322, 4750, 16798, 12880, 18542, 8379, 15011, 26850, 14763, 11677, 98390, 69992, 89456, 48988, 2880, 46040, 1288, 21868, 21148, 3048, 26780, 76394, 7212, 25488, 91310, 61384, 98390]

theorem plane426GenLeaf0011 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0011Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0011Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0011Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0011Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 8
  · exact hroot.hOcc 11
  · exact hroot.hOcc 13
  · exact hroot.hOcc 62
  · exact hroot.hOcc 71
  · exact hroot.hOcc 81
  · exact hroot.hOcc 82
  · exact hroot.hOcc 99
  · exact hroot.hOcc 104
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 130
  · exact hroot.hOcc 134
  · exact hroot.hOcc 160
  · exact hroot.hOcc 189
  · exact hroot.hOcc 205
  · exact hroot.hOcc 208
  · exact hroot.hOcc 211
  · exact hroot.hOcc 221
  · exact hroot.hOcc 242
  · exact hroot.hOcc 270
  · exact hroot.hOcc 279
  · exact hroot.hOcc 288
  · exact hroot.hOcc 290
  · exact hroot.hOcc 294
  · exact hroot.hOcc 296
  · exact hroot.hOcc 302
  · exact hroot.hOcc 310
  · exact hroot.hOcc 312
  · exact hroot.hOcc 318
  · exact hroot.hOcc 321
  · exact hroot.hOcc 322
  · exact hroot.hOcc 323
  · exact hroot.hOcc 327
  · exact hroot.hOcc 328
  · exact hroot.hOcc 333
  · exact hroot.hOcc 334
  · exact hroot.hOcc 335
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (24 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (28 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (33 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (38 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (40 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (47 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (35 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (4 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (29 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (20 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20

end QiushiMatmul
