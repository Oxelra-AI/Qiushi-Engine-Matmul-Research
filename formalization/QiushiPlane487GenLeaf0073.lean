import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0073Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 100, .occ 136, .occ 211, .occ 216, .occ 217, .occ 219, .occ 223, .occ 224, .occ 228, .occ 230, .occ 246, .occ 260, .occ 275, .occ 288, .occ 303, .occ 305, .occ 306, .occ 313, .occ 315, .occ 319, .occ 320, .occ 325, .occ 332, .occ 378, .occ 385, .occ 386, .occ 394, .occ 401, .occ 472, .occ 479, .occ 482, .occ 484, .occ 487, .occ 505, .occ 509, .occ 650, .occ 664, .occ 667, .sumGe, .nonneg 7, .nonneg 8, .nonneg 18, .branchGe 39 (1), .branchLe 28 (0), .branchGe 40 (1), .branchLe 13 (0), .branchLe 32 (0), .branchLe 33 (0)]

def plane487GenLeaf0073Mult : Fin 49 → Nat := ![81874, 18674, 109879, 184340, 1895, 98903, 4527, 38225, 164112, 46820, 62046, 26692, 9335, 260087, 71246, 39093, 529053, 44049, 129662, 145259, 100625, 155624, 93040, 143091, 111745, 42192, 224884, 174734, 212879, 112942, 71629, 165724, 87833, 125026, 97497, 32928, 94974, 253121, 20733, 741857, 409183, 23588, 89150, 1546931, 199148, 2196478, 670228, 447134, 644360]

theorem plane487GenLeaf0073 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0073Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0073Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0073Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0073Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 100
  · exact hroot.hOcc 136
  · exact hroot.hOcc 211
  · exact hroot.hOcc 216
  · exact hroot.hOcc 217
  · exact hroot.hOcc 219
  · exact hroot.hOcc 223
  · exact hroot.hOcc 224
  · exact hroot.hOcc 228
  · exact hroot.hOcc 230
  · exact hroot.hOcc 246
  · exact hroot.hOcc 260
  · exact hroot.hOcc 275
  · exact hroot.hOcc 288
  · exact hroot.hOcc 303
  · exact hroot.hOcc 305
  · exact hroot.hOcc 306
  · exact hroot.hOcc 313
  · exact hroot.hOcc 315
  · exact hroot.hOcc 319
  · exact hroot.hOcc 320
  · exact hroot.hOcc 325
  · exact hroot.hOcc 332
  · exact hroot.hOcc 378
  · exact hroot.hOcc 385
  · exact hroot.hOcc 386
  · exact hroot.hOcc 394
  · exact hroot.hOcc 401
  · exact hroot.hOcc 472
  · exact hroot.hOcc 479
  · exact hroot.hOcc 482
  · exact hroot.hOcc 484
  · exact hroot.hOcc 487
  · exact hroot.hOcc 505
  · exact hroot.hOcc 509
  · exact hroot.hOcc 650
  · exact hroot.hOcc 664
  · exact hroot.hOcc 667
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (18 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (28 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (40 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40
  · change (∑ k, (if k = (13 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (32 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (33 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33

end QiushiMatmul
