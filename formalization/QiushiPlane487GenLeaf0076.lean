import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0076Refs : Fin 47 → RowRef 668 48 := ![.occ 83, .occ 94, .occ 101, .occ 122, .occ 123, .occ 160, .occ 162, .occ 172, .occ 208, .occ 217, .occ 233, .occ 241, .occ 264, .occ 272, .occ 278, .occ 289, .occ 297, .occ 303, .occ 305, .occ 313, .occ 315, .occ 325, .occ 332, .occ 343, .occ 348, .occ 366, .occ 378, .occ 379, .occ 380, .occ 385, .occ 399, .occ 422, .occ 472, .occ 479, .occ 482, .occ 505, .occ 618, .occ 653, .occ 659, .occ 664, .sumGe, .nonneg 8, .nonneg 36, .branchGe 39 (1), .branchLe 7 (0), .branchGe 40 (1), .branchGe 13 (1)]

def plane487GenLeaf0076Mult : Fin 47 → Nat := ![66, 443, 291, 609, 1213, 169, 584, 156, 21, 211, 66, 862, 108, 654, 614, 227, 39, 953, 178, 953, 145, 32, 994, 145, 211, 1352, 1024, 190, 1806, 804, 145, 705, 348, 1217, 485, 311, 66, 887, 716, 174, 2800, 30, 145, 5102, 602, 11310, 8534]

theorem plane487GenLeaf0076 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0076Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0076Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0076Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0076Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 94
  · exact hroot.hOcc 101
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 160
  · exact hroot.hOcc 162
  · exact hroot.hOcc 172
  · exact hroot.hOcc 208
  · exact hroot.hOcc 217
  · exact hroot.hOcc 233
  · exact hroot.hOcc 241
  · exact hroot.hOcc 264
  · exact hroot.hOcc 272
  · exact hroot.hOcc 278
  · exact hroot.hOcc 289
  · exact hroot.hOcc 297
  · exact hroot.hOcc 303
  · exact hroot.hOcc 305
  · exact hroot.hOcc 313
  · exact hroot.hOcc 315
  · exact hroot.hOcc 325
  · exact hroot.hOcc 332
  · exact hroot.hOcc 343
  · exact hroot.hOcc 348
  · exact hroot.hOcc 366
  · exact hroot.hOcc 378
  · exact hroot.hOcc 379
  · exact hroot.hOcc 380
  · exact hroot.hOcc 385
  · exact hroot.hOcc 399
  · exact hroot.hOcc 422
  · exact hroot.hOcc 472
  · exact hroot.hOcc 479
  · exact hroot.hOcc 482
  · exact hroot.hOcc 505
  · exact hroot.hOcc 618
  · exact hroot.hOcc 653
  · exact hroot.hOcc 659
  · exact hroot.hOcc 664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (36 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (40 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40
  · change (∑ k, (if k = (13 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
