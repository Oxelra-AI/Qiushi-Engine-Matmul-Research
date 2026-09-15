import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0039Refs : Fin 49 → RowRef 668 48 := ![.occ 82, .occ 102, .occ 106, .occ 137, .occ 139, .occ 195, .occ 216, .occ 218, .occ 230, .occ 237, .occ 241, .occ 275, .occ 294, .occ 298, .occ 303, .occ 315, .occ 326, .occ 335, .occ 337, .occ 340, .occ 378, .occ 379, .occ 386, .occ 399, .occ 454, .occ 477, .occ 523, .occ 524, .occ 526, .occ 530, .occ 531, .occ 563, .occ 565, .occ 601, .occ 604, .occ 606, .occ 623, .occ 639, .occ 666, .sumGe, .nonneg 0, .nonneg 7, .nonneg 30, .nonneg 44, .branchLe 39 (0), .branchGe 23 (1), .branchLe 2 (0), .branchLe 4 (0), .branchLe 46 (0)]

def plane487GenLeaf0039Mult : Fin 49 → Nat := ![214703, 60187, 13955, 102044, 222432, 541555, 196777, 28163, 72729, 249684, 305526, 200091, 109772, 124987, 85960, 417321, 260947, 385179, 3547, 61064, 102581, 203931, 266167, 3335, 58671, 198006, 97068, 1867, 82507, 18742, 22948, 31798, 100114, 36138, 4976, 42670, 14439, 47837, 223190, 839155, 42322, 27555, 32221, 10263, 724850, 2933824, 810992, 568128, 705358]

theorem plane487GenLeaf0039 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0039Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0039Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0039Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0039Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 102
  · exact hroot.hOcc 106
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 195
  · exact hroot.hOcc 216
  · exact hroot.hOcc 218
  · exact hroot.hOcc 230
  · exact hroot.hOcc 237
  · exact hroot.hOcc 241
  · exact hroot.hOcc 275
  · exact hroot.hOcc 294
  · exact hroot.hOcc 298
  · exact hroot.hOcc 303
  · exact hroot.hOcc 315
  · exact hroot.hOcc 326
  · exact hroot.hOcc 335
  · exact hroot.hOcc 337
  · exact hroot.hOcc 340
  · exact hroot.hOcc 378
  · exact hroot.hOcc 379
  · exact hroot.hOcc 386
  · exact hroot.hOcc 399
  · exact hroot.hOcc 454
  · exact hroot.hOcc 477
  · exact hroot.hOcc 523
  · exact hroot.hOcc 524
  · exact hroot.hOcc 526
  · exact hroot.hOcc 530
  · exact hroot.hOcc 531
  · exact hroot.hOcc 563
  · exact hroot.hOcc 565
  · exact hroot.hOcc 601
  · exact hroot.hOcc 604
  · exact hroot.hOcc 606
  · exact hroot.hOcc 623
  · exact hroot.hOcc 639
  · exact hroot.hOcc 666
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (30 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (44 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (2 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (4 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (46 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46

end QiushiMatmul
