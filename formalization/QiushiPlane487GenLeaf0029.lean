import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0029Refs : Fin 49 → RowRef 668 48 := ![.occ 82, .occ 101, .occ 104, .occ 111, .occ 120, .occ 123, .occ 131, .occ 186, .occ 216, .occ 218, .occ 219, .occ 220, .occ 224, .occ 240, .occ 269, .occ 294, .occ 295, .occ 302, .occ 303, .occ 308, .occ 333, .occ 339, .occ 342, .occ 352, .occ 380, .occ 392, .occ 471, .occ 472, .occ 521, .occ 523, .occ 528, .occ 531, .occ 542, .occ 553, .occ 571, .occ 584, .occ 632, .occ 639, .occ 648, .occ 665, .sumGe, .nonneg 0, .nonneg 17, .branchLe 39 (0), .branchLe 23 (0), .branchGe 6 (1), .branchLe 33 (0), .branchGe 14 (1), .branchLe 24 (0)]

def plane487GenLeaf0029Mult : Fin 49 → Nat := ![113146, 87256, 205129, 62156, 71231, 43482, 96695, 95067, 20065, 293152, 209266, 27747, 139450, 11034, 69664, 5469, 227828, 88232, 155104, 10870, 61444, 58880, 5401, 116608, 154442, 103483, 121309, 40528, 49351, 6194, 14224, 39674, 18141, 108022, 881, 31237, 11280, 18716, 99776, 70284, 471383, 62121, 112599, 360571, 470502, 1378426, 333461, 940283, 452667]

theorem plane487GenLeaf0029 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0029Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0029Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0029Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0029Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 101
  · exact hroot.hOcc 104
  · exact hroot.hOcc 111
  · exact hroot.hOcc 120
  · exact hroot.hOcc 123
  · exact hroot.hOcc 131
  · exact hroot.hOcc 186
  · exact hroot.hOcc 216
  · exact hroot.hOcc 218
  · exact hroot.hOcc 219
  · exact hroot.hOcc 220
  · exact hroot.hOcc 224
  · exact hroot.hOcc 240
  · exact hroot.hOcc 269
  · exact hroot.hOcc 294
  · exact hroot.hOcc 295
  · exact hroot.hOcc 302
  · exact hroot.hOcc 303
  · exact hroot.hOcc 308
  · exact hroot.hOcc 333
  · exact hroot.hOcc 339
  · exact hroot.hOcc 342
  · exact hroot.hOcc 352
  · exact hroot.hOcc 380
  · exact hroot.hOcc 392
  · exact hroot.hOcc 471
  · exact hroot.hOcc 472
  · exact hroot.hOcc 521
  · exact hroot.hOcc 523
  · exact hroot.hOcc 528
  · exact hroot.hOcc 531
  · exact hroot.hOcc 542
  · exact hroot.hOcc 553
  · exact hroot.hOcc 571
  · exact hroot.hOcc 584
  · exact hroot.hOcc 632
  · exact hroot.hOcc 639
  · exact hroot.hOcc 648
  · exact hroot.hOcc 665
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (17 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (33 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (14 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (24 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24

end QiushiMatmul
