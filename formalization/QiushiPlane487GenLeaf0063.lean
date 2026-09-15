import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0063Refs : Fin 48 → RowRef 668 48 := ![.occ 79, .occ 90, .occ 99, .occ 123, .occ 156, .occ 157, .occ 159, .occ 164, .occ 167, .occ 219, .occ 225, .occ 253, .occ 262, .occ 281, .occ 296, .occ 303, .occ 306, .occ 308, .occ 315, .occ 335, .occ 340, .occ 343, .occ 381, .occ 386, .occ 390, .occ 471, .occ 481, .occ 485, .occ 491, .occ 509, .occ 511, .occ 526, .occ 588, .occ 595, .occ 650, .occ 661, .occ 664, .occ 665, .sumGe, .nonneg 0, .branchGe 39 (1), .branchLe 7 (0), .branchLe 28 (0), .branchLe 40 (0), .branchLe 29 (0), .branchLe 19 (0), .branchGe 36 (1), .branchGe 37 (1)]

def plane487GenLeaf0063Mult : Fin 48 → Nat := ![13533, 8706, 7989, 627, 8689, 6933, 11561, 584, 7308, 44, 10230, 9311, 61, 682, 9895, 10299, 3083, 3956, 3436, 5605, 15884, 14437, 545, 3761, 11023, 1556, 5039, 2582, 3990, 5561, 2716, 5545, 4759, 501, 10795, 2522, 2529, 2522, 33906, 2357, 24119, 6998, 25101, 11002, 31377, 27948, 102054, 34865]

theorem plane487GenLeaf0063 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0063Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0063Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0063Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0063Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 79
  · exact hroot.hOcc 90
  · exact hroot.hOcc 99
  · exact hroot.hOcc 123
  · exact hroot.hOcc 156
  · exact hroot.hOcc 157
  · exact hroot.hOcc 159
  · exact hroot.hOcc 164
  · exact hroot.hOcc 167
  · exact hroot.hOcc 219
  · exact hroot.hOcc 225
  · exact hroot.hOcc 253
  · exact hroot.hOcc 262
  · exact hroot.hOcc 281
  · exact hroot.hOcc 296
  · exact hroot.hOcc 303
  · exact hroot.hOcc 306
  · exact hroot.hOcc 308
  · exact hroot.hOcc 315
  · exact hroot.hOcc 335
  · exact hroot.hOcc 340
  · exact hroot.hOcc 343
  · exact hroot.hOcc 381
  · exact hroot.hOcc 386
  · exact hroot.hOcc 390
  · exact hroot.hOcc 471
  · exact hroot.hOcc 481
  · exact hroot.hOcc 485
  · exact hroot.hOcc 491
  · exact hroot.hOcc 509
  · exact hroot.hOcc 511
  · exact hroot.hOcc 526
  · exact hroot.hOcc 588
  · exact hroot.hOcc 595
  · exact hroot.hOcc 650
  · exact hroot.hOcc 661
  · exact hroot.hOcc 664
  · exact hroot.hOcc 665
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (28 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (29 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (19 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (36 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (37 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37

end QiushiMatmul
