import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0027Refs : Fin 49 → RowRef 668 48 := ![.occ 82, .occ 83, .occ 100, .occ 111, .occ 119, .occ 143, .occ 145, .occ 239, .occ 240, .occ 241, .occ 242, .occ 275, .occ 294, .occ 296, .occ 301, .occ 312, .occ 313, .occ 315, .occ 343, .occ 353, .occ 370, .occ 380, .occ 385, .occ 386, .occ 399, .occ 444, .occ 446, .occ 468, .occ 471, .occ 531, .occ 560, .occ 563, .occ 584, .occ 600, .occ 639, .occ 648, .occ 664, .sumGe, .nonneg 8, .nonneg 30, .nonneg 45, .branchLe 39 (0), .branchLe 23 (0), .branchGe 6 (1), .branchLe 33 (0), .branchLe 14 (0), .branchGe 29 (1), .branchLe 3 (0), .branchGe 12 (1)]

def plane487GenLeaf0027Mult : Fin 49 → Nat := ![17581, 2533, 27750, 22530, 15220, 1450, 22230, 18159, 17101, 3193, 4238, 1577, 19113, 14389, 76, 18386, 17739, 5145, 17475, 17585, 4291, 3120, 1493, 14970, 5561, 17062, 4330, 2870, 5145, 7249, 6214, 2856, 7449, 3504, 7507, 12918, 2946, 53350, 581, 877, 10232, 30073, 25276, 68439, 15014, 42339, 126763, 42897, 91630]

theorem plane487GenLeaf0027 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0027Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0027Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0027Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0027Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 100
  · exact hroot.hOcc 111
  · exact hroot.hOcc 119
  · exact hroot.hOcc 143
  · exact hroot.hOcc 145
  · exact hroot.hOcc 239
  · exact hroot.hOcc 240
  · exact hroot.hOcc 241
  · exact hroot.hOcc 242
  · exact hroot.hOcc 275
  · exact hroot.hOcc 294
  · exact hroot.hOcc 296
  · exact hroot.hOcc 301
  · exact hroot.hOcc 312
  · exact hroot.hOcc 313
  · exact hroot.hOcc 315
  · exact hroot.hOcc 343
  · exact hroot.hOcc 353
  · exact hroot.hOcc 370
  · exact hroot.hOcc 380
  · exact hroot.hOcc 385
  · exact hroot.hOcc 386
  · exact hroot.hOcc 399
  · exact hroot.hOcc 444
  · exact hroot.hOcc 446
  · exact hroot.hOcc 468
  · exact hroot.hOcc 471
  · exact hroot.hOcc 531
  · exact hroot.hOcc 560
  · exact hroot.hOcc 563
  · exact hroot.hOcc 584
  · exact hroot.hOcc 600
  · exact hroot.hOcc 639
  · exact hroot.hOcc 648
  · exact hroot.hOcc 664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (30 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (45 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (33 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (14 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (29 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (3 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (12 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
