import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0051Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 87, .occ 92, .occ 100, .occ 162, .occ 165, .occ 194, .occ 201, .occ 211, .occ 224, .occ 227, .occ 230, .occ 246, .occ 259, .occ 260, .occ 269, .occ 285, .occ 294, .occ 315, .occ 334, .occ 336, .occ 381, .occ 386, .occ 401, .occ 410, .occ 414, .occ 457, .occ 498, .occ 509, .occ 618, .occ 645, .occ 649, .occ 650, .occ 656, .occ 657, .occ 661, .occ 665, .sumGe, .branchGe 39 (1), .branchLe 7 (0), .branchLe 28 (0), .branchLe 40 (0), .branchLe 29 (0), .branchLe 19 (0), .branchLe 36 (0), .branchLe 23 (0), .branchLe 45 (0), .branchLe 5 (0), .branchGe 25 (1)]

def plane487GenLeaf0051Mult : Fin 49 → Nat := ![239884, 237385, 368031, 147198, 230732, 3737, 47459, 252336, 117261, 12459, 10638, 142536, 15165, 90186, 215596, 5760, 5864, 19221, 43202, 57787, 8498, 62126, 49191, 186478, 192170, 121581, 105029, 99549, 30763, 40873, 47563, 27636, 191849, 160853, 47450, 170309, 30375, 647582, 1109081, 69440, 364311, 557518, 472834, 494960, 424970, 509367, 433468, 389570, 1079367]

theorem plane487GenLeaf0051 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_45 : x 45 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0051Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0051Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0051Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0051Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 87
  · exact hroot.hOcc 92
  · exact hroot.hOcc 100
  · exact hroot.hOcc 162
  · exact hroot.hOcc 165
  · exact hroot.hOcc 194
  · exact hroot.hOcc 201
  · exact hroot.hOcc 211
  · exact hroot.hOcc 224
  · exact hroot.hOcc 227
  · exact hroot.hOcc 230
  · exact hroot.hOcc 246
  · exact hroot.hOcc 259
  · exact hroot.hOcc 260
  · exact hroot.hOcc 269
  · exact hroot.hOcc 285
  · exact hroot.hOcc 294
  · exact hroot.hOcc 315
  · exact hroot.hOcc 334
  · exact hroot.hOcc 336
  · exact hroot.hOcc 381
  · exact hroot.hOcc 386
  · exact hroot.hOcc 401
  · exact hroot.hOcc 410
  · exact hroot.hOcc 414
  · exact hroot.hOcc 457
  · exact hroot.hOcc 498
  · exact hroot.hOcc 509
  · exact hroot.hOcc 618
  · exact hroot.hOcc 645
  · exact hroot.hOcc 649
  · exact hroot.hOcc 650
  · exact hroot.hOcc 656
  · exact hroot.hOcc 657
  · exact hroot.hOcc 661
  · exact hroot.hOcc 665
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (28 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (29 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (19 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (36 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (45 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_45
  · change (∑ k, (if k = (5 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (25 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25

end QiushiMatmul
