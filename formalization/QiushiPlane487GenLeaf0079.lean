import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0079Refs : Fin 49 → RowRef 668 48 := ![.occ 105, .occ 147, .occ 157, .occ 174, .occ 177, .occ 194, .occ 200, .occ 217, .occ 225, .occ 227, .occ 230, .occ 237, .occ 239, .occ 260, .occ 263, .occ 269, .occ 284, .occ 302, .occ 305, .occ 315, .occ 332, .occ 333, .occ 350, .occ 377, .occ 378, .occ 386, .occ 401, .occ 482, .occ 497, .occ 531, .occ 544, .occ 654, .occ 655, .occ 656, .occ 660, .occ 662, .occ 665, .sumGe, .nonneg 8, .nonneg 31, .branchGe 39 (1), .branchLe 7 (0), .branchGe 28 (1), .branchLe 3 (0), .branchLe 36 (0), .branchLe 35 (0), .branchLe 13 (0), .branchGe 37 (1), .branchLe 9 (0)]

def plane487GenLeaf0079Mult : Fin 49 → Nat := ![70560, 44703, 1772, 339, 58930, 6943, 24204, 13139, 13800, 13228, 2972, 14586, 14569, 2087, 18599, 19317, 32849, 5572, 29686, 33665, 21700, 15066, 21, 24878, 14907, 14800, 28570, 15504, 3356, 1092, 5067, 1805, 7489, 2918, 28114, 20663, 13063, 98423, 40005, 2798, 78255, 22839, 314485, 75673, 90934, 59005, 47815, 24809, 85360]

theorem plane487GenLeaf0079 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0079Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0079Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0079Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0079Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 105
  · exact hroot.hOcc 147
  · exact hroot.hOcc 157
  · exact hroot.hOcc 174
  · exact hroot.hOcc 177
  · exact hroot.hOcc 194
  · exact hroot.hOcc 200
  · exact hroot.hOcc 217
  · exact hroot.hOcc 225
  · exact hroot.hOcc 227
  · exact hroot.hOcc 230
  · exact hroot.hOcc 237
  · exact hroot.hOcc 239
  · exact hroot.hOcc 260
  · exact hroot.hOcc 263
  · exact hroot.hOcc 269
  · exact hroot.hOcc 284
  · exact hroot.hOcc 302
  · exact hroot.hOcc 305
  · exact hroot.hOcc 315
  · exact hroot.hOcc 332
  · exact hroot.hOcc 333
  · exact hroot.hOcc 350
  · exact hroot.hOcc 377
  · exact hroot.hOcc 378
  · exact hroot.hOcc 386
  · exact hroot.hOcc 401
  · exact hroot.hOcc 482
  · exact hroot.hOcc 497
  · exact hroot.hOcc 531
  · exact hroot.hOcc 544
  · exact hroot.hOcc 654
  · exact hroot.hOcc 655
  · exact hroot.hOcc 656
  · exact hroot.hOcc 660
  · exact hroot.hOcc 662
  · exact hroot.hOcc 665
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (31 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (28 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (3 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (36 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (35 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (13 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (37 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (9 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9

end QiushiMatmul
