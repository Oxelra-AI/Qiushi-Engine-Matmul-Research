import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0024Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 86, .occ 95, .occ 110, .occ 120, .occ 138, .occ 173, .occ 186, .occ 194, .occ 230, .occ 259, .occ 293, .occ 294, .occ 295, .occ 303, .occ 313, .occ 329, .occ 334, .occ 340, .occ 348, .occ 378, .occ 381, .occ 386, .occ 391, .occ 399, .occ 402, .occ 410, .occ 432, .occ 461, .occ 462, .occ 478, .occ 521, .occ 551, .occ 566, .occ 615, .occ 648, .occ 650, .occ 666, .sumGe, .nonneg 31, .branchLe 39 (0), .branchLe 23 (0), .branchGe 6 (1), .branchLe 33 (0), .branchLe 14 (0), .branchLe 29 (0), .branchGe 9 (1), .branchLe 44 (0), .branchGe 25 (1)]

def plane487GenLeaf0024Mult : Fin 49 → Nat := ![25514, 6095, 2229, 30519, 352, 15861, 852, 41869, 59838, 17507, 19136, 1456, 8434, 17704, 27131, 5390, 14045, 364, 9470, 7830, 16935, 10337, 22274, 19165, 23584, 5707, 1794, 3589, 9365, 26083, 14924, 7995, 5469, 5475, 18164, 12593, 1432, 4043, 75319, 3441, 73887, 71276, 207074, 23298, 21057, 27960, 24981, 53572, 151000]

theorem plane487GenLeaf0024 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0024Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0024Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0024Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0024Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 86
  · exact hroot.hOcc 95
  · exact hroot.hOcc 110
  · exact hroot.hOcc 120
  · exact hroot.hOcc 138
  · exact hroot.hOcc 173
  · exact hroot.hOcc 186
  · exact hroot.hOcc 194
  · exact hroot.hOcc 230
  · exact hroot.hOcc 259
  · exact hroot.hOcc 293
  · exact hroot.hOcc 294
  · exact hroot.hOcc 295
  · exact hroot.hOcc 303
  · exact hroot.hOcc 313
  · exact hroot.hOcc 329
  · exact hroot.hOcc 334
  · exact hroot.hOcc 340
  · exact hroot.hOcc 348
  · exact hroot.hOcc 378
  · exact hroot.hOcc 381
  · exact hroot.hOcc 386
  · exact hroot.hOcc 391
  · exact hroot.hOcc 399
  · exact hroot.hOcc 402
  · exact hroot.hOcc 410
  · exact hroot.hOcc 432
  · exact hroot.hOcc 461
  · exact hroot.hOcc 462
  · exact hroot.hOcc 478
  · exact hroot.hOcc 521
  · exact hroot.hOcc 551
  · exact hroot.hOcc 566
  · exact hroot.hOcc 615
  · exact hroot.hOcc 648
  · exact hroot.hOcc 650
  · exact hroot.hOcc 666
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (33 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (14 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (29 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (9 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (44 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (25 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25

end QiushiMatmul
