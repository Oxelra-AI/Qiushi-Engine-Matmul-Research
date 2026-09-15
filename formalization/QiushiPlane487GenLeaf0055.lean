import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0055Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 92, .occ 95, .occ 102, .occ 106, .occ 123, .occ 155, .occ 162, .occ 196, .occ 197, .occ 211, .occ 219, .occ 225, .occ 246, .occ 256, .occ 267, .occ 295, .occ 297, .occ 302, .occ 313, .occ 322, .occ 334, .occ 391, .occ 399, .occ 401, .occ 407, .occ 466, .occ 470, .occ 498, .occ 543, .occ 595, .occ 598, .occ 618, .occ 645, .occ 650, .occ 656, .occ 661, .occ 662, .sumGe, .branchGe 39 (1), .branchLe 7 (0), .branchLe 28 (0), .branchLe 40 (0), .branchLe 29 (0), .branchLe 19 (0), .branchLe 36 (0), .branchLe 23 (0), .branchGe 45 (1), .branchLe 10 (0)]

def plane487GenLeaf0055Mult : Fin 49 → Nat := ![24906, 15756, 35012, 118534, 80396, 9526, 6784, 10934, 127265, 69847, 29448, 14410, 26674, 54157, 21218, 17659, 83049, 70662, 18462, 23301, 59004, 3880, 12950, 7220, 374, 6669, 18009, 19199, 27542, 11237, 20673, 667, 6114, 12965, 40514, 54928, 39844, 14379, 196946, 182526, 48017, 142056, 166864, 67320, 182567, 130013, 183981, 401820, 196946]

theorem plane487GenLeaf0055 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_45 : (1 : Int) ≤ x 45)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0055Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0055Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0055Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0055Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 92
  · exact hroot.hOcc 95
  · exact hroot.hOcc 102
  · exact hroot.hOcc 106
  · exact hroot.hOcc 123
  · exact hroot.hOcc 155
  · exact hroot.hOcc 162
  · exact hroot.hOcc 196
  · exact hroot.hOcc 197
  · exact hroot.hOcc 211
  · exact hroot.hOcc 219
  · exact hroot.hOcc 225
  · exact hroot.hOcc 246
  · exact hroot.hOcc 256
  · exact hroot.hOcc 267
  · exact hroot.hOcc 295
  · exact hroot.hOcc 297
  · exact hroot.hOcc 302
  · exact hroot.hOcc 313
  · exact hroot.hOcc 322
  · exact hroot.hOcc 334
  · exact hroot.hOcc 391
  · exact hroot.hOcc 399
  · exact hroot.hOcc 401
  · exact hroot.hOcc 407
  · exact hroot.hOcc 466
  · exact hroot.hOcc 470
  · exact hroot.hOcc 498
  · exact hroot.hOcc 543
  · exact hroot.hOcc 595
  · exact hroot.hOcc 598
  · exact hroot.hOcc 618
  · exact hroot.hOcc 645
  · exact hroot.hOcc 650
  · exact hroot.hOcc 656
  · exact hroot.hOcc 661
  · exact hroot.hOcc 662
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (28 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (29 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (19 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (36 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (45 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_45
  · change (∑ k, (if k = (10 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
