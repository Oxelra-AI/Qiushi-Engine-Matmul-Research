import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0016Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 104, .occ 105, .occ 138, .occ 168, .occ 200, .occ 218, .occ 223, .occ 225, .occ 233, .occ 235, .occ 269, .occ 290, .occ 303, .occ 315, .occ 340, .occ 356, .occ 374, .occ 377, .occ 385, .occ 386, .occ 399, .occ 450, .occ 453, .occ 513, .occ 514, .occ 515, .occ 521, .occ 525, .occ 536, .occ 541, .occ 566, .occ 573, .occ 606, .occ 649, .occ 651, .occ 654, .occ 656, .occ 665, .occ 666, .sumGe, .nonneg 33, .nonneg 36, .branchLe 39 (0), .branchLe 23 (0), .branchLe 6 (0), .branchGe 25 (1), .branchLe 1 (0), .branchLe 35 (0)]

def plane487GenLeaf0016Mult : Fin 49 → Nat := ![721870, 634916, 297799, 618335, 379710, 245552, 22286, 70737, 447356, 590793, 343267, 131003, 54296, 251918, 479975, 443622, 210770, 252108, 523306, 278178, 270243, 736437, 109866, 61065, 157493, 7443, 118125, 333257, 86231, 27730, 193700, 234821, 231986, 125577, 19306, 43846, 247161, 74261, 90483, 321614, 1788276, 88911, 109978, 1402869, 293650, 1656201, 4244256, 1717539, 1443772]

theorem plane487GenLeaf0016 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0016Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0016Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0016Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0016Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 138
  · exact hroot.hOcc 168
  · exact hroot.hOcc 200
  · exact hroot.hOcc 218
  · exact hroot.hOcc 223
  · exact hroot.hOcc 225
  · exact hroot.hOcc 233
  · exact hroot.hOcc 235
  · exact hroot.hOcc 269
  · exact hroot.hOcc 290
  · exact hroot.hOcc 303
  · exact hroot.hOcc 315
  · exact hroot.hOcc 340
  · exact hroot.hOcc 356
  · exact hroot.hOcc 374
  · exact hroot.hOcc 377
  · exact hroot.hOcc 385
  · exact hroot.hOcc 386
  · exact hroot.hOcc 399
  · exact hroot.hOcc 450
  · exact hroot.hOcc 453
  · exact hroot.hOcc 513
  · exact hroot.hOcc 514
  · exact hroot.hOcc 515
  · exact hroot.hOcc 521
  · exact hroot.hOcc 525
  · exact hroot.hOcc 536
  · exact hroot.hOcc 541
  · exact hroot.hOcc 566
  · exact hroot.hOcc 573
  · exact hroot.hOcc 606
  · exact hroot.hOcc 649
  · exact hroot.hOcc 651
  · exact hroot.hOcc 654
  · exact hroot.hOcc 656
  · exact hroot.hOcc 665
  · exact hroot.hOcc 666
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (33 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (36 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (25 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (1 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (35 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35

end QiushiMatmul
