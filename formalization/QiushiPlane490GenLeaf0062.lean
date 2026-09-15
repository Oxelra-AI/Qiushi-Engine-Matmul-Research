import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0062Refs : Fin 44 → RowRef 713 43 := ![.occ 93, .occ 111, .occ 115, .occ 151, .occ 196, .occ 202, .occ 204, .occ 243, .occ 244, .occ 247, .occ 249, .occ 252, .occ 269, .occ 274, .occ 275, .occ 276, .occ 277, .occ 278, .occ 295, .occ 304, .occ 335, .occ 346, .occ 351, .occ 390, .occ 448, .occ 455, .occ 464, .occ 542, .occ 570, .occ 615, .occ 677, .occ 692, .occ 693, .occ 695, .occ 697, .occ 707, .sumGe, .branchLe 29 (0), .branchGe 4 (1), .branchLe 34 (0), .branchLe 23 (0), .branchGe 39 (1), .branchGe 18 (1), .branchLe 40 (0)]

def plane490GenLeaf0062Mult : Fin 44 → Nat := ![276, 323, 1801, 169, 1094, 477, 1620, 205, 467, 649, 170, 788, 775, 1641, 2428, 1612, 276, 189, 836, 276, 1231, 236, 439, 1550, 1406, 199, 340, 389, 1077, 926, 122, 659, 383, 32, 321, 248, 3884, 2932, 14740, 2273, 3495, 4587, 6549, 3253]

theorem plane490GenLeaf0062 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0062Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0062Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0062Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0062Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 93
  · exact hroot.hOcc 111
  · exact hroot.hOcc 115
  · exact hroot.hOcc 151
  · exact hroot.hOcc 196
  · exact hroot.hOcc 202
  · exact hroot.hOcc 204
  · exact hroot.hOcc 243
  · exact hroot.hOcc 244
  · exact hroot.hOcc 247
  · exact hroot.hOcc 249
  · exact hroot.hOcc 252
  · exact hroot.hOcc 269
  · exact hroot.hOcc 274
  · exact hroot.hOcc 275
  · exact hroot.hOcc 276
  · exact hroot.hOcc 277
  · exact hroot.hOcc 278
  · exact hroot.hOcc 295
  · exact hroot.hOcc 304
  · exact hroot.hOcc 335
  · exact hroot.hOcc 346
  · exact hroot.hOcc 351
  · exact hroot.hOcc 390
  · exact hroot.hOcc 448
  · exact hroot.hOcc 455
  · exact hroot.hOcc 464
  · exact hroot.hOcc 542
  · exact hroot.hOcc 570
  · exact hroot.hOcc 615
  · exact hroot.hOcc 677
  · exact hroot.hOcc 692
  · exact hroot.hOcc 693
  · exact hroot.hOcc 695
  · exact hroot.hOcc 697
  · exact hroot.hOcc 707
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (40 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40

end QiushiMatmul
