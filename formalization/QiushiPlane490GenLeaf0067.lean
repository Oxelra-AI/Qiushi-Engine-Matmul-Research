import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0067Refs : Fin 43 → RowRef 713 43 := ![.occ 88, .occ 110, .occ 115, .occ 151, .occ 196, .occ 202, .occ 204, .occ 219, .occ 224, .occ 275, .occ 279, .occ 289, .occ 291, .occ 295, .occ 335, .occ 349, .occ 350, .occ 362, .occ 382, .occ 390, .occ 398, .occ 409, .occ 428, .occ 432, .occ 434, .occ 436, .occ 448, .occ 486, .occ 494, .occ 506, .occ 542, .occ 615, .occ 623, .occ 655, .occ 684, .occ 698, .occ 700, .sumGe, .branchGe 4 (1), .branchLe 34 (0), .branchGe 23 (1), .branchLe 25 (0), .branchGe 18 (1)]

def plane490GenLeaf0067Mult : Fin 43 → Nat := ![10, 9, 81, 141, 185, 5, 301, 74, 9, 73, 190, 74, 161, 179, 48, 319, 128, 148, 2, 187, 10, 259, 21, 82, 57, 16, 196, 37, 37, 111, 205, 16, 200, 182, 70, 72, 5, 571, 2362, 159, 1445, 523, 1567]

theorem plane490GenLeaf0067 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0067Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0067Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0067Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0067Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 88
  · exact hroot.hOcc 110
  · exact hroot.hOcc 115
  · exact hroot.hOcc 151
  · exact hroot.hOcc 196
  · exact hroot.hOcc 202
  · exact hroot.hOcc 204
  · exact hroot.hOcc 219
  · exact hroot.hOcc 224
  · exact hroot.hOcc 275
  · exact hroot.hOcc 279
  · exact hroot.hOcc 289
  · exact hroot.hOcc 291
  · exact hroot.hOcc 295
  · exact hroot.hOcc 335
  · exact hroot.hOcc 349
  · exact hroot.hOcc 350
  · exact hroot.hOcc 362
  · exact hroot.hOcc 382
  · exact hroot.hOcc 390
  · exact hroot.hOcc 398
  · exact hroot.hOcc 409
  · exact hroot.hOcc 428
  · exact hroot.hOcc 432
  · exact hroot.hOcc 434
  · exact hroot.hOcc 436
  · exact hroot.hOcc 448
  · exact hroot.hOcc 486
  · exact hroot.hOcc 494
  · exact hroot.hOcc 506
  · exact hroot.hOcc 542
  · exact hroot.hOcc 615
  · exact hroot.hOcc 623
  · exact hroot.hOcc 655
  · exact hroot.hOcc 684
  · exact hroot.hOcc 698
  · exact hroot.hOcc 700
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18

end QiushiMatmul
