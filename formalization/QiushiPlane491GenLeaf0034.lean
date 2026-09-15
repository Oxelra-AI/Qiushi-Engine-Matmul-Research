import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0034Refs : Fin 50 → RowRef 726 49 := ![.occ 85, .occ 97, .occ 102, .occ 104, .occ 116, .occ 141, .occ 222, .occ 243, .occ 260, .occ 292, .occ 335, .occ 336, .occ 364, .occ 373, .occ 398, .occ 420, .occ 423, .occ 437, .occ 464, .occ 486, .occ 487, .occ 495, .occ 501, .occ 504, .occ 508, .occ 569, .occ 594, .occ 603, .occ 621, .occ 628, .occ 640, .occ 642, .occ 673, .occ 685, .occ 704, .occ 718, .sumGe, .nonneg 10, .nonneg 23, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchGe 29 (1), .branchLe 43 (0), .branchLe 9 (0), .branchLe 5 (0), .branchLe 44 (0), .branchLe 24 (0), .branchGe 4 (1), .branchGe 21 (1)]

def plane491GenLeaf0034Mult : Fin 50 → Nat := ![3506, 103133, 217932, 287729, 380719, 75769, 3402, 110989, 124283, 255147, 219602, 5267, 47676, 150151, 146102, 48540, 3228, 33894, 27697, 89284, 71907, 78178, 13827, 136351, 19110, 12422, 107504, 67536, 84000, 208949, 4439, 28503, 33436, 110948, 25214, 69886, 545384, 82949, 49697, 445712, 458141, 516881, 636073, 394977, 384193, 358279, 429331, 254600, 860735, 868159]

theorem plane491GenLeaf0034 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0034Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0034Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0034Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0034Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 97
  · exact hroot.hOcc 102
  · exact hroot.hOcc 104
  · exact hroot.hOcc 116
  · exact hroot.hOcc 141
  · exact hroot.hOcc 222
  · exact hroot.hOcc 243
  · exact hroot.hOcc 260
  · exact hroot.hOcc 292
  · exact hroot.hOcc 335
  · exact hroot.hOcc 336
  · exact hroot.hOcc 364
  · exact hroot.hOcc 373
  · exact hroot.hOcc 398
  · exact hroot.hOcc 420
  · exact hroot.hOcc 423
  · exact hroot.hOcc 437
  · exact hroot.hOcc 464
  · exact hroot.hOcc 486
  · exact hroot.hOcc 487
  · exact hroot.hOcc 495
  · exact hroot.hOcc 501
  · exact hroot.hOcc 504
  · exact hroot.hOcc 508
  · exact hroot.hOcc 569
  · exact hroot.hOcc 594
  · exact hroot.hOcc 603
  · exact hroot.hOcc 621
  · exact hroot.hOcc 628
  · exact hroot.hOcc 640
  · exact hroot.hOcc 642
  · exact hroot.hOcc 673
  · exact hroot.hOcc 685
  · exact hroot.hOcc 704
  · exact hroot.hOcc 718
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (23 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (9 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (5 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (24 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (4 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (21 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21

end QiushiMatmul
