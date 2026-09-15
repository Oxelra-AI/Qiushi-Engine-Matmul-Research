import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0038Refs : Fin 50 → RowRef 726 49 := ![.occ 78, .occ 80, .occ 97, .occ 116, .occ 119, .occ 121, .occ 157, .occ 173, .occ 203, .occ 230, .occ 240, .occ 241, .occ 257, .occ 304, .occ 327, .occ 335, .occ 365, .occ 367, .occ 420, .occ 422, .occ 425, .occ 430, .occ 501, .occ 552, .occ 570, .occ 574, .occ 581, .occ 584, .occ 592, .occ 594, .occ 599, .occ 624, .occ 628, .occ 678, .occ 685, .occ 686, .occ 703, .occ 704, .occ 713, .sumGe, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchGe 29 (1), .branchLe 43 (0), .branchGe 9 (1), .branchLe 0 (0), .branchLe 23 (0), .branchLe 35 (0), .branchLe 4 (0)]

def plane491GenLeaf0038Mult : Fin 50 → Nat := ![226059, 177394, 206326, 40333, 79010, 55205, 92583, 37871, 70925, 16004, 88943, 77755, 141513, 41892, 32066, 143662, 25037, 3128, 145701, 164213, 77489, 136605, 61663, 102514, 33364, 183553, 16602, 56001, 51499, 113466, 32603, 17927, 39045, 30889, 12878, 164724, 12311, 23380, 57260, 513683, 419954, 244753, 476335, 896591, 343473, 797043, 349506, 227338, 451258, 482878]

theorem plane491GenLeaf0038 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0038Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0038Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0038Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0038Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 78
  · exact hroot.hOcc 80
  · exact hroot.hOcc 97
  · exact hroot.hOcc 116
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 157
  · exact hroot.hOcc 173
  · exact hroot.hOcc 203
  · exact hroot.hOcc 230
  · exact hroot.hOcc 240
  · exact hroot.hOcc 241
  · exact hroot.hOcc 257
  · exact hroot.hOcc 304
  · exact hroot.hOcc 327
  · exact hroot.hOcc 335
  · exact hroot.hOcc 365
  · exact hroot.hOcc 367
  · exact hroot.hOcc 420
  · exact hroot.hOcc 422
  · exact hroot.hOcc 425
  · exact hroot.hOcc 430
  · exact hroot.hOcc 501
  · exact hroot.hOcc 552
  · exact hroot.hOcc 570
  · exact hroot.hOcc 574
  · exact hroot.hOcc 581
  · exact hroot.hOcc 584
  · exact hroot.hOcc 592
  · exact hroot.hOcc 594
  · exact hroot.hOcc 599
  · exact hroot.hOcc 624
  · exact hroot.hOcc 628
  · exact hroot.hOcc 678
  · exact hroot.hOcc 685
  · exact hroot.hOcc 686
  · exact hroot.hOcc 703
  · exact hroot.hOcc 704
  · exact hroot.hOcc 713
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (9 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (0 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (23 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (35 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (4 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4

end QiushiMatmul
