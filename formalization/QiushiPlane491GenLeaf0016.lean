import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0016Refs : Fin 50 → RowRef 726 49 := ![.occ 80, .occ 101, .occ 102, .occ 105, .occ 120, .occ 121, .occ 134, .occ 143, .occ 202, .occ 222, .occ 237, .occ 244, .occ 248, .occ 249, .occ 257, .occ 286, .occ 306, .occ 319, .occ 320, .occ 326, .occ 357, .occ 358, .occ 364, .occ 368, .occ 424, .occ 425, .occ 431, .occ 508, .occ 532, .occ 565, .occ 569, .occ 596, .occ 615, .occ 621, .occ 652, .occ 697, .occ 711, .occ 723, .sumGe, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchLe 46 (0), .branchLe 32 (0), .branchGe 38 (1), .branchLe 1 (0), .branchLe 10 (0), .branchLe 7 (0), .branchGe 8 (1)]

def plane491GenLeaf0016Mult : Fin 50 → Nat := ![27633, 20116, 18483, 1502, 6650, 16465, 5269, 8872, 11579, 487, 7335, 6202, 5637, 6365, 3792, 1698, 2429, 13592, 10175, 223, 3787, 10536, 2271, 5871, 908, 5432, 2948, 8295, 2211, 3426, 13448, 2496, 1627, 65, 2514, 5626, 331, 4010, 27964, 17683, 6221, 21185, 9587, 7461, 10166, 90572, 21743, 7772, 10506, 115239]

theorem plane491GenLeaf0016 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0016Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0016Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0016Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0016Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 80
  · exact hroot.hOcc 101
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 134
  · exact hroot.hOcc 143
  · exact hroot.hOcc 202
  · exact hroot.hOcc 222
  · exact hroot.hOcc 237
  · exact hroot.hOcc 244
  · exact hroot.hOcc 248
  · exact hroot.hOcc 249
  · exact hroot.hOcc 257
  · exact hroot.hOcc 286
  · exact hroot.hOcc 306
  · exact hroot.hOcc 319
  · exact hroot.hOcc 320
  · exact hroot.hOcc 326
  · exact hroot.hOcc 357
  · exact hroot.hOcc 358
  · exact hroot.hOcc 364
  · exact hroot.hOcc 368
  · exact hroot.hOcc 424
  · exact hroot.hOcc 425
  · exact hroot.hOcc 431
  · exact hroot.hOcc 508
  · exact hroot.hOcc 532
  · exact hroot.hOcc 565
  · exact hroot.hOcc 569
  · exact hroot.hOcc 596
  · exact hroot.hOcc 615
  · exact hroot.hOcc 621
  · exact hroot.hOcc 652
  · exact hroot.hOcc 697
  · exact hroot.hOcc 711
  · exact hroot.hOcc 723
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (32 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (38 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38
  · change (∑ k, (if k = (1 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (10 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (7 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
