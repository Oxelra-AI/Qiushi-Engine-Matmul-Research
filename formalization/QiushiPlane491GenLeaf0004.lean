import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0004Refs : Fin 50 → RowRef 726 49 := ![.occ 78, .occ 80, .occ 88, .occ 89, .occ 103, .occ 105, .occ 111, .occ 219, .occ 230, .occ 240, .occ 257, .occ 258, .occ 279, .occ 299, .occ 324, .occ 326, .occ 366, .occ 373, .occ 385, .occ 397, .occ 431, .occ 456, .occ 531, .occ 532, .occ 554, .occ 559, .occ 563, .occ 575, .occ 582, .occ 584, .occ 585, .occ 594, .occ 616, .occ 624, .occ 631, .occ 643, .occ 700, .occ 716, .sumGe, .nonneg 34, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchLe 46 (0), .branchLe 32 (0), .branchLe 38 (0), .branchLe 6 (0), .branchGe 9 (1), .branchLe 45 (0)]

def plane491GenLeaf0004Mult : Fin 50 → Nat := ![1212062, 306898, 262005, 621478, 372054, 978581, 524311, 600352, 307898, 916184, 768340, 143815, 217592, 363445, 227872, 355376, 609364, 436979, 107830, 76852, 159735, 127844, 405896, 662455, 525348, 142281, 785210, 665739, 349450, 58421, 21145, 225784, 146800, 108854, 60482, 268628, 226780, 59502, 2548675, 301079, 1733827, 1434364, 1369564, 2322891, 2300750, 1570181, 1893532, 2262409, 4269233, 2346892]

theorem plane491GenLeaf0004 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_45 : x 45 ≤ (0 : Int))
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0004Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0004Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 78
  · exact hroot.hOcc 80
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 111
  · exact hroot.hOcc 219
  · exact hroot.hOcc 230
  · exact hroot.hOcc 240
  · exact hroot.hOcc 257
  · exact hroot.hOcc 258
  · exact hroot.hOcc 279
  · exact hroot.hOcc 299
  · exact hroot.hOcc 324
  · exact hroot.hOcc 326
  · exact hroot.hOcc 366
  · exact hroot.hOcc 373
  · exact hroot.hOcc 385
  · exact hroot.hOcc 397
  · exact hroot.hOcc 431
  · exact hroot.hOcc 456
  · exact hroot.hOcc 531
  · exact hroot.hOcc 532
  · exact hroot.hOcc 554
  · exact hroot.hOcc 559
  · exact hroot.hOcc 563
  · exact hroot.hOcc 575
  · exact hroot.hOcc 582
  · exact hroot.hOcc 584
  · exact hroot.hOcc 585
  · exact hroot.hOcc 594
  · exact hroot.hOcc 616
  · exact hroot.hOcc 624
  · exact hroot.hOcc 631
  · exact hroot.hOcc 643
  · exact hroot.hOcc 700
  · exact hroot.hOcc 716
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (34 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (32 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (38 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (6 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (9 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (45 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_45

end QiushiMatmul
