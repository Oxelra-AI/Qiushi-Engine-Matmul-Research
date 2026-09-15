import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0048Refs : Fin 50 → RowRef 726 49 := ![.occ 82, .occ 100, .occ 102, .occ 106, .occ 107, .occ 113, .occ 119, .occ 164, .occ 219, .occ 224, .occ 232, .occ 244, .occ 257, .occ 273, .occ 293, .occ 305, .occ 332, .occ 335, .occ 367, .occ 382, .occ 392, .occ 394, .occ 421, .occ 422, .occ 424, .occ 431, .occ 450, .occ 459, .occ 461, .occ 511, .occ 624, .occ 628, .occ 634, .occ 642, .occ 661, .occ 662, .occ 664, .occ 709, .occ 725, .sumGe, .branchLe 31 (0), .branchLe 16 (0), .branchGe 27 (1), .branchLe 11 (0), .branchLe 23 (0), .branchLe 0 (0), .branchLe 43 (0), .branchLe 6 (0), .branchLe 44 (0), .branchGe 7 (1)]

def plane491GenLeaf0048Mult : Fin 50 → Nat := ![259737, 296305, 65143, 109209, 61030, 24135, 38866, 125448, 36568, 31363, 195735, 24054, 12620, 16147, 42946, 39112, 43954, 4562, 87667, 34847, 108105, 42192, 111695, 35465, 70043, 46030, 5892, 18030, 43764, 51289, 14958, 78548, 73606, 58110, 31457, 15096, 44482, 30475, 4562, 296305, 134477, 58490, 928604, 136721, 296305, 59440, 187029, 164589, 161827, 857896]

theorem plane491GenLeaf0048 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0048Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0048Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0048Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0048Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 113
  · exact hroot.hOcc 119
  · exact hroot.hOcc 164
  · exact hroot.hOcc 219
  · exact hroot.hOcc 224
  · exact hroot.hOcc 232
  · exact hroot.hOcc 244
  · exact hroot.hOcc 257
  · exact hroot.hOcc 273
  · exact hroot.hOcc 293
  · exact hroot.hOcc 305
  · exact hroot.hOcc 332
  · exact hroot.hOcc 335
  · exact hroot.hOcc 367
  · exact hroot.hOcc 382
  · exact hroot.hOcc 392
  · exact hroot.hOcc 394
  · exact hroot.hOcc 421
  · exact hroot.hOcc 422
  · exact hroot.hOcc 424
  · exact hroot.hOcc 431
  · exact hroot.hOcc 450
  · exact hroot.hOcc 459
  · exact hroot.hOcc 461
  · exact hroot.hOcc 511
  · exact hroot.hOcc 624
  · exact hroot.hOcc 628
  · exact hroot.hOcc 634
  · exact hroot.hOcc 642
  · exact hroot.hOcc 661
  · exact hroot.hOcc 662
  · exact hroot.hOcc 664
  · exact hroot.hOcc 709
  · exact hroot.hOcc 725
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (23 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (0 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (6 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (7 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7

end QiushiMatmul
