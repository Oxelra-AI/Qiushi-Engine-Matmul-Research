import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0020Refs : Fin 50 → RowRef 726 49 := ![.occ 80, .occ 99, .occ 101, .occ 102, .occ 107, .occ 173, .occ 174, .occ 243, .occ 244, .occ 257, .occ 263, .occ 292, .occ 320, .occ 330, .occ 332, .occ 340, .occ 365, .occ 370, .occ 396, .occ 402, .occ 409, .occ 413, .occ 423, .occ 431, .occ 494, .occ 501, .occ 534, .occ 552, .occ 554, .occ 569, .occ 570, .occ 573, .occ 594, .occ 610, .occ 621, .occ 626, .occ 681, .occ 683, .occ 705, .occ 714, .sumGe, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchLe 46 (0), .branchGe 32 (1), .branchLe 28 (0), .branchLe 22 (0), .branchLe 3 (0)]

def plane491GenLeaf0020Mult : Fin 50 → Nat := ![260701, 591694, 76894, 23525, 236926, 28823, 326888, 323620, 46236, 102021, 38182, 54970, 40677, 266975, 173041, 4452, 322627, 15108, 45607, 73857, 47306, 53857, 335685, 151678, 131230, 34216, 134429, 121156, 154907, 105413, 3610, 47573, 48910, 175233, 137436, 37260, 65200, 153831, 37753, 1337, 768328, 206843, 595287, 315528, 436112, 252476, 2875009, 378506, 289554, 666307]

theorem plane491GenLeaf0020 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0020Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0020Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0020Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0020Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 80
  · exact hroot.hOcc 99
  · exact hroot.hOcc 101
  · exact hroot.hOcc 102
  · exact hroot.hOcc 107
  · exact hroot.hOcc 173
  · exact hroot.hOcc 174
  · exact hroot.hOcc 243
  · exact hroot.hOcc 244
  · exact hroot.hOcc 257
  · exact hroot.hOcc 263
  · exact hroot.hOcc 292
  · exact hroot.hOcc 320
  · exact hroot.hOcc 330
  · exact hroot.hOcc 332
  · exact hroot.hOcc 340
  · exact hroot.hOcc 365
  · exact hroot.hOcc 370
  · exact hroot.hOcc 396
  · exact hroot.hOcc 402
  · exact hroot.hOcc 409
  · exact hroot.hOcc 413
  · exact hroot.hOcc 423
  · exact hroot.hOcc 431
  · exact hroot.hOcc 494
  · exact hroot.hOcc 501
  · exact hroot.hOcc 534
  · exact hroot.hOcc 552
  · exact hroot.hOcc 554
  · exact hroot.hOcc 569
  · exact hroot.hOcc 570
  · exact hroot.hOcc 573
  · exact hroot.hOcc 594
  · exact hroot.hOcc 610
  · exact hroot.hOcc 621
  · exact hroot.hOcc 626
  · exact hroot.hOcc 681
  · exact hroot.hOcc 683
  · exact hroot.hOcc 705
  · exact hroot.hOcc 714
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (32 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (28 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (22 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (3 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3

end QiushiMatmul
