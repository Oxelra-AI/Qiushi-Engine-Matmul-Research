import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0026Refs : Fin 50 → RowRef 726 49 := ![.occ 104, .occ 113, .occ 117, .occ 208, .occ 209, .occ 219, .occ 221, .occ 244, .occ 247, .occ 255, .occ 257, .occ 258, .occ 300, .occ 314, .occ 315, .occ 317, .occ 327, .occ 329, .occ 335, .occ 351, .occ 359, .occ 370, .occ 377, .occ 414, .occ 421, .occ 422, .occ 431, .occ 444, .occ 448, .occ 490, .occ 513, .occ 524, .occ 543, .occ 554, .occ 585, .occ 586, .occ 630, .occ 664, .occ 685, .occ 700, .sumGe, .nonneg 18, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchGe 46 (1), .branchLe 14 (0), .branchLe 43 (0), .branchLe 8 (0)]

def plane491GenLeaf0026Mult : Fin 50 → Nat := ![721242, 2489556, 3403422, 1627267, 1067767, 513994, 229655, 326974, 338523, 24836, 440240, 1040195, 1812811, 261608, 2710367, 4112512, 2640618, 2386879, 827247, 736786, 1051207, 904306, 3880144, 253782, 1050545, 2383299, 2176437, 655740, 767141, 17219, 465076, 762142, 2333715, 295792, 497441, 1485666, 1015359, 2269346, 1763389, 233982, 8210228, 3872944, 1080979, 5161521, 7448086, 4811570, 30038275, 7445033, 7914436, 7466579]

theorem plane491GenLeaf0026 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_46 : (1 : Int) ≤ x 46)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0026Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0026Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0026Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0026Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 104
  · exact hroot.hOcc 113
  · exact hroot.hOcc 117
  · exact hroot.hOcc 208
  · exact hroot.hOcc 209
  · exact hroot.hOcc 219
  · exact hroot.hOcc 221
  · exact hroot.hOcc 244
  · exact hroot.hOcc 247
  · exact hroot.hOcc 255
  · exact hroot.hOcc 257
  · exact hroot.hOcc 258
  · exact hroot.hOcc 300
  · exact hroot.hOcc 314
  · exact hroot.hOcc 315
  · exact hroot.hOcc 317
  · exact hroot.hOcc 327
  · exact hroot.hOcc 329
  · exact hroot.hOcc 335
  · exact hroot.hOcc 351
  · exact hroot.hOcc 359
  · exact hroot.hOcc 370
  · exact hroot.hOcc 377
  · exact hroot.hOcc 414
  · exact hroot.hOcc 421
  · exact hroot.hOcc 422
  · exact hroot.hOcc 431
  · exact hroot.hOcc 444
  · exact hroot.hOcc 448
  · exact hroot.hOcc 490
  · exact hroot.hOcc 513
  · exact hroot.hOcc 524
  · exact hroot.hOcc 543
  · exact hroot.hOcc 554
  · exact hroot.hOcc 585
  · exact hroot.hOcc 586
  · exact hroot.hOcc 630
  · exact hroot.hOcc 664
  · exact hroot.hOcc 685
  · exact hroot.hOcc 700
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_46
  · change (∑ k, (if k = (14 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (8 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8

end QiushiMatmul
