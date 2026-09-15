import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0030Refs : Fin 50 → RowRef 726 49 := ![.occ 102, .occ 105, .occ 111, .occ 116, .occ 119, .occ 126, .occ 157, .occ 158, .occ 166, .occ 219, .occ 243, .occ 304, .occ 335, .occ 351, .occ 364, .occ 368, .occ 394, .occ 400, .occ 410, .occ 420, .occ 422, .occ 432, .occ 501, .occ 504, .occ 533, .occ 558, .occ 573, .occ 581, .occ 584, .occ 628, .occ 642, .occ 647, .occ 680, .occ 685, .occ 692, .occ 704, .occ 720, .occ 725, .sumGe, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchGe 29 (1), .branchLe 43 (0), .branchLe 9 (0), .branchLe 5 (0), .branchLe 44 (0), .branchLe 24 (0), .branchLe 4 (0), .branchLe 26 (0)]

def plane491GenLeaf0030Mult : Fin 50 → Nat := ![23091, 6905, 8944, 3710, 3317, 20542, 36755, 32678, 10206, 15611, 3988, 20350, 23333, 15986, 14972, 4494, 5484, 27356, 622, 740, 1348, 351, 7475, 2073, 19762, 2891, 17612, 6514, 7434, 29607, 3636, 4860, 4792, 9445, 6159, 2452, 1594, 2186, 71945, 57492, 36179, 56062, 152541, 69493, 34942, 54265, 37647, 67085, 59805, 64470]

theorem plane491GenLeaf0030 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0030Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0030Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0030Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0030Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 111
  · exact hroot.hOcc 116
  · exact hroot.hOcc 119
  · exact hroot.hOcc 126
  · exact hroot.hOcc 157
  · exact hroot.hOcc 158
  · exact hroot.hOcc 166
  · exact hroot.hOcc 219
  · exact hroot.hOcc 243
  · exact hroot.hOcc 304
  · exact hroot.hOcc 335
  · exact hroot.hOcc 351
  · exact hroot.hOcc 364
  · exact hroot.hOcc 368
  · exact hroot.hOcc 394
  · exact hroot.hOcc 400
  · exact hroot.hOcc 410
  · exact hroot.hOcc 420
  · exact hroot.hOcc 422
  · exact hroot.hOcc 432
  · exact hroot.hOcc 501
  · exact hroot.hOcc 504
  · exact hroot.hOcc 533
  · exact hroot.hOcc 558
  · exact hroot.hOcc 573
  · exact hroot.hOcc 581
  · exact hroot.hOcc 584
  · exact hroot.hOcc 628
  · exact hroot.hOcc 642
  · exact hroot.hOcc 647
  · exact hroot.hOcc 680
  · exact hroot.hOcc 685
  · exact hroot.hOcc 692
  · exact hroot.hOcc 704
  · exact hroot.hOcc 720
  · exact hroot.hOcc 725
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (9 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (5 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (24 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (4 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (26 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26

end QiushiMatmul
