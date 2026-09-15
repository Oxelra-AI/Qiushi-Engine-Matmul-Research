import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0014Refs : Fin 50 → RowRef 726 49 := ![.occ 84, .occ 88, .occ 102, .occ 103, .occ 107, .occ 108, .occ 121, .occ 124, .occ 202, .occ 246, .occ 258, .occ 287, .occ 296, .occ 364, .occ 366, .occ 370, .occ 413, .occ 431, .occ 510, .occ 515, .occ 532, .occ 552, .occ 559, .occ 569, .occ 573, .occ 574, .occ 576, .occ 643, .occ 647, .occ 665, .occ 685, .occ 691, .occ 692, .occ 700, .occ 707, .occ 721, .occ 722, .sumGe, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchLe 46 (0), .branchLe 32 (0), .branchGe 38 (1), .branchLe 1 (0), .branchLe 10 (0), .branchLe 7 (0), .branchLe 8 (0), .branchLe 12 (0)]

def plane491GenLeaf0014Mult : Fin 50 → Nat := ![28280, 42953, 101014, 33240, 8596, 118212, 78945, 556, 232, 8794, 26454, 83062, 27094, 8930, 8426, 34734, 2406, 77812, 20884, 21388, 16730, 27828, 19634, 19724, 37677, 12120, 15428, 24236, 62467, 31782, 6438, 33020, 19064, 34305, 27062, 49995, 43298, 253918, 178838, 163405, 151348, 141120, 128644, 141790, 308773, 221026, 203923, 185356, 234194, 139951]

theorem plane491GenLeaf0014 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0014Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0014Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0014Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0014Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 88
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 107
  · exact hroot.hOcc 108
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 202
  · exact hroot.hOcc 246
  · exact hroot.hOcc 258
  · exact hroot.hOcc 287
  · exact hroot.hOcc 296
  · exact hroot.hOcc 364
  · exact hroot.hOcc 366
  · exact hroot.hOcc 370
  · exact hroot.hOcc 413
  · exact hroot.hOcc 431
  · exact hroot.hOcc 510
  · exact hroot.hOcc 515
  · exact hroot.hOcc 532
  · exact hroot.hOcc 552
  · exact hroot.hOcc 559
  · exact hroot.hOcc 569
  · exact hroot.hOcc 573
  · exact hroot.hOcc 574
  · exact hroot.hOcc 576
  · exact hroot.hOcc 643
  · exact hroot.hOcc 647
  · exact hroot.hOcc 665
  · exact hroot.hOcc 685
  · exact hroot.hOcc 691
  · exact hroot.hOcc 692
  · exact hroot.hOcc 700
  · exact hroot.hOcc 707
  · exact hroot.hOcc 721
  · exact hroot.hOcc 722
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
  · change (∑ k, (if k = (8 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (12 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12

end QiushiMatmul
