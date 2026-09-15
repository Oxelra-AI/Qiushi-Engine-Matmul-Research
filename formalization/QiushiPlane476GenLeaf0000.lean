import QiushiPlane476GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane476GenLeaf0000Refs : Fin 51 → RowRef 113 50 := ![.occ 15, .occ 16, .occ 18, .occ 19, .occ 21, .occ 24, .occ 28, .occ 35, .occ 37, .occ 38, .occ 40, .occ 43, .occ 44, .occ 47, .occ 48, .occ 49, .occ 50, .occ 52, .occ 53, .occ 54, .occ 55, .occ 56, .occ 57, .occ 58, .occ 60, .occ 62, .occ 66, .occ 70, .occ 71, .occ 72, .occ 73, .occ 76, .occ 78, .occ 79, .occ 80, .occ 82, .occ 84, .occ 85, .occ 87, .occ 89, .occ 97, .occ 98, .occ 99, .occ 101, .occ 110, .occ 112, .sumGe, .nonneg 0, .nonneg 32, .branchLe 35 (0), .branchLe 11 (0)]

def plane476GenLeaf0000Mult : Fin 51 → Nat := ![18917872, 1832091, 1883309, 12281125, 2435112, 3410142, 5910543, 4905080, 21290845, 5275100, 30360271, 36114686, 8625095, 11233183, 72703, 3839619, 1094188, 20853944, 4718632, 2928690, 11835668, 16488911, 35426386, 5297894, 8781537, 1913282, 7258474, 10006581, 10210851, 16871849, 5652873, 2594992, 9283227, 24240743, 12639013, 14559660, 2423478, 173615, 12643997, 12369090, 12935673, 7526296, 12099144, 3659012, 7893178, 8529557, 78574101, 8080351, 2903052, 42497690, 75645411]

theorem plane476GenLeaf0000 (x : Fin 50 → Int)
    (hroot : plane476GenOccSys.RootHolds x)
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane476GenLeaf0000Refs i).resolveCoeff plane476GenOccSys j)
    (fun i => (plane476GenLeaf0000Refs i).resolveRhs plane476GenOccSys) plane476GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane476GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 21
  · exact hroot.hOcc 24
  · exact hroot.hOcc 28
  · exact hroot.hOcc 35
  · exact hroot.hOcc 37
  · exact hroot.hOcc 38
  · exact hroot.hOcc 40
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 47
  · exact hroot.hOcc 48
  · exact hroot.hOcc 49
  · exact hroot.hOcc 50
  · exact hroot.hOcc 52
  · exact hroot.hOcc 53
  · exact hroot.hOcc 54
  · exact hroot.hOcc 55
  · exact hroot.hOcc 56
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 60
  · exact hroot.hOcc 62
  · exact hroot.hOcc 66
  · exact hroot.hOcc 70
  · exact hroot.hOcc 71
  · exact hroot.hOcc 72
  · exact hroot.hOcc 73
  · exact hroot.hOcc 76
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 80
  · exact hroot.hOcc 82
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 87
  · exact hroot.hOcc 89
  · exact hroot.hOcc 97
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 101
  · exact hroot.hOcc 110
  · exact hroot.hOcc 112
  · change (∑ j, (-1 : Int) * x j) ≤ -plane476GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (32 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (35 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (11 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11

end QiushiMatmul
