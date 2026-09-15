import QiushiFrozenRank361Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane361RankCoverGenLeaf0000Refs : Fin 22 → RowRef 86 24 := ![.occ 8, .occ 16, .occ 36, .occ 39, .occ 40, .occ 44, .occ 54, .occ 55, .occ 61, .occ 64, .occ 69, .occ 70, .occ 72, .occ 74, .occ 75, .occ 84, .sumGe, .branchLe 14 (0), .branchLe 7 (0), .branchLe 5 (1), .branchLe 6 (0), .branchLe 0 (0)]

def plane361RankCoverGenLeaf0000Mult : Fin 22 → Nat := ![6, 12, 6, 2, 6, 4, 2, 1, 5, 1, 2, 2, 1, 2, 4, 4, 12, 8, 12, 12, 6, 8]

theorem plane361RankCoverGenLeaf0000 (x : Fin 24 → Int)
    (hroot : plane361RankCoverGenOccSys.RootHolds x)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (1 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_0 : x 0 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane361RankCoverGenLeaf0000Refs i).resolveCoeff plane361RankCoverGenOccSys j)
    (fun i => (plane361RankCoverGenLeaf0000Refs i).resolveRhs plane361RankCoverGenOccSys) plane361RankCoverGenLeaf0000Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane361RankCoverGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · exact hroot.hOcc 16
  · exact hroot.hOcc 36
  · exact hroot.hOcc 39
  · exact hroot.hOcc 40
  · exact hroot.hOcc 44
  · exact hroot.hOcc 54
  · exact hroot.hOcc 55
  · exact hroot.hOcc 61
  · exact hroot.hOcc 64
  · exact hroot.hOcc 69
  · exact hroot.hOcc 70
  · exact hroot.hOcc 72
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
  · exact hroot.hOcc 84
  · change (∑ j, (-1 : Int) * x j) ≤ -plane361RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (7 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (5 : Fin 24) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (0 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane361RankCoverGenLeaf0001Refs : Fin 18 → RowRef 86 24 := ![.occ 1, .occ 8, .occ 14, .occ 16, .occ 39, .occ 44, .occ 48, .occ 49, .occ 54, .occ 55, .occ 60, .occ 81, .sumGe, .nonneg 20, .branchLe 7 (0), .branchLe 5 (1), .branchLe 6 (0), .branchGe 0 (1)]

def plane361RankCoverGenLeaf0001Mult : Fin 18 → Nat := ![1, 2, 1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4]

theorem plane361RankCoverGenLeaf0001 (x : Fin 24 → Int)
    (hroot : plane361RankCoverGenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (1 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane361RankCoverGenLeaf0001Refs i).resolveCoeff plane361RankCoverGenOccSys j)
    (fun i => (plane361RankCoverGenLeaf0001Refs i).resolveRhs plane361RankCoverGenOccSys) plane361RankCoverGenLeaf0001Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane361RankCoverGenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · exact hroot.hOcc 8
  · exact hroot.hOcc 14
  · exact hroot.hOcc 16
  · exact hroot.hOcc 39
  · exact hroot.hOcc 44
  · exact hroot.hOcc 48
  · exact hroot.hOcc 49
  · exact hroot.hOcc 54
  · exact hroot.hOcc 55
  · exact hroot.hOcc 60
  · exact hroot.hOcc 81
  · change (∑ j, (-1 : Int) * x j) ≤ -plane361RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (20 : Fin 24) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (7 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (5 : Fin 24) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (0 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane361RankCoverGenLeaf0002Refs : Fin 20 → RowRef 86 24 := ![.occ 0, .occ 11, .occ 16, .occ 17, .occ 22, .occ 31, .occ 37, .occ 44, .occ 46, .occ 50, .occ 72, .occ 74, .occ 83, .occ 84, .sumGe, .branchLe 14 (0), .branchLe 7 (0), .branchLe 5 (1), .branchGe 6 (1), .branchLe 15 (0)]

def plane361RankCoverGenLeaf0002Mult : Fin 20 → Nat := ![1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 2]

theorem plane361RankCoverGenLeaf0002 (x : Fin 24 → Int)
    (hroot : plane361RankCoverGenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (1 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane361RankCoverGenLeaf0002Refs i).resolveCoeff plane361RankCoverGenOccSys j)
    (fun i => (plane361RankCoverGenLeaf0002Refs i).resolveRhs plane361RankCoverGenOccSys) plane361RankCoverGenLeaf0002Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane361RankCoverGenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 11
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 22
  · exact hroot.hOcc 31
  · exact hroot.hOcc 37
  · exact hroot.hOcc 44
  · exact hroot.hOcc 46
  · exact hroot.hOcc 50
  · exact hroot.hOcc 72
  · exact hroot.hOcc 74
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · change (∑ j, (-1 : Int) * x j) ≤ -plane361RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (7 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (5 : Fin 24) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (15 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane361RankCoverGenLeaf0003Refs : Fin 16 → RowRef 86 24 := ![.occ 0, .occ 16, .occ 40, .occ 44, .occ 57, .occ 65, .occ 71, .occ 72, .occ 81, .occ 82, .occ 83, .occ 84, .sumGe, .branchLe 7 (0), .branchGe 6 (1), .branchGe 15 (1)]

def plane361RankCoverGenLeaf0003Mult : Fin 16 → Nat := ![2, 2, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 2, 4]

theorem plane361RankCoverGenLeaf0003 (x : Fin 24 → Int)
    (hroot : plane361RankCoverGenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane361RankCoverGenLeaf0003Refs i).resolveCoeff plane361RankCoverGenOccSys j)
    (fun i => (plane361RankCoverGenLeaf0003Refs i).resolveRhs plane361RankCoverGenOccSys) plane361RankCoverGenLeaf0003Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane361RankCoverGenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 16
  · exact hroot.hOcc 40
  · exact hroot.hOcc 44
  · exact hroot.hOcc 57
  · exact hroot.hOcc 65
  · exact hroot.hOcc 71
  · exact hroot.hOcc 72
  · exact hroot.hOcc 81
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · change (∑ j, (-1 : Int) * x j) ≤ -plane361RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (6 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (15 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane361RankCoverGenLeaf0004Refs : Fin 25 → RowRef 86 24 := ![.occ 0, .occ 5, .occ 8, .occ 16, .occ 25, .occ 27, .occ 28, .occ 41, .occ 42, .occ 46, .occ 49, .occ 50, .occ 53, .occ 54, .occ 55, .occ 61, .occ 70, .occ 71, .occ 78, .occ 79, .occ 81, .sumGe, .branchLe 14 (0), .branchLe 7 (0), .branchGe 5 (2)]

def plane361RankCoverGenLeaf0004Mult : Fin 25 → Nat := ![12, 5, 5, 11, 23, 12, 20, 3, 2, 1, 3, 3, 12, 2, 8, 1, 9, 4, 3, 11, 11, 23, 7, 20, 74]

theorem plane361RankCoverGenLeaf0004 (x : Fin 24 → Int)
    (hroot : plane361RankCoverGenOccSys.RootHolds x)
    (hLB_5 : (2 : Int) ≤ x 5)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane361RankCoverGenLeaf0004Refs i).resolveCoeff plane361RankCoverGenOccSys j)
    (fun i => (plane361RankCoverGenLeaf0004Refs i).resolveRhs plane361RankCoverGenOccSys) plane361RankCoverGenLeaf0004Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane361RankCoverGenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 5
  · exact hroot.hOcc 8
  · exact hroot.hOcc 16
  · exact hroot.hOcc 25
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 41
  · exact hroot.hOcc 42
  · exact hroot.hOcc 46
  · exact hroot.hOcc 49
  · exact hroot.hOcc 50
  · exact hroot.hOcc 53
  · exact hroot.hOcc 54
  · exact hroot.hOcc 55
  · exact hroot.hOcc 61
  · exact hroot.hOcc 70
  · exact hroot.hOcc 71
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · change (∑ j, (-1 : Int) * x j) ≤ -plane361RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (7 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (5 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane361RankCoverGenLeaf0005Refs : Fin 25 → RowRef 86 24 := ![.occ 0, .occ 10, .occ 16, .occ 23, .occ 25, .occ 31, .occ 33, .occ 34, .occ 35, .occ 37, .occ 39, .occ 44, .occ 56, .occ 58, .occ 62, .occ 63, .occ 64, .occ 66, .occ 73, .occ 77, .occ 83, .sumGe, .branchLe 14 (0), .branchGe 7 (1), .branchLe 0 (0)]

def plane361RankCoverGenLeaf0005Mult : Fin 25 → Nat := ![34, 6, 24, 47, 22, 2, 37, 54, 18, 4, 15, 10, 1, 48, 5, 30, 8, 3, 21, 32, 4, 58, 53, 193, 48]

theorem plane361RankCoverGenLeaf0005 (x : Fin 24 → Int)
    (hroot : plane361RankCoverGenOccSys.RootHolds x)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_0 : x 0 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane361RankCoverGenLeaf0005Refs i).resolveCoeff plane361RankCoverGenOccSys j)
    (fun i => (plane361RankCoverGenLeaf0005Refs i).resolveRhs plane361RankCoverGenOccSys) plane361RankCoverGenLeaf0005Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane361RankCoverGenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 10
  · exact hroot.hOcc 16
  · exact hroot.hOcc 23
  · exact hroot.hOcc 25
  · exact hroot.hOcc 31
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 37
  · exact hroot.hOcc 39
  · exact hroot.hOcc 44
  · exact hroot.hOcc 56
  · exact hroot.hOcc 58
  · exact hroot.hOcc 62
  · exact hroot.hOcc 63
  · exact hroot.hOcc 64
  · exact hroot.hOcc 66
  · exact hroot.hOcc 73
  · exact hroot.hOcc 77
  · exact hroot.hOcc 83
  · change (∑ j, (-1 : Int) * x j) ≤ -plane361RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (7 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (0 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane361RankCoverGenLeaf0006Refs : Fin 25 → RowRef 86 24 := ![.occ 0, .occ 11, .occ 13, .occ 16, .occ 21, .occ 23, .occ 26, .occ 33, .occ 34, .occ 39, .occ 44, .occ 47, .occ 49, .occ 53, .occ 54, .occ 58, .occ 63, .occ 69, .occ 76, .occ 77, .occ 81, .sumGe, .branchLe 14 (0), .branchGe 7 (1), .branchGe 0 (1)]

def plane361RankCoverGenLeaf0006Mult : Fin 25 → Nat := ![17, 2, 21, 6, 8, 20, 3, 13, 21, 5, 8, 2, 5, 2, 1, 12, 15, 2, 2, 15, 1, 23, 17, 97, 14]

theorem plane361RankCoverGenLeaf0006 (x : Fin 24 → Int)
    (hroot : plane361RankCoverGenOccSys.RootHolds x)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane361RankCoverGenLeaf0006Refs i).resolveCoeff plane361RankCoverGenOccSys j)
    (fun i => (plane361RankCoverGenLeaf0006Refs i).resolveRhs plane361RankCoverGenOccSys) plane361RankCoverGenLeaf0006Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane361RankCoverGenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 11
  · exact hroot.hOcc 13
  · exact hroot.hOcc 16
  · exact hroot.hOcc 21
  · exact hroot.hOcc 23
  · exact hroot.hOcc 26
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 39
  · exact hroot.hOcc 44
  · exact hroot.hOcc 47
  · exact hroot.hOcc 49
  · exact hroot.hOcc 53
  · exact hroot.hOcc 54
  · exact hroot.hOcc 58
  · exact hroot.hOcc 63
  · exact hroot.hOcc 69
  · exact hroot.hOcc 76
  · exact hroot.hOcc 77
  · exact hroot.hOcc 81
  · change (∑ j, (-1 : Int) * x j) ≤ -plane361RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (7 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (0 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane361RankCoverGenLeaf0007Refs : Fin 25 → RowRef 86 24 := ![.occ 0, .occ 5, .occ 15, .occ 16, .occ 29, .occ 30, .occ 34, .occ 35, .occ 40, .occ 43, .occ 44, .occ 49, .occ 59, .occ 64, .occ 65, .occ 66, .occ 67, .occ 75, .occ 77, .occ 80, .occ 82, .sumGe, .branchGe 14 (1), .branchLe 2 (1), .branchLe 18 (0)]

def plane361RankCoverGenLeaf0007Mult : Fin 25 → Nat := ![1, 1, 3, 23, 8, 4, 7, 17, 5, 2, 3, 16, 2, 2, 15, 6, 1, 14, 8, 7, 1, 24, 45, 21, 22]

theorem plane361RankCoverGenLeaf0007 (x : Fin 24 → Int)
    (hroot : plane361RankCoverGenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hUB_2 : x 2 ≤ (1 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane361RankCoverGenLeaf0007Refs i).resolveCoeff plane361RankCoverGenOccSys j)
    (fun i => (plane361RankCoverGenLeaf0007Refs i).resolveRhs plane361RankCoverGenOccSys) plane361RankCoverGenLeaf0007Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane361RankCoverGenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 5
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 40
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 49
  · exact hroot.hOcc 59
  · exact hroot.hOcc 64
  · exact hroot.hOcc 65
  · exact hroot.hOcc 66
  · exact hroot.hOcc 67
  · exact hroot.hOcc 75
  · exact hroot.hOcc 77
  · exact hroot.hOcc 80
  · exact hroot.hOcc 82
  · change (∑ j, (-1 : Int) * x j) ≤ -plane361RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (2 : Fin 24) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (18 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane361RankCoverGenLeaf0008Refs : Fin 22 → RowRef 86 24 := ![.occ 8, .occ 16, .occ 24, .occ 29, .occ 32, .occ 35, .occ 38, .occ 39, .occ 45, .occ 49, .occ 51, .occ 56, .occ 63, .occ 67, .occ 68, .occ 72, .occ 75, .occ 80, .sumGe, .branchGe 14 (1), .branchLe 2 (1), .branchGe 18 (1)]

def plane361RankCoverGenLeaf0008Mult : Fin 22 → Nat := ![3, 15, 3, 12, 4, 5, 2, 9, 3, 13, 1, 13, 1, 10, 3, 3, 6, 4, 16, 46, 3, 21]

theorem plane361RankCoverGenLeaf0008 (x : Fin 24 → Int)
    (hroot : plane361RankCoverGenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hUB_2 : x 2 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane361RankCoverGenLeaf0008Refs i).resolveCoeff plane361RankCoverGenOccSys j)
    (fun i => (plane361RankCoverGenLeaf0008Refs i).resolveRhs plane361RankCoverGenOccSys) plane361RankCoverGenLeaf0008Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane361RankCoverGenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · exact hroot.hOcc 16
  · exact hroot.hOcc 24
  · exact hroot.hOcc 29
  · exact hroot.hOcc 32
  · exact hroot.hOcc 35
  · exact hroot.hOcc 38
  · exact hroot.hOcc 39
  · exact hroot.hOcc 45
  · exact hroot.hOcc 49
  · exact hroot.hOcc 51
  · exact hroot.hOcc 56
  · exact hroot.hOcc 63
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 72
  · exact hroot.hOcc 75
  · exact hroot.hOcc 80
  · change (∑ j, (-1 : Int) * x j) ≤ -plane361RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (2 : Fin 24) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (18 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane361RankCoverGenLeaf0009Refs : Fin 13 → RowRef 86 24 := ![.occ 16, .occ 41, .occ 49, .occ 55, .occ 56, .occ 60, .occ 75, .occ 80, .occ 84, .sumGe, .branchGe 14 (1), .branchGe 2 (2), .branchLe 7 (0)]

def plane361RankCoverGenLeaf0009Mult : Fin 13 → Nat := ![2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]

theorem plane361RankCoverGenLeaf0009 (x : Fin 24 → Int)
    (hroot : plane361RankCoverGenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_2 : (2 : Int) ≤ x 2)
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane361RankCoverGenLeaf0009Refs i).resolveCoeff plane361RankCoverGenOccSys j)
    (fun i => (plane361RankCoverGenLeaf0009Refs i).resolveRhs plane361RankCoverGenOccSys) plane361RankCoverGenLeaf0009Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane361RankCoverGenLeaf0009Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 16
  · exact hroot.hOcc 41
  · exact hroot.hOcc 49
  · exact hroot.hOcc 55
  · exact hroot.hOcc 56
  · exact hroot.hOcc 60
  · exact hroot.hOcc 75
  · exact hroot.hOcc 80
  · exact hroot.hOcc 84
  · change (∑ j, (-1 : Int) * x j) ≤ -plane361RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (2 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane361RankCoverGenLeaf0010Refs : Fin 24 → RowRef 86 24 := ![.occ 0, .occ 5, .occ 16, .occ 17, .occ 18, .occ 19, .occ 20, .occ 29, .occ 34, .occ 42, .occ 44, .occ 49, .occ 52, .occ 56, .occ 58, .occ 63, .occ 65, .occ 67, .occ 84, .occ 85, .sumGe, .branchGe 14 (1), .branchGe 2 (2), .branchGe 7 (1)]

def plane361RankCoverGenLeaf0010Mult : Fin 24 → Nat := ![7, 4, 3, 4, 2, 2, 4, 5, 3, 2, 3, 5, 3, 4, 3, 4, 1, 6, 1, 2, 10, 16, 15, 10]

theorem plane361RankCoverGenLeaf0010 (x : Fin 24 → Int)
    (hroot : plane361RankCoverGenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_2 : (2 : Int) ≤ x 2)
    (hLB_7 : (1 : Int) ≤ x 7)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane361RankCoverGenLeaf0010Refs i).resolveCoeff plane361RankCoverGenOccSys j)
    (fun i => (plane361RankCoverGenLeaf0010Refs i).resolveRhs plane361RankCoverGenOccSys) plane361RankCoverGenLeaf0010Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane361RankCoverGenLeaf0010Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 5
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 29
  · exact hroot.hOcc 34
  · exact hroot.hOcc 42
  · exact hroot.hOcc 44
  · exact hroot.hOcc 49
  · exact hroot.hOcc 52
  · exact hroot.hOcc 56
  · exact hroot.hOcc 58
  · exact hroot.hOcc 63
  · exact hroot.hOcc 65
  · exact hroot.hOcc 67
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · change (∑ j, (-1 : Int) * x j) ≤ -plane361RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (2 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7

end QiushiMatmul
