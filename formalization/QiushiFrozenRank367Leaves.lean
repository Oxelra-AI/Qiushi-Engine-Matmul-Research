import QiushiFrozenRank367Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane367RankCoverGenLeaf0000Refs : Fin 23 → RowRef 70 24 := ![.occ 0, .occ 1, .occ 3, .occ 4, .occ 6, .occ 19, .occ 20, .occ 21, .occ 29, .occ 32, .occ 36, .occ 40, .occ 41, .occ 44, .occ 46, .occ 48, .occ 52, .occ 59, .occ 60, .occ 65, .sumGe, .branchLe 12 (0), .branchLe 11 (0)]

def plane367RankCoverGenLeaf0000Mult : Fin 23 → Nat := ![8, 2, 2, 5, 1, 2, 5, 4, 4, 2, 4, 1, 1, 4, 3, 1, 4, 2, 1, 4, 10, 10, 7]

theorem plane367RankCoverGenLeaf0000 (x : Fin 24 → Int)
    (hroot : plane367RankCoverGenOccSys.RootHolds x)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane367RankCoverGenLeaf0000Refs i).resolveCoeff plane367RankCoverGenOccSys j)
    (fun i => (plane367RankCoverGenLeaf0000Refs i).resolveRhs plane367RankCoverGenOccSys) plane367RankCoverGenLeaf0000Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane367RankCoverGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 1
  · exact hroot.hOcc 3
  · exact hroot.hOcc 4
  · exact hroot.hOcc 6
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 29
  · exact hroot.hOcc 32
  · exact hroot.hOcc 36
  · exact hroot.hOcc 40
  · exact hroot.hOcc 41
  · exact hroot.hOcc 44
  · exact hroot.hOcc 46
  · exact hroot.hOcc 48
  · exact hroot.hOcc 52
  · exact hroot.hOcc 59
  · exact hroot.hOcc 60
  · exact hroot.hOcc 65
  · change (∑ j, (-1 : Int) * x j) ≤ -plane367RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (12 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (11 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane367RankCoverGenLeaf0001Refs : Fin 24 → RowRef 70 24 := ![.occ 0, .occ 1, .occ 9, .occ 19, .occ 20, .occ 22, .occ 27, .occ 34, .occ 36, .occ 42, .occ 44, .occ 48, .occ 52, .occ 53, .occ 54, .occ 57, .occ 58, .occ 65, .occ 68, .sumGe, .nonneg 16, .branchLe 12 (0), .branchGe 11 (1), .branchLe 3 (1)]

def plane367RankCoverGenLeaf0001Mult : Fin 24 → Nat := ![10, 6, 1, 1, 6, 2, 7, 3, 3, 1, 1, 1, 3, 2, 2, 1, 5, 5, 3, 11, 6, 10, 9, 4]

theorem plane367RankCoverGenLeaf0001 (x : Fin 24 → Int)
    (hroot : plane367RankCoverGenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane367RankCoverGenLeaf0001Refs i).resolveCoeff plane367RankCoverGenOccSys j)
    (fun i => (plane367RankCoverGenLeaf0001Refs i).resolveRhs plane367RankCoverGenOccSys) plane367RankCoverGenLeaf0001Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane367RankCoverGenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 1
  · exact hroot.hOcc 9
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 22
  · exact hroot.hOcc 27
  · exact hroot.hOcc 34
  · exact hroot.hOcc 36
  · exact hroot.hOcc 42
  · exact hroot.hOcc 44
  · exact hroot.hOcc 48
  · exact hroot.hOcc 52
  · exact hroot.hOcc 53
  · exact hroot.hOcc 54
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 65
  · exact hroot.hOcc 68
  · change (∑ j, (-1 : Int) * x j) ≤ -plane367RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 24) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (12 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (11 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (3 : Fin 24) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_3

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane367RankCoverGenLeaf0002Refs : Fin 21 → RowRef 70 24 := ![.occ 0, .occ 1, .occ 6, .occ 15, .occ 16, .occ 17, .occ 18, .occ 22, .occ 24, .occ 30, .occ 32, .occ 38, .occ 44, .occ 48, .occ 50, .occ 57, .occ 64, .sumGe, .branchLe 12 (0), .branchGe 11 (1), .branchGe 3 (2)]

def plane367RankCoverGenLeaf0002Mult : Fin 21 → Nat := ![1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 3, 10]

theorem plane367RankCoverGenLeaf0002 (x : Fin 24 → Int)
    (hroot : plane367RankCoverGenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_3 : (2 : Int) ≤ x 3)
    (hUB_12 : x 12 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane367RankCoverGenLeaf0002Refs i).resolveCoeff plane367RankCoverGenOccSys j)
    (fun i => (plane367RankCoverGenLeaf0002Refs i).resolveRhs plane367RankCoverGenOccSys) plane367RankCoverGenLeaf0002Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane367RankCoverGenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 1
  · exact hroot.hOcc 6
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 22
  · exact hroot.hOcc 24
  · exact hroot.hOcc 30
  · exact hroot.hOcc 32
  · exact hroot.hOcc 38
  · exact hroot.hOcc 44
  · exact hroot.hOcc 48
  · exact hroot.hOcc 50
  · exact hroot.hOcc 57
  · exact hroot.hOcc 64
  · change (∑ j, (-1 : Int) * x j) ≤ -plane367RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (12 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (11 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (3 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane367RankCoverGenLeaf0003Refs : Fin 25 → RowRef 70 24 := ![.occ 0, .occ 1, .occ 3, .occ 4, .occ 5, .occ 19, .occ 20, .occ 22, .occ 28, .occ 29, .occ 35, .occ 36, .occ 42, .occ 43, .occ 44, .occ 52, .occ 56, .occ 59, .occ 62, .occ 63, .occ 65, .occ 67, .sumGe, .nonneg 16, .branchLe 15 (0)]

def plane367RankCoverGenLeaf0003Mult : Fin 25 → Nat := ![94, 84, 24, 4, 2, 38, 60, 40, 30, 50, 11, 43, 27, 19, 38, 21, 19, 58, 3, 43, 44, 20, 144, 22, 144]

theorem plane367RankCoverGenLeaf0003 (x : Fin 24 → Int)
    (hroot : plane367RankCoverGenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hUB_15 : x 15 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane367RankCoverGenLeaf0003Refs i).resolveCoeff plane367RankCoverGenOccSys j)
    (fun i => (plane367RankCoverGenLeaf0003Refs i).resolveRhs plane367RankCoverGenOccSys) plane367RankCoverGenLeaf0003Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane367RankCoverGenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 1
  · exact hroot.hOcc 3
  · exact hroot.hOcc 4
  · exact hroot.hOcc 5
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 22
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 35
  · exact hroot.hOcc 36
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 52
  · exact hroot.hOcc 56
  · exact hroot.hOcc 59
  · exact hroot.hOcc 62
  · exact hroot.hOcc 63
  · exact hroot.hOcc 65
  · exact hroot.hOcc 67
  · change (∑ j, (-1 : Int) * x j) ≤ -plane367RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 24) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (15 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane367RankCoverGenLeaf0004Refs : Fin 23 → RowRef 70 24 := ![.occ 0, .occ 1, .occ 6, .occ 19, .occ 20, .occ 22, .occ 23, .occ 27, .occ 28, .occ 33, .occ 34, .occ 37, .occ 41, .occ 42, .occ 44, .occ 48, .occ 56, .occ 63, .occ 65, .occ 67, .sumGe, .branchGe 12 (1), .branchLe 9 (0)]

def plane367RankCoverGenLeaf0004Mult : Fin 23 → Nat := ![5, 7, 4, 12, 2, 2, 2, 5, 3, 7, 4, 1, 3, 9, 9, 6, 8, 8, 2, 5, 22, 4, 22]

theorem plane367RankCoverGenLeaf0004 (x : Fin 24 → Int)
    (hroot : plane367RankCoverGenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane367RankCoverGenLeaf0004Refs i).resolveCoeff plane367RankCoverGenOccSys j)
    (fun i => (plane367RankCoverGenLeaf0004Refs i).resolveRhs plane367RankCoverGenOccSys) plane367RankCoverGenLeaf0004Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane367RankCoverGenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 1
  · exact hroot.hOcc 6
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 37
  · exact hroot.hOcc 41
  · exact hroot.hOcc 42
  · exact hroot.hOcc 44
  · exact hroot.hOcc 48
  · exact hroot.hOcc 56
  · exact hroot.hOcc 63
  · exact hroot.hOcc 65
  · exact hroot.hOcc 67
  · change (∑ j, (-1 : Int) * x j) ≤ -plane367RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (12 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (9 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane367RankCoverGenLeaf0005Refs : Fin 19 → RowRef 70 24 := ![.occ 0, .occ 9, .occ 20, .occ 27, .occ 28, .occ 31, .occ 34, .occ 39, .occ 43, .occ 45, .occ 49, .occ 56, .occ 61, .sumGe, .nonneg 18, .branchGe 12 (1), .branchGe 15 (1), .branchLe 10 (0), .branchLe 14 (0)]

def plane367RankCoverGenLeaf0005Mult : Fin 19 → Nat := ![2, 2, 2, 4, 4, 1, 3, 2, 1, 1, 2, 1, 3, 4, 2, 6, 4, 4, 4]

theorem plane367RankCoverGenLeaf0005 (x : Fin 24 → Int)
    (hroot : plane367RankCoverGenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane367RankCoverGenLeaf0005Refs i).resolveCoeff plane367RankCoverGenOccSys j)
    (fun i => (plane367RankCoverGenLeaf0005Refs i).resolveRhs plane367RankCoverGenOccSys) plane367RankCoverGenLeaf0005Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane367RankCoverGenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 9
  · exact hroot.hOcc 20
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 31
  · exact hroot.hOcc 34
  · exact hroot.hOcc 39
  · exact hroot.hOcc 43
  · exact hroot.hOcc 45
  · exact hroot.hOcc 49
  · exact hroot.hOcc 56
  · exact hroot.hOcc 61
  · change (∑ j, (-1 : Int) * x j) ≤ -plane367RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 24) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (12 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (15 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (10 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (14 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane367RankCoverGenLeaf0006Refs : Fin 25 → RowRef 70 24 := ![.occ 0, .occ 1, .occ 2, .occ 20, .occ 29, .occ 32, .occ 34, .occ 36, .occ 42, .occ 43, .occ 48, .occ 49, .occ 52, .occ 55, .occ 61, .occ 62, .occ 63, .occ 65, .sumGe, .nonneg 18, .nonneg 20, .branchGe 12 (1), .branchGe 15 (1), .branchLe 10 (0), .branchGe 14 (1)]

def plane367RankCoverGenLeaf0006Mult : Fin 25 → Nat := ![4, 4, 19, 10, 14, 3, 2, 1, 26, 4, 13, 9, 6, 4, 19, 4, 17, 7, 34, 18, 19, 45, 13, 29, 30]

theorem plane367RankCoverGenLeaf0006 (x : Fin 24 → Int)
    (hroot : plane367RankCoverGenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hUB_10 : x 10 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane367RankCoverGenLeaf0006Refs i).resolveCoeff plane367RankCoverGenOccSys j)
    (fun i => (plane367RankCoverGenLeaf0006Refs i).resolveRhs plane367RankCoverGenOccSys) plane367RankCoverGenLeaf0006Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane367RankCoverGenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 1
  · exact hroot.hOcc 2
  · exact hroot.hOcc 20
  · exact hroot.hOcc 29
  · exact hroot.hOcc 32
  · exact hroot.hOcc 34
  · exact hroot.hOcc 36
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 48
  · exact hroot.hOcc 49
  · exact hroot.hOcc 52
  · exact hroot.hOcc 55
  · exact hroot.hOcc 61
  · exact hroot.hOcc 62
  · exact hroot.hOcc 63
  · exact hroot.hOcc 65
  · change (∑ j, (-1 : Int) * x j) ≤ -plane367RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 24) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (20 : Fin 24) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (12 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (15 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (10 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (14 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane367RankCoverGenLeaf0007Refs : Fin 23 → RowRef 70 24 := ![.occ 0, .occ 4, .occ 23, .occ 26, .occ 27, .occ 28, .occ 41, .occ 42, .occ 47, .occ 48, .occ 52, .occ 56, .occ 58, .occ 61, .occ 67, .occ 68, .occ 69, .sumGe, .branchGe 12 (1), .branchGe 15 (1), .branchGe 10 (1), .branchLe 4 (0), .branchLe 0 (0)]

def plane367RankCoverGenLeaf0007Mult : Fin 23 → Nat := ![1, 3, 4, 2, 2, 8, 8, 2, 1, 4, 6, 4, 3, 5, 3, 5, 4, 14, 8, 2, 9, 10, 14]

theorem plane367RankCoverGenLeaf0007 (x : Fin 24 → Int)
    (hroot : plane367RankCoverGenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_0 : x 0 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane367RankCoverGenLeaf0007Refs i).resolveCoeff plane367RankCoverGenOccSys j)
    (fun i => (plane367RankCoverGenLeaf0007Refs i).resolveRhs plane367RankCoverGenOccSys) plane367RankCoverGenLeaf0007Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane367RankCoverGenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 4
  · exact hroot.hOcc 23
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 41
  · exact hroot.hOcc 42
  · exact hroot.hOcc 47
  · exact hroot.hOcc 48
  · exact hroot.hOcc 52
  · exact hroot.hOcc 56
  · exact hroot.hOcc 58
  · exact hroot.hOcc 61
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 69
  · change (∑ j, (-1 : Int) * x j) ≤ -plane367RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (12 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (15 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (10 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (4 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (0 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane367RankCoverGenLeaf0008Refs : Fin 24 → RowRef 70 24 := ![.occ 0, .occ 1, .occ 22, .occ 25, .occ 27, .occ 28, .occ 34, .occ 36, .occ 38, .occ 49, .occ 51, .occ 56, .occ 62, .occ 64, .occ 65, .occ 66, .occ 67, .occ 68, .sumGe, .nonneg 21, .branchGe 9 (1), .branchGe 10 (1), .branchLe 4 (0), .branchGe 0 (1)]

def plane367RankCoverGenLeaf0008Mult : Fin 24 → Nat := ![20, 20, 4, 2, 4, 4, 12, 20, 2, 2, 4, 2, 3, 13, 6, 12, 3, 3, 28, 8, 22, 32, 12, 38]

theorem plane367RankCoverGenLeaf0008 (x : Fin 24 → Int)
    (hroot : plane367RankCoverGenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hUB_4 : x 4 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane367RankCoverGenLeaf0008Refs i).resolveCoeff plane367RankCoverGenOccSys j)
    (fun i => (plane367RankCoverGenLeaf0008Refs i).resolveRhs plane367RankCoverGenOccSys) plane367RankCoverGenLeaf0008Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane367RankCoverGenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 1
  · exact hroot.hOcc 22
  · exact hroot.hOcc 25
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 34
  · exact hroot.hOcc 36
  · exact hroot.hOcc 38
  · exact hroot.hOcc 49
  · exact hroot.hOcc 51
  · exact hroot.hOcc 56
  · exact hroot.hOcc 62
  · exact hroot.hOcc 64
  · exact hroot.hOcc 65
  · exact hroot.hOcc 66
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · change (∑ j, (-1 : Int) * x j) ≤ -plane367RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (21 : Fin 24) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (9 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (10 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (4 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (0 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane367RankCoverGenLeaf0009Refs : Fin 23 → RowRef 70 24 := ![.occ 1, .occ 3, .occ 17, .occ 19, .occ 20, .occ 22, .occ 34, .occ 36, .occ 41, .occ 42, .occ 46, .occ 48, .occ 61, .occ 66, .occ 67, .occ 69, .sumGe, .nonneg 18, .nonneg 22, .branchGe 12 (1), .branchGe 15 (1), .branchGe 10 (1), .branchGe 4 (1)]

def plane367RankCoverGenLeaf0009Mult : Fin 23 → Nat := ![1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 9, 4]

theorem plane367RankCoverGenLeaf0009 (x : Fin 24 → Int)
    (hroot : plane367RankCoverGenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_4 : (1 : Int) ≤ x 4)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane367RankCoverGenLeaf0009Refs i).resolveCoeff plane367RankCoverGenOccSys j)
    (fun i => (plane367RankCoverGenLeaf0009Refs i).resolveRhs plane367RankCoverGenOccSys) plane367RankCoverGenLeaf0009Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane367RankCoverGenLeaf0009Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · exact hroot.hOcc 3
  · exact hroot.hOcc 17
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 22
  · exact hroot.hOcc 34
  · exact hroot.hOcc 36
  · exact hroot.hOcc 41
  · exact hroot.hOcc 42
  · exact hroot.hOcc 46
  · exact hroot.hOcc 48
  · exact hroot.hOcc 61
  · exact hroot.hOcc 66
  · exact hroot.hOcc 67
  · exact hroot.hOcc 69
  · change (∑ j, (-1 : Int) * x j) ≤ -plane367RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 24) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (22 : Fin 24) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (12 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (15 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (10 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (4 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
