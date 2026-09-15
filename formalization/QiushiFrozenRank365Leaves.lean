import QiushiFrozenRank365Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane365RankCoverGenLeaf0000Refs : Fin 20 → RowRef 52 23 := ![.occ 0, .occ 2, .occ 3, .occ 7, .occ 15, .occ 16, .occ 17, .occ 19, .occ 23, .occ 26, .occ 29, .occ 31, .occ 40, .occ 41, .occ 45, .occ 46, .sumGe, .nonneg 14, .branchLe 20 (0), .branchLe 15 (0)]

def plane365RankCoverGenLeaf0000Mult : Fin 20 → Nat := ![4, 4, 2, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 4]

theorem plane365RankCoverGenLeaf0000 (x : Fin 23 → Int)
    (hroot : plane365RankCoverGenOccSys.RootHolds x)
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane365RankCoverGenLeaf0000Refs i).resolveCoeff plane365RankCoverGenOccSys j)
    (fun i => (plane365RankCoverGenLeaf0000Refs i).resolveRhs plane365RankCoverGenOccSys) plane365RankCoverGenLeaf0000Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane365RankCoverGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 2
  · exact hroot.hOcc 3
  · exact hroot.hOcc 7
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 19
  · exact hroot.hOcc 23
  · exact hroot.hOcc 26
  · exact hroot.hOcc 29
  · exact hroot.hOcc 31
  · exact hroot.hOcc 40
  · exact hroot.hOcc 41
  · exact hroot.hOcc 45
  · exact hroot.hOcc 46
  · change (∑ j, (-1 : Int) * x j) ≤ -plane365RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 23) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (20 : Fin 23) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (15 : Fin 23) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane365RankCoverGenLeaf0001Refs : Fin 24 → RowRef 52 23 := ![.occ 0, .occ 2, .occ 6, .occ 7, .occ 15, .occ 16, .occ 19, .occ 25, .occ 28, .occ 29, .occ 31, .occ 32, .occ 33, .occ 35, .occ 36, .occ 37, .occ 39, .occ 42, .occ 43, .occ 45, .occ 50, .sumGe, .branchLe 20 (0), .branchGe 15 (1)]

def plane365RankCoverGenLeaf0001Mult : Fin 24 → Nat := ![1, 7, 14, 2, 14, 8, 19, 34, 3, 16, 5, 13, 16, 22, 16, 2, 20, 4, 7, 2, 1, 39, 39, 58]

theorem plane365RankCoverGenLeaf0001 (x : Fin 23 → Int)
    (hroot : plane365RankCoverGenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hUB_20 : x 20 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane365RankCoverGenLeaf0001Refs i).resolveCoeff plane365RankCoverGenOccSys j)
    (fun i => (plane365RankCoverGenLeaf0001Refs i).resolveRhs plane365RankCoverGenOccSys) plane365RankCoverGenLeaf0001Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane365RankCoverGenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 2
  · exact hroot.hOcc 6
  · exact hroot.hOcc 7
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 19
  · exact hroot.hOcc 25
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 31
  · exact hroot.hOcc 32
  · exact hroot.hOcc 33
  · exact hroot.hOcc 35
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 39
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 45
  · exact hroot.hOcc 50
  · change (∑ j, (-1 : Int) * x j) ≤ -plane365RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (20 : Fin 23) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (15 : Fin 23) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane365RankCoverGenLeaf0002Refs : Fin 24 → RowRef 52 23 := ![.occ 0, .occ 4, .occ 6, .occ 7, .occ 18, .occ 20, .occ 22, .occ 27, .occ 29, .occ 32, .occ 35, .occ 38, .occ 41, .occ 42, .occ 44, .occ 45, .occ 46, .occ 48, .occ 49, .occ 51, .sumGe, .nonneg 4, .branchGe 20 (1), .branchLe 12 (0)]

def plane365RankCoverGenLeaf0002Mult : Fin 24 → Nat := ![58, 35, 10, 52, 31, 15, 19, 21, 5, 6, 13, 29, 20, 4, 36, 14, 11, 14, 21, 1, 71, 5, 96, 25]

theorem plane365RankCoverGenLeaf0002 (x : Fin 23 → Int)
    (hroot : plane365RankCoverGenOccSys.RootHolds x)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hUB_12 : x 12 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane365RankCoverGenLeaf0002Refs i).resolveCoeff plane365RankCoverGenOccSys j)
    (fun i => (plane365RankCoverGenLeaf0002Refs i).resolveRhs plane365RankCoverGenOccSys) plane365RankCoverGenLeaf0002Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane365RankCoverGenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 4
  · exact hroot.hOcc 6
  · exact hroot.hOcc 7
  · exact hroot.hOcc 18
  · exact hroot.hOcc 20
  · exact hroot.hOcc 22
  · exact hroot.hOcc 27
  · exact hroot.hOcc 29
  · exact hroot.hOcc 32
  · exact hroot.hOcc 35
  · exact hroot.hOcc 38
  · exact hroot.hOcc 41
  · exact hroot.hOcc 42
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 46
  · exact hroot.hOcc 48
  · exact hroot.hOcc 49
  · exact hroot.hOcc 51
  · change (∑ j, (-1 : Int) * x j) ≤ -plane365RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 23) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (20 : Fin 23) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (12 : Fin 23) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane365RankCoverGenLeaf0003Refs : Fin 21 → RowRef 52 23 := ![.occ 0, .occ 4, .occ 6, .occ 7, .occ 14, .occ 15, .occ 18, .occ 21, .occ 22, .occ 24, .occ 30, .occ 34, .occ 35, .occ 46, .occ 47, .occ 49, .occ 51, .sumGe, .nonneg 14, .branchGe 20 (1), .branchGe 12 (1)]

def plane365RankCoverGenLeaf0003Mult : Fin 21 → Nat := ![1, 2, 3, 5, 3, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 6, 6]

theorem plane365RankCoverGenLeaf0003 (x : Fin 23 → Int)
    (hroot : plane365RankCoverGenOccSys.RootHolds x)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_12 : (1 : Int) ≤ x 12)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane365RankCoverGenLeaf0003Refs i).resolveCoeff plane365RankCoverGenOccSys j)
    (fun i => (plane365RankCoverGenLeaf0003Refs i).resolveRhs plane365RankCoverGenOccSys) plane365RankCoverGenLeaf0003Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane365RankCoverGenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 4
  · exact hroot.hOcc 6
  · exact hroot.hOcc 7
  · exact hroot.hOcc 14
  · exact hroot.hOcc 15
  · exact hroot.hOcc 18
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 24
  · exact hroot.hOcc 30
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 46
  · exact hroot.hOcc 47
  · exact hroot.hOcc 49
  · exact hroot.hOcc 51
  · change (∑ j, (-1 : Int) * x j) ≤ -plane365RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 23) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (20 : Fin 23) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (12 : Fin 23) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
