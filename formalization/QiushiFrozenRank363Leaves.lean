import QiushiFrozenRank363Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane363RankCoverGenLeaf0000Refs : Fin 13 → RowRef 33 19 := ![.occ 2, .occ 4, .occ 17, .occ 20, .occ 21, .occ 25, .occ 26, .occ 27, .occ 32, .sumGe, .branchLe 0 (1), .branchLe 4 (0), .branchLe 1 (1)]

def plane363RankCoverGenLeaf0000Mult : Fin 13 → Nat := ![1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2]

theorem plane363RankCoverGenLeaf0000 (x : Fin 19 → Int)
    (hroot : plane363RankCoverGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (1 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane363RankCoverGenLeaf0000Refs i).resolveCoeff plane363RankCoverGenOccSys j)
    (fun i => (plane363RankCoverGenLeaf0000Refs i).resolveRhs plane363RankCoverGenOccSys) plane363RankCoverGenLeaf0000Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane363RankCoverGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 4
  · exact hroot.hOcc 17
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 32
  · change (∑ j, (-1 : Int) * x j) ≤ -plane363RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 19) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (4 : Fin 19) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (1 : Fin 19) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_1

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane363RankCoverGenLeaf0001Refs : Fin 13 → RowRef 33 19 := ![.occ 2, .occ 3, .occ 4, .occ 15, .occ 18, .occ 21, .occ 23, .occ 26, .occ 27, .occ 28, .occ 31, .sumGe, .branchGe 1 (2)]

def plane363RankCoverGenLeaf0001Mult : Fin 13 → Nat := ![3, 2, 1, 3, 2, 2, 2, 1, 2, 1, 1, 3, 3]

theorem plane363RankCoverGenLeaf0001 (x : Fin 19 → Int)
    (hroot : plane363RankCoverGenOccSys.RootHolds x)
    (hLB_1 : (2 : Int) ≤ x 1)
    (hUB_0 : x 0 ≤ (1 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane363RankCoverGenLeaf0001Refs i).resolveCoeff plane363RankCoverGenOccSys j)
    (fun i => (plane363RankCoverGenLeaf0001Refs i).resolveRhs plane363RankCoverGenOccSys) plane363RankCoverGenLeaf0001Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane363RankCoverGenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 3
  · exact hroot.hOcc 4
  · exact hroot.hOcc 15
  · exact hroot.hOcc 18
  · exact hroot.hOcc 21
  · exact hroot.hOcc 23
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 31
  · change (∑ j, (-1 : Int) * x j) ≤ -plane363RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 19) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane363RankCoverGenLeaf0002Refs : Fin 10 → RowRef 33 19 := ![.occ 3, .occ 4, .occ 16, .occ 20, .occ 24, .occ 27, .occ 29, .sumGe, .branchLe 0 (1), .branchGe 4 (1)]

def plane363RankCoverGenLeaf0002Mult : Fin 10 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 2]

theorem plane363RankCoverGenLeaf0002 (x : Fin 19 → Int)
    (hroot : plane363RankCoverGenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_0 : x 0 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane363RankCoverGenLeaf0002Refs i).resolveCoeff plane363RankCoverGenOccSys j)
    (fun i => (plane363RankCoverGenLeaf0002Refs i).resolveRhs plane363RankCoverGenOccSys) plane363RankCoverGenLeaf0002Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane363RankCoverGenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 4
  · exact hroot.hOcc 16
  · exact hroot.hOcc 20
  · exact hroot.hOcc 24
  · exact hroot.hOcc 27
  · exact hroot.hOcc 29
  · change (∑ j, (-1 : Int) * x j) ≤ -plane363RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 19) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (4 : Fin 19) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane363RankCoverGenLeaf0003Refs : Fin 13 → RowRef 33 19 := ![.occ 2, .occ 3, .occ 4, .occ 15, .occ 18, .occ 20, .occ 22, .occ 27, .occ 28, .occ 29, .occ 30, .sumGe, .branchGe 0 (2)]

def plane363RankCoverGenLeaf0003Mult : Fin 13 → Nat := ![1, 3, 2, 3, 2, 2, 2, 2, 1, 1, 1, 3, 3]

theorem plane363RankCoverGenLeaf0003 (x : Fin 19 → Int)
    (hroot : plane363RankCoverGenOccSys.RootHolds x)
    (hLB_0 : (2 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane363RankCoverGenLeaf0003Refs i).resolveCoeff plane363RankCoverGenOccSys j)
    (fun i => (plane363RankCoverGenLeaf0003Refs i).resolveRhs plane363RankCoverGenOccSys) plane363RankCoverGenLeaf0003Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane363RankCoverGenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 3
  · exact hroot.hOcc 4
  · exact hroot.hOcc 15
  · exact hroot.hOcc 18
  · exact hroot.hOcc 20
  · exact hroot.hOcc 22
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · change (∑ j, (-1 : Int) * x j) ≤ -plane363RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 19) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
