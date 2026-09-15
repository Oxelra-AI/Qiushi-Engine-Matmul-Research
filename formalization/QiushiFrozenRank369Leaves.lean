import QiushiFrozenRank369Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane369RankCoverGenLeaf0000Refs : Fin 22 → RowRef 37 23 := ![.occ 0, .occ 3, .occ 4, .occ 12, .occ 13, .occ 14, .occ 16, .occ 17, .occ 19, .occ 21, .occ 22, .occ 24, .occ 25, .occ 26, .occ 27, .occ 29, .occ 30, .occ 31, .occ 33, .occ 35, .sumGe, .branchLe 13 (0)]

def plane369RankCoverGenLeaf0000Mult : Fin 22 → Nat := ![1, 2, 4, 6, 2, 2, 1, 2, 1, 3, 2, 1, 2, 4, 1, 1, 3, 1, 1, 1, 7, 5]

theorem plane369RankCoverGenLeaf0000 (x : Fin 23 → Int)
    (hroot : plane369RankCoverGenOccSys.RootHolds x)
    (hUB_13 : x 13 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane369RankCoverGenLeaf0000Refs i).resolveCoeff plane369RankCoverGenOccSys j)
    (fun i => (plane369RankCoverGenLeaf0000Refs i).resolveRhs plane369RankCoverGenOccSys) plane369RankCoverGenLeaf0000Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane369RankCoverGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 3
  · exact hroot.hOcc 4
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 19
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 33
  · exact hroot.hOcc 35
  · change (∑ j, (-1 : Int) * x j) ≤ -plane369RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 23) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13

end QiushiMatmul

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane369RankCoverGenLeaf0001Refs : Fin 20 → RowRef 37 23 := ![.occ 2, .occ 4, .occ 12, .occ 15, .occ 17, .occ 18, .occ 19, .occ 20, .occ 21, .occ 23, .occ 24, .occ 26, .occ 28, .occ 29, .occ 30, .occ 32, .occ 34, .occ 36, .sumGe, .branchGe 13 (1)]

def plane369RankCoverGenLeaf0001Mult : Fin 20 → Nat := ![2, 4, 2, 1, 2, 1, 3, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 2, 5, 10]

theorem plane369RankCoverGenLeaf0001 (x : Fin 23 → Int)
    (hroot : plane369RankCoverGenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane369RankCoverGenLeaf0001Refs i).resolveCoeff plane369RankCoverGenOccSys j)
    (fun i => (plane369RankCoverGenLeaf0001Refs i).resolveRhs plane369RankCoverGenOccSys) plane369RankCoverGenLeaf0001Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane369RankCoverGenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 4
  · exact hroot.hOcc 12
  · exact hroot.hOcc 15
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 26
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 32
  · exact hroot.hOcc 34
  · exact hroot.hOcc 36
  · change (∑ j, (-1 : Int) * x j) ≤ -plane369RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 23) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
