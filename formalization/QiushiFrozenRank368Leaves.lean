import QiushiFrozenRank368Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane368RankCoverGenLeaf0000Refs : Fin 14 → RowRef 25 20 := ![.occ 0, .occ 2, .occ 10, .occ 14, .occ 15, .occ 16, .occ 17, .occ 19, .occ 20, .occ 21, .occ 22, .occ 23, .occ 24, .sumGe]

def plane368RankCoverGenLeaf0000Mult : Fin 14 → Nat := ![1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2]

theorem plane368RankCoverGenLeaf0000 (x : Fin 20 → Int)
    (hroot : plane368RankCoverGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane368RankCoverGenLeaf0000Refs i).resolveCoeff plane368RankCoverGenOccSys j)
    (fun i => (plane368RankCoverGenLeaf0000Refs i).resolveRhs plane368RankCoverGenOccSys) plane368RankCoverGenLeaf0000Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane368RankCoverGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 2
  · exact hroot.hOcc 10
  · exact hroot.hOcc 14
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · change (∑ j, (-1 : Int) * x j) ≤ -plane368RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
