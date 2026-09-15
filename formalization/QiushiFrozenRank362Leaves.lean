import QiushiFrozenRank362Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane362RankCoverGenLeaf0000Refs : Fin 25 → RowRef 31 24 := ![.occ 0, .occ 3, .occ 7, .occ 10, .occ 11, .occ 12, .occ 13, .occ 14, .occ 15, .occ 16, .occ 17, .occ 18, .occ 19, .occ 20, .occ 21, .occ 22, .occ 23, .occ 24, .occ 25, .occ 26, .occ 27, .occ 28, .occ 29, .occ 30, .sumGe]

def plane362RankCoverGenLeaf0000Mult : Fin 25 → Nat := ![45, 63, 76, 95, 95, 13, 18, 38, 16, 38, 16, 13, 7, 62, 4, 24, 30, 4, 4, 7, 7, 6, 4, 30, 99]

theorem plane362RankCoverGenLeaf0000 (x : Fin 24 → Int)
    (hroot : plane362RankCoverGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane362RankCoverGenLeaf0000Refs i).resolveCoeff plane362RankCoverGenOccSys j)
    (fun i => (plane362RankCoverGenLeaf0000Refs i).resolveRhs plane362RankCoverGenOccSys) plane362RankCoverGenLeaf0000Mult
    (by decide +kernel) (by decide +kernel) x
  intro i; fin_cases i <;> simp only [plane362RankCoverGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 3
  · exact hroot.hOcc 7
  · exact hroot.hOcc 10
  · exact hroot.hOcc 11
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · change (∑ j, (-1 : Int) * x j) ≤ -plane362RankCoverGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
