import QiushiFrozenRank365Leaves
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane365RankCoverGenNoModel (x : Fin 23 → Int) (hroot : plane365RankCoverGenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 20 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 15 ≤ (0 : Int)
    ·
      exact plane365RankCoverGenLeaf0000 x hroot (by omega) (by omega)
    ·
      exact plane365RankCoverGenLeaf0001 x hroot (by omega) (by omega)
  ·
    by_cases hbranch_R : x 12 ≤ (0 : Int)
    ·
      exact plane365RankCoverGenLeaf0002 x hroot (by omega) (by omega)
    ·
      exact plane365RankCoverGenLeaf0003 x hroot (by omega) (by omega)

end QiushiMatmul
