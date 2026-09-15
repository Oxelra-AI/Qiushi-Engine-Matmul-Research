import QiushiFrozenRank363Leaves
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane363RankCoverGenNoModel (x : Fin 19 → Int) (hroot : plane363RankCoverGenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 0 ≤ (1 : Int)
  ·
    by_cases hbranch_L : x 4 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 1 ≤ (1 : Int)
      ·
        exact plane363RankCoverGenLeaf0000 x hroot (by omega) (by omega) (by omega)
      ·
        exact plane363RankCoverGenLeaf0001 x hroot (by omega) (by omega) (by omega)
    ·
      exact plane363RankCoverGenLeaf0002 x hroot (by omega) (by omega)
  ·
    exact plane363RankCoverGenLeaf0003 x hroot (by omega)

end QiushiMatmul
