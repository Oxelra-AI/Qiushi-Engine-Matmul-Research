import QiushiFrozenRank369Leaves
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane369RankCoverGenNoModel (x : Fin 23 → Int) (hroot : plane369RankCoverGenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 13 ≤ (0 : Int)
  ·
    exact plane369RankCoverGenLeaf0000 x hroot (by omega)
  ·
    exact plane369RankCoverGenLeaf0001 x hroot (by omega)

end QiushiMatmul
