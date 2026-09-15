import QiushiFrozenRank362Leaves
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane362RankCoverGenNoModel (x : Fin 24 → Int) (hroot : plane362RankCoverGenOccSys.RootHolds x) : False := by
  exact plane362RankCoverGenLeaf0000 x hroot

end QiushiMatmul
