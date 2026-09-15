import QiushiFrozenRank367Leaves
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane367RankCoverGenNoModel (x : Fin 24 → Int) (hroot : plane367RankCoverGenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 12 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 11 ≤ (0 : Int)
    ·
      exact plane367RankCoverGenLeaf0000 x hroot (by omega) (by omega)
    ·
      by_cases hbranch_LR : x 3 ≤ (1 : Int)
      ·
        exact plane367RankCoverGenLeaf0001 x hroot (by omega) (by omega) (by omega)
      ·
        exact plane367RankCoverGenLeaf0002 x hroot (by omega) (by omega) (by omega)
  ·
    by_cases hbranch_R : x 15 ≤ (0 : Int)
    ·
      exact plane367RankCoverGenLeaf0003 x hroot (by omega) (by omega)
    ·
      by_cases hbranch_RR : x 9 ≤ (0 : Int)
      ·
        exact plane367RankCoverGenLeaf0004 x hroot (by omega) (by omega) (by omega)
      ·
        by_cases hbranch_RRR : x 10 ≤ (0 : Int)
        ·
          by_cases hbranch_RRRL : x 14 ≤ (0 : Int)
          ·
            exact plane367RankCoverGenLeaf0005 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane367RankCoverGenLeaf0006 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_RRRR : x 4 ≤ (0 : Int)
          ·
            by_cases hbranch_RRRRL : x 0 ≤ (0 : Int)
            ·
              exact plane367RankCoverGenLeaf0007 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            ·
              exact plane367RankCoverGenLeaf0008 x hroot (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane367RankCoverGenLeaf0009 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)

end QiushiMatmul
