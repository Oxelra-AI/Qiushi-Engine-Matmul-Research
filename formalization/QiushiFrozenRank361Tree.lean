import QiushiFrozenRank361Leaves
set_option maxHeartbeats 8000000
namespace QiushiMatmul

theorem plane361RankCoverGenNoModel (x : Fin 24 → Int) (hroot : plane361RankCoverGenOccSys.RootHolds x) : False := by
  by_cases hbranch_root : x 14 ≤ (0 : Int)
  ·
    by_cases hbranch_L : x 7 ≤ (0 : Int)
    ·
      by_cases hbranch_LL : x 5 ≤ (1 : Int)
      ·
        by_cases hbranch_LLL : x 6 ≤ (0 : Int)
        ·
          by_cases hbranch_LLLL : x 0 ≤ (0 : Int)
          ·
            exact plane361RankCoverGenLeaf0000 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane361RankCoverGenLeaf0001 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
        ·
          by_cases hbranch_LLLR : x 15 ≤ (0 : Int)
          ·
            exact plane361RankCoverGenLeaf0002 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
          ·
            exact plane361RankCoverGenLeaf0003 x hroot (by omega) (by omega) (by omega) (by omega) (by omega)
      ·
        exact plane361RankCoverGenLeaf0004 x hroot (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_LR : x 0 ≤ (0 : Int)
      ·
        exact plane361RankCoverGenLeaf0005 x hroot (by omega) (by omega) (by omega)
      ·
        exact plane361RankCoverGenLeaf0006 x hroot (by omega) (by omega) (by omega)
  ·
    by_cases hbranch_R : x 2 ≤ (1 : Int)
    ·
      by_cases hbranch_RL : x 18 ≤ (0 : Int)
      ·
        exact plane361RankCoverGenLeaf0007 x hroot (by omega) (by omega) (by omega)
      ·
        exact plane361RankCoverGenLeaf0008 x hroot (by omega) (by omega) (by omega)
    ·
      by_cases hbranch_RR : x 7 ≤ (0 : Int)
      ·
        exact plane361RankCoverGenLeaf0009 x hroot (by omega) (by omega) (by omega)
      ·
        exact plane361RankCoverGenLeaf0010 x hroot (by omega) (by omega) (by omega)

end QiushiMatmul
