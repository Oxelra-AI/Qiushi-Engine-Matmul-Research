import QiushiFrozenRank361Checks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane361RankCoverGenBool : PlaneExtBool plane361RankCoverGenConfig where
  hSectionCoset := plane361RankCoverGenSectionAll
  hDeadCover := plane361RankCoverGenDeadAll
  hPlaneLeSource := plane361RankCoverGenSourceAll
  hPlaneLeDead := plane361RankCoverGenDeadSourceAll
  hIndicator := plane361RankCoverGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
