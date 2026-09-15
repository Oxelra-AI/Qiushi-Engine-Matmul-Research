import QiushiFrozenRank365Checks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane365RankCoverGenBool : PlaneExtBool plane365RankCoverGenConfig where
  hSectionCoset := plane365RankCoverGenSectionAll
  hDeadCover := plane365RankCoverGenDeadAll
  hPlaneLeSource := plane365RankCoverGenSourceAll
  hPlaneLeDead := plane365RankCoverGenDeadSourceAll
  hIndicator := plane365RankCoverGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
