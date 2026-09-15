import QiushiFrozenRank363Checks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane363RankCoverGenBool : PlaneExtBool plane363RankCoverGenConfig where
  hSectionCoset := plane363RankCoverGenSectionAll
  hDeadCover := plane363RankCoverGenDeadAll
  hPlaneLeSource := plane363RankCoverGenSourceAll
  hPlaneLeDead := plane363RankCoverGenDeadSourceAll
  hIndicator := plane363RankCoverGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
