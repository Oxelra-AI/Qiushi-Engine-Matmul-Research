import QiushiFrozenRank368Checks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane368RankCoverGenBool : PlaneExtBool plane368RankCoverGenConfig where
  hSectionCoset := plane368RankCoverGenSectionAll
  hDeadCover := plane368RankCoverGenDeadAll
  hPlaneLeSource := plane368RankCoverGenSourceAll
  hPlaneLeDead := plane368RankCoverGenDeadSourceAll
  hIndicator := plane368RankCoverGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
