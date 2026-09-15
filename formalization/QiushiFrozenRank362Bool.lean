import QiushiFrozenRank362Checks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane362RankCoverGenBool : PlaneExtBool plane362RankCoverGenConfig where
  hSectionCoset := plane362RankCoverGenSectionAll
  hDeadCover := plane362RankCoverGenDeadAll
  hPlaneLeSource := plane362RankCoverGenSourceAll
  hPlaneLeDead := plane362RankCoverGenDeadSourceAll
  hIndicator := plane362RankCoverGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
