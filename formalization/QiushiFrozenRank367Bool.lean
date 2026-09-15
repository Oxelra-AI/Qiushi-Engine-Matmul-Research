import QiushiFrozenRank367Checks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane367RankCoverGenBool : PlaneExtBool plane367RankCoverGenConfig where
  hSectionCoset := plane367RankCoverGenSectionAll
  hDeadCover := plane367RankCoverGenDeadAll
  hPlaneLeSource := plane367RankCoverGenSourceAll
  hPlaneLeDead := plane367RankCoverGenDeadSourceAll
  hIndicator := plane367RankCoverGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
