import QiushiFrozenRank369Checks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane369RankCoverGenBool : PlaneExtBool plane369RankCoverGenConfig where
  hSectionCoset := plane369RankCoverGenSectionAll
  hDeadCover := plane369RankCoverGenDeadAll
  hPlaneLeSource := plane369RankCoverGenSourceAll
  hPlaneLeDead := plane369RankCoverGenDeadSourceAll
  hIndicator := plane369RankCoverGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
