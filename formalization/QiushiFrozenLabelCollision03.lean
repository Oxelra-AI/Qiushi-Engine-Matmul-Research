import QiushiFrozenLabelIncidence

namespace QiushiMatmul.FrozenLabel
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

theorem collision_pair_12 :
    planeIncidence 6 (frozenWangBasis 352) ≠
      planeIncidence 6 (frozenWangBasis 355) := by decide +kernel

theorem collision_pair_13 :
    planeIncidence 6 (frozenWangBasis 352) ≠
      planeIncidence 6 (frozenWangBasis 356) := by decide +kernel

theorem collision_pair_14 :
    planeIncidence 6 (frozenWangBasis 353) ≠
      planeIncidence 6 (frozenWangBasis 360) := by decide +kernel

theorem collision_pair_15 :
    planeIncidence 9 (frozenWangBasis 364) ≠
      planeIncidence 9 (frozenWangBasis 365) := by decide +kernel

end QiushiMatmul.FrozenLabel
