import QiushiFrozenLabelIncidence

namespace QiushiMatmul.FrozenLabel
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

theorem collision_pair_20 :
    planeIncidence 6 (frozenWangBasis 381) ≠
      planeIncidence 6 (frozenWangBasis 382) := by decide +kernel

theorem collision_pair_21 :
    planeIncidence 6 (frozenWangBasis 381) ≠
      planeIncidence 6 (frozenWangBasis 387) := by decide +kernel

theorem collision_pair_22 :
    planeIncidence 6 (frozenWangBasis 381) ≠
      planeIncidence 6 (frozenWangBasis 388) := by decide +kernel

theorem collision_pair_23 :
    planeIncidence 6 (frozenWangBasis 381) ≠
      planeIncidence 6 (frozenWangBasis 394) := by decide +kernel

end QiushiMatmul.FrozenLabel
