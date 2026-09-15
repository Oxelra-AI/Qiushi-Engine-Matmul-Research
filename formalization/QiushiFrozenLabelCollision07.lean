import QiushiFrozenLabelIncidence

namespace QiushiMatmul.FrozenLabel
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

theorem collision_pair_28 :
    planeIncidence 1 (frozenWangBasis 420) ≠
      planeIncidence 1 (frozenWangBasis 437) := by decide +kernel

theorem collision_pair_29 :
    planeIncidence 8 (frozenWangBasis 423) ≠
      planeIncidence 8 (frozenWangBasis 426) := by decide +kernel

theorem collision_pair_30 :
    planeIncidence 6 (frozenWangBasis 425) ≠
      planeIncidence 6 (frozenWangBasis 435) := by decide +kernel

theorem collision_pair_31 :
    planeIncidence 1 (frozenWangBasis 425) ≠
      planeIncidence 1 (frozenWangBasis 437) := by decide +kernel

end QiushiMatmul.FrozenLabel
