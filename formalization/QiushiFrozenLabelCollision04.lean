import QiushiFrozenLabelIncidence

namespace QiushiMatmul.FrozenLabel
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

theorem collision_pair_16 :
    planeIncidence 6 (frozenWangBasis 364) ≠
      planeIncidence 6 (frozenWangBasis 373) := by decide +kernel

theorem collision_pair_17 :
    planeIncidence 8 (frozenWangBasis 365) ≠
      planeIncidence 8 (frozenWangBasis 370) := by decide +kernel

theorem collision_pair_18 :
    planeIncidence 6 (frozenWangBasis 370) ≠
      planeIncidence 6 (frozenWangBasis 373) := by decide +kernel

theorem collision_pair_19 :
    planeIncidence 6 (frozenWangBasis 380) ≠
      planeIncidence 6 (frozenWangBasis 381) := by decide +kernel

end QiushiMatmul.FrozenLabel
