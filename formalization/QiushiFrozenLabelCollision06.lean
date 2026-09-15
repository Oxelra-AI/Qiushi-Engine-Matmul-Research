import QiushiFrozenLabelIncidence

namespace QiushiMatmul.FrozenLabel
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

theorem collision_pair_24 :
    planeIncidence 6 (frozenWangBasis 381) ≠
      planeIncidence 6 (frozenWangBasis 399) := by decide +kernel

theorem collision_pair_25 :
    planeIncidence 1 (frozenWangBasis 418) ≠
      planeIncidence 1 (frozenWangBasis 420) := by decide +kernel

theorem collision_pair_26 :
    planeIncidence 7 (frozenWangBasis 418) ≠
      planeIncidence 7 (frozenWangBasis 425) := by decide +kernel

theorem collision_pair_27 :
    planeIncidence 6 (frozenWangBasis 420) ≠
      planeIncidence 6 (frozenWangBasis 435) := by decide +kernel

end QiushiMatmul.FrozenLabel
