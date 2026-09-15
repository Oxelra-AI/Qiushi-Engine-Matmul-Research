import QiushiFrozenLabelIncidence

namespace QiushiMatmul.FrozenLabel
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

theorem collision_pair_08 :
    planeIncidence 6 (frozenWangBasis 312) ≠
      planeIncidence 6 (frozenWangBasis 352) := by decide +kernel

theorem collision_pair_09 :
    planeIncidence 1 (frozenWangBasis 318) ≠
      planeIncidence 1 (frozenWangBasis 360) := by decide +kernel

theorem collision_pair_10 :
    planeIncidence 6 (frozenWangBasis 320) ≠
      planeIncidence 6 (frozenWangBasis 322) := by decide +kernel

theorem collision_pair_11 :
    planeIncidence 6 (frozenWangBasis 331) ≠
      planeIncidence 6 (frozenWangBasis 332) := by decide +kernel

end QiushiMatmul.FrozenLabel
