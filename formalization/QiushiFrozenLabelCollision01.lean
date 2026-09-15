import QiushiFrozenLabelIncidence

namespace QiushiMatmul.FrozenLabel
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

theorem collision_pair_04 :
    planeIncidence 6 (frozenWangBasis 282) ≠
      planeIncidence 6 (frozenWangBasis 326) := by decide +kernel

theorem collision_pair_05 :
    planeIncidence 1 (frozenWangBasis 286) ≠
      planeIncidence 1 (frozenWangBasis 290) := by decide +kernel

theorem collision_pair_06 :
    planeIncidence 1 (frozenWangBasis 289) ≠
      planeIncidence 1 (frozenWangBasis 360) := by decide +kernel

theorem collision_pair_07 :
    planeIncidence 1 (frozenWangBasis 299) ≠
      planeIncidence 1 (frozenWangBasis 331) := by decide +kernel

end QiushiMatmul.FrozenLabel
