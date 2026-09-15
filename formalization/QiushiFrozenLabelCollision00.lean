import QiushiFrozenLabelIncidence

namespace QiushiMatmul.FrozenLabel
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

theorem collision_pair_00 :
    planeIncidence 6 (frozenWangBasis 129) ≠
      planeIncidence 6 (frozenWangBasis 133) := by decide +kernel

theorem collision_pair_01 :
    planeIncidence 6 (frozenWangBasis 262) ≠
      planeIncidence 6 (frozenWangBasis 272) := by decide +kernel

theorem collision_pair_02 :
    planeIncidence 1 (frozenWangBasis 264) ≠
      planeIncidence 1 (frozenWangBasis 266) := by decide +kernel

theorem collision_pair_03 :
    planeIncidence 6 (frozenWangBasis 281) ≠
      planeIncidence 6 (frozenWangBasis 325) := by decide +kernel

end QiushiMatmul.FrozenLabel
