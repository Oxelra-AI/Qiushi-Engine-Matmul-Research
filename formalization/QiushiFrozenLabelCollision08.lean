import QiushiFrozenLabelIncidence

namespace QiushiMatmul.FrozenLabel
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

theorem collision_pair_32 :
    planeIncidence 1 (frozenWangBasis 426) ≠
      planeIncidence 1 (frozenWangBasis 439) := by decide +kernel

theorem collision_pair_33 :
    planeIncidence 1 (frozenWangBasis 426) ≠
      planeIncidence 1 (frozenWangBasis 440) := by decide +kernel

theorem collision_pair_34 :
    planeIncidence 9 (frozenWangBasis 460) ≠
      planeIncidence 9 (frozenWangBasis 463) := by decide +kernel

theorem collision_pair_35 :
    planeIncidence 8 (frozenWangBasis 460) ≠
      planeIncidence 8 (frozenWangBasis 469) := by decide +kernel

end QiushiMatmul.FrozenLabel
