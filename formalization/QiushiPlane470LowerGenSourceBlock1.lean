import QiushiPlane470LowerGenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane470LowerGenSourceBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 52,
    plane470LowerGenSourceProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane470LowerGenSourceProperty, plane470LowerGenConfig, plane470LowerGenOccSys]
  decide +kernel
end QiushiMatmul
