import QiushiPlane470LowerGenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane470LowerGenDeadBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 512,
    plane470LowerGenDeadProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane470LowerGenDeadProperty, plane470LowerGenConfig, plane470LowerGenOccSys]
  decide +kernel
end QiushiMatmul
