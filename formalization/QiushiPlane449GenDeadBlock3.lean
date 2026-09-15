import QiushiPlane449GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane449GenDeadBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 512,
    plane449GenDeadProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane449GenDeadProperty, plane449GenConfig, plane449GenOccSys]
  decide +kernel
end QiushiMatmul
