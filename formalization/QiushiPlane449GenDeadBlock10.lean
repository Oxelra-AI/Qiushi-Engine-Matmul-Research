import QiushiPlane449GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane449GenDeadBlock10 : forall offset : Fin 32,
    forall hlt : 10 * 32 + offset.val < 512,
    plane449GenDeadProperty (Fin.mk (10 * 32 + offset.val) hlt) := by
  simp only [plane449GenDeadProperty, plane449GenConfig, plane449GenOccSys]
  decide +kernel
end QiushiMatmul
