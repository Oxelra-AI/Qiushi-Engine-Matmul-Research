import QiushiPlane278GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane278GenDeadBlock1 : forall offset : Fin 128,
    forall hlt : 1 * 128 + offset.val < 512,
    plane278GenDeadProperty (Fin.mk (1 * 128 + offset.val) hlt) := by
  simp only [plane278GenDeadProperty, plane278GenConfig, plane278GenOccSys]
  decide +kernel
end QiushiMatmul
