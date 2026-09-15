import QiushiPlane489GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane489GenDeadBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 512,
    plane489GenDeadProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane489GenDeadProperty, plane489GenConfig, plane489GenOccSys]
  decide +kernel
end QiushiMatmul
