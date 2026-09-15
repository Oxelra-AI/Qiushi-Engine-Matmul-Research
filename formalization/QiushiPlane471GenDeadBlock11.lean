import QiushiPlane471GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane471GenDeadBlock11 : forall offset : Fin 32,
    forall hlt : 11 * 32 + offset.val < 512,
    plane471GenDeadProperty (Fin.mk (11 * 32 + offset.val) hlt) := by
  simp only [plane471GenDeadProperty, plane471GenConfig, plane471GenOccSys]
  decide +kernel
end QiushiMatmul
