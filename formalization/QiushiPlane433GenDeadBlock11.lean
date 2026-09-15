import QiushiPlane433GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane433GenDeadBlock11 : forall offset : Fin 32,
    forall hlt : 11 * 32 + offset.val < 512,
    plane433GenDeadProperty (Fin.mk (11 * 32 + offset.val) hlt) := by
  simp only [plane433GenDeadProperty, plane433GenConfig, plane433GenOccSys]
  decide +kernel
end QiushiMatmul
