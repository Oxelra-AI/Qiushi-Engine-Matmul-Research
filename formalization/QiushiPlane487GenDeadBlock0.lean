import QiushiPlane487GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane487GenDeadBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 512,
    plane487GenDeadProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane487GenDeadProperty, plane487GenConfig, plane487GenOccSys]
  decide +kernel
end QiushiMatmul
