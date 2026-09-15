import QiushiPlane459GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane459GenDeadBlock4 : forall offset : Fin 32,
    forall hlt : 4 * 32 + offset.val < 512,
    plane459GenDeadProperty (Fin.mk (4 * 32 + offset.val) hlt) := by
  simp only [plane459GenDeadProperty, plane459GenConfig, plane459GenOccSys]
  decide +kernel
end QiushiMatmul
