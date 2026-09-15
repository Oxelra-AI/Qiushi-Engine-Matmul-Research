import QiushiPlane469GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane469GenDeadSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 3,
    plane469GenDeadSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane469GenDeadSourceProperty, plane469GenConfig, plane469GenOccSys]
  decide +kernel
end QiushiMatmul
