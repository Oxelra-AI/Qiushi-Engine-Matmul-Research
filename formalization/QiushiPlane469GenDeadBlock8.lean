import QiushiPlane469GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane469GenDeadBlock8 : forall offset : Fin 32,
    forall hlt : 8 * 32 + offset.val < 512,
    plane469GenDeadProperty (Fin.mk (8 * 32 + offset.val) hlt) := by
  simp only [plane469GenDeadProperty, plane469GenConfig, plane469GenOccSys]
  decide +kernel
end QiushiMatmul
