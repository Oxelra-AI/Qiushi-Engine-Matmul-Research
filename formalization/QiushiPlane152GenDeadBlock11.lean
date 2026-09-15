import QiushiPlane152GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane152GenDeadBlock11 : forall offset : Fin 32,
    forall hlt : 11 * 32 + offset.val < 512,
    plane152GenDeadProperty (Fin.mk (11 * 32 + offset.val) hlt) := by
  simp only [plane152GenDeadProperty, plane152GenConfig, plane152GenOccSys]
  decide +kernel
end QiushiMatmul
