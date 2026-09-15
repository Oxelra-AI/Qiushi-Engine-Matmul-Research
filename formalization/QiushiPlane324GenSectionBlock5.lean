import QiushiPlane324GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane324GenSectionBlock5 : forall offset : Fin 32,
    forall hlt : 5 * 32 + offset.val < 512,
    plane324GenSectionProperty (Fin.mk (5 * 32 + offset.val) hlt) := by
  simp only [plane324GenSectionProperty, plane324GenConfig, plane324GenOccSys]
  decide +kernel
end QiushiMatmul
