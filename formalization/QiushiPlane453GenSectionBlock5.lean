import QiushiPlane453GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane453GenSectionBlock5 : forall offset : Fin 32,
    forall hlt : 5 * 32 + offset.val < 512,
    plane453GenSectionProperty (Fin.mk (5 * 32 + offset.val) hlt) := by
  simp only [plane453GenSectionProperty, plane453GenConfig, plane453GenOccSys]
  decide +kernel
end QiushiMatmul
