import QiushiPlane487GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane487GenSectionBlock4 : forall offset : Fin 32,
    forall hlt : 4 * 32 + offset.val < 512,
    plane487GenSectionProperty (Fin.mk (4 * 32 + offset.val) hlt) := by
  simp only [plane487GenSectionProperty, plane487GenConfig, plane487GenOccSys]
  decide +kernel
end QiushiMatmul
