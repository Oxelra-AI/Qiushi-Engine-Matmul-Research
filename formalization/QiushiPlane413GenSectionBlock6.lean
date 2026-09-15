import QiushiPlane413GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane413GenSectionBlock6 : forall offset : Fin 32,
    forall hlt : 6 * 32 + offset.val < 512,
    plane413GenSectionProperty (Fin.mk (6 * 32 + offset.val) hlt) := by
  simp only [plane413GenSectionProperty, plane413GenConfig, plane413GenOccSys]
  decide +kernel
end QiushiMatmul
