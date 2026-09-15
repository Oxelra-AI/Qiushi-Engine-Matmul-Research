import QiushiPlane459GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane459GenSectionBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 512,
    plane459GenSectionProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane459GenSectionProperty, plane459GenConfig, plane459GenOccSys]
  decide +kernel
end QiushiMatmul
