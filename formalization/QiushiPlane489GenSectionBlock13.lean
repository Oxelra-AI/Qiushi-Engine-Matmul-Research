import QiushiPlane489GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane489GenSectionBlock13 : forall offset : Fin 32,
    forall hlt : 13 * 32 + offset.val < 512,
    plane489GenSectionProperty (Fin.mk (13 * 32 + offset.val) hlt) := by
  simp only [plane489GenSectionProperty, plane489GenConfig, plane489GenOccSys]
  decide +kernel
end QiushiMatmul
