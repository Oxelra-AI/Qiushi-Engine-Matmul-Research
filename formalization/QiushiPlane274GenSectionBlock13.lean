import QiushiPlane274GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane274GenSectionBlock13 : forall offset : Fin 32,
    forall hlt : 13 * 32 + offset.val < 512,
    plane274GenSectionProperty (Fin.mk (13 * 32 + offset.val) hlt) := by
  simp only [plane274GenSectionProperty, plane274GenConfig, plane274GenOccSys]
  decide +kernel
end QiushiMatmul
