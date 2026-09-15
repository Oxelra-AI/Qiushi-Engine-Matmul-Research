import QiushiPlane267GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane267GenSectionBlock7 : forall offset : Fin 32,
    forall hlt : 7 * 32 + offset.val < 512,
    plane267GenSectionProperty (Fin.mk (7 * 32 + offset.val) hlt) := by
  simp only [plane267GenSectionProperty, plane267GenConfig, plane267GenOccSys]
  decide +kernel
end QiushiMatmul
