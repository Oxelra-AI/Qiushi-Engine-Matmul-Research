import QiushiPlane454GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane454GenSectionBlock6 : forall offset : Fin 32,
    forall hlt : 6 * 32 + offset.val < 512,
    plane454GenSectionProperty (Fin.mk (6 * 32 + offset.val) hlt) := by
  simp only [plane454GenSectionProperty, plane454GenConfig, plane454GenOccSys]
  decide +kernel
end QiushiMatmul
