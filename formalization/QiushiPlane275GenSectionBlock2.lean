import QiushiPlane275GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane275GenSectionBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 512,
    plane275GenSectionProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane275GenSectionProperty, plane275GenConfig, plane275GenOccSys]
  decide +kernel
end QiushiMatmul
