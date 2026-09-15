import QiushiPlane276GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane276GenSectionBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 512,
    plane276GenSectionProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane276GenSectionProperty, plane276GenConfig, plane276GenOccSys]
  decide +kernel
end QiushiMatmul
