import QiushiPlane278GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane278GenSectionBlock2 : forall offset : Fin 128,
    forall hlt : 2 * 128 + offset.val < 512,
    plane278GenSectionProperty (Fin.mk (2 * 128 + offset.val) hlt) := by
  simp only [plane278GenSectionProperty, plane278GenConfig, plane278GenOccSys]
  decide +kernel
end QiushiMatmul
