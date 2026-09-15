import QiushiPlane481GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane481GenSectionBlock11 : forall offset : Fin 32,
    forall hlt : 11 * 32 + offset.val < 512,
    plane481GenSectionProperty (Fin.mk (11 * 32 + offset.val) hlt) := by
  simp only [plane481GenSectionProperty, plane481GenConfig, plane481GenOccSys]
  decide +kernel
end QiushiMatmul
