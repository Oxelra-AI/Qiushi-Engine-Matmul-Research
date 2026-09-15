import QiushiPlane270GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane270GenSectionBlock4 : forall offset : Fin 32,
    forall hlt : 4 * 32 + offset.val < 512,
    plane270GenSectionProperty (Fin.mk (4 * 32 + offset.val) hlt) := by
  simp only [plane270GenSectionProperty, plane270GenConfig, plane270GenOccSys]
  decide +kernel
end QiushiMatmul
