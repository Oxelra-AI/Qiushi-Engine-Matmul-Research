import QiushiPlane338GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane338GenSectionBlock13 : forall offset : Fin 32,
    forall hlt : 13 * 32 + offset.val < 512,
    plane338GenSectionProperty (Fin.mk (13 * 32 + offset.val) hlt) := by
  simp only [plane338GenSectionProperty, plane338GenConfig, plane338GenOccSys]
  decide +kernel
end QiushiMatmul
