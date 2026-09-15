import QiushiPlane419GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane419GenSectionBlock9 : forall offset : Fin 32,
    forall hlt : 9 * 32 + offset.val < 512,
    plane419GenSectionProperty (Fin.mk (9 * 32 + offset.val) hlt) := by
  simp only [plane419GenSectionProperty, plane419GenConfig, plane419GenOccSys]
  decide +kernel
end QiushiMatmul
