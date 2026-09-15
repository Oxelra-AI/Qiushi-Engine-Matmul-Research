import QiushiPlane298GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane298GenSectionBlock9 : forall offset : Fin 32,
    forall hlt : 9 * 32 + offset.val < 512,
    plane298GenSectionProperty (Fin.mk (9 * 32 + offset.val) hlt) := by
  simp only [plane298GenSectionProperty, plane298GenConfig, plane298GenOccSys]
  decide +kernel
end QiushiMatmul
