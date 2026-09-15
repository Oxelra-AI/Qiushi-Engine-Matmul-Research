import QiushiPlane461GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane461GenSectionBlock15 : forall offset : Fin 32,
    forall hlt : 15 * 32 + offset.val < 512,
    plane461GenSectionProperty (Fin.mk (15 * 32 + offset.val) hlt) := by
  simp only [plane461GenSectionProperty, plane461GenConfig, plane461GenOccSys]
  decide +kernel
end QiushiMatmul
