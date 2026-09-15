import QiushiPlane476GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane476GenSectionBlock8 : forall offset : Fin 32,
    forall hlt : 8 * 32 + offset.val < 512,
    plane476GenSectionProperty (Fin.mk (8 * 32 + offset.val) hlt) := by
  simp only [plane476GenSectionProperty, plane476GenConfig, plane476GenOccSys]
  decide +kernel
end QiushiMatmul
