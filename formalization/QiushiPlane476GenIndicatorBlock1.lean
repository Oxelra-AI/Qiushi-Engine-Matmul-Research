import QiushiPlane476GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane476GenIndicatorBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 113,
    plane476GenIndicatorProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane476GenIndicatorProperty, plane476GenConfig, plane476GenOccSys]
  decide +kernel
end QiushiMatmul
