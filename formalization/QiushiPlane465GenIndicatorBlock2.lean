import QiushiPlane465GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane465GenIndicatorBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 88,
    plane465GenIndicatorProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane465GenIndicatorProperty, plane465GenConfig, plane465GenOccSys]
  decide +kernel
end QiushiMatmul
