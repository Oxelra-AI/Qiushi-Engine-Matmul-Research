import QiushiPlane429GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane429GenIndicatorBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 55,
    plane429GenIndicatorProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane429GenIndicatorProperty, plane429GenConfig, plane429GenOccSys]
  decide +kernel
end QiushiMatmul
