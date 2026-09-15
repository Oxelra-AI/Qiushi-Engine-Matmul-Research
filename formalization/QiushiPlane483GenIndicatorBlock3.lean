import QiushiPlane483GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane483GenIndicatorBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 112,
    plane483GenIndicatorProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane483GenIndicatorProperty, plane483GenConfig, plane483GenOccSys]
  decide +kernel
end QiushiMatmul
